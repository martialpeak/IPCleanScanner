# -*- coding: utf-8 -*-
from __future__ import annotations
import sys
import os
import json
import traceback
import threading
import time
import socket
import subprocess
import tempfile
import math
import statistics
import io
from dataclasses import dataclass
from collections import deque

from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
import ipaddress
from pathlib import Path
from typing import Dict, Tuple, Any, List, Optional

from PyQt6.QtCore import Qt, QThread, QObject, QTimer, pyqtSignal, QPoint, QAbstractTableModel, QModelIndex, QSortFilterProxyModel
from PyQt6.QtGui import QFont, QGuiApplication, QAction, QIcon
from PyQt6.QtWidgets import (
    QApplication,
    QMainWindow,
    QWidget,
    QVBoxLayout,
    QLabel,
    QPushButton,
    QHBoxLayout,
    QProgressBar,
    QMessageBox,
    QGroupBox,
    QFileDialog,
    QSpinBox,
    QComboBox,
    QDialog,
    QLineEdit,
    QCheckBox,
    QPlainTextEdit,
    QTableView,
    QAbstractItemView,
    QHeaderView,
    QMenu,
    QProgressDialog,
    QRadioButton,
    QButtonGroup,
)

# Optional: raise Xray process priority on Windows to improve throughput.
try:
    import psutil  # type: ignore
except Exception:
    psutil = None

def _raise_process_priority(pid: int) -> None:
    try:
        if psutil is None:
            return
        p = psutil.Process(pid)
        if sys.platform.startswith("win"):
            p.nice(psutil.HIGH_PRIORITY_CLASS)
        else:
            try:
                p.nice(-5)
            except Exception:
                pass
    except Exception:
        pass


# ---------------------- Qt Models (virtualized tables for large data) ----------------------
class ToolsIPModel(QAbstractTableModel):
    HEADERS = ["IPv4 (click to copy)"]

    def __init__(self, ips: Optional[List[str]] = None, parent: QObject | None = None):
        super().__init__(parent)
        self._ips: List[str] = list(ips or [])

    def set_ips(self, ips: List[str]) -> None:
        self.beginResetModel()
        self._ips = list(ips or [])
        self.endResetModel()

    def rowCount(self, parent: QModelIndex = QModelIndex()) -> int:
        return 0 if parent.isValid() else len(self._ips)

    def columnCount(self, parent: QModelIndex = QModelIndex()) -> int:
        return 0 if parent.isValid() else 1

    def headerData(self, section: int, orientation: Qt.Orientation, role: int = Qt.ItemDataRole.DisplayRole):
        if role == Qt.ItemDataRole.DisplayRole and orientation == Qt.Orientation.Horizontal:
            return self.HEADERS[section]
        return None

    def data(self, index: QModelIndex, role: int = Qt.ItemDataRole.DisplayRole):
        if not index.isValid():
            return None
        r = index.row()
        if r < 0 or r >= len(self._ips):
            return None
        ip = self._ips[r]
        if role == Qt.ItemDataRole.DisplayRole:
            return ip
        if role == Qt.ItemDataRole.TextAlignmentRole:
            return int(Qt.AlignmentFlag.AlignCenter)
        return None

    def flags(self, index: QModelIndex):
        if not index.isValid():
            return Qt.ItemFlag.NoItemFlags
        return Qt.ItemFlag.ItemIsEnabled | Qt.ItemFlag.ItemIsSelectable


class RangesTableModel(QAbstractTableModel):
    HEADERS = ["Use", "Provider", "IPv4 CIDR", "Total IPs in range"]

    def __init__(self, providers: Dict[str, Any], rows: Optional[List[Tuple[str, str, int, bool]]] = None, parent: QObject | None = None):
        super().__init__(parent)
        self._providers = providers or {}
        # rows: (provider, cidr, total_ips, checked)
        self._rows: List[Tuple[str, str, int, bool]] = list(rows or [])

    def set_providers(self, providers: Dict[str, Any]) -> None:
        self._providers = providers or {}
        self.layoutChanged.emit()

    def set_provider_icons(self, icons: Dict[str, QIcon]) -> None:
        self._provider_icons = dict(icons or {})
        self.layoutChanged.emit()

    def set_rows(self, rows: List[Tuple[str, str, int, bool]]) -> None:
        self.beginResetModel()
        self._rows = list(rows or [])
        self.endResetModel()

    def rowCount(self, parent: QModelIndex = QModelIndex()) -> int:
        return 0 if parent.isValid() else len(self._rows)

    def columnCount(self, parent: QModelIndex = QModelIndex()) -> int:
        return 0 if parent.isValid() else 4

    def headerData(self, section: int, orientation: Qt.Orientation, role: int = Qt.ItemDataRole.DisplayRole):
        if role == Qt.ItemDataRole.DisplayRole and orientation == Qt.Orientation.Horizontal:
            return self.HEADERS[section]
        return None

    def data(self, index: QModelIndex, role: int = Qt.ItemDataRole.DisplayRole):
        if not index.isValid():
            return None
        r, c = index.row(), index.column()
        if r < 0 or r >= len(self._rows):
            return None
        prov, cidr, total, checked = self._rows[r]

        if c == 0:
            if role == Qt.ItemDataRole.CheckStateRole:
                return Qt.CheckState.Checked if checked else Qt.CheckState.Unchecked
            if role == Qt.ItemDataRole.DisplayRole:
                return ""
            if role == Qt.ItemDataRole.TextAlignmentRole:
                return int(Qt.AlignmentFlag.AlignCenter)
            return None

        if c == 1:
            if role == Qt.ItemDataRole.DisplayRole:
                return prov
            if role == Qt.ItemDataRole.DecorationRole:
                ic = icon_for_provider(self._providers, prov)
                return ic if (ic is not None and not ic.isNull()) else None

        if c == 2 and role == Qt.ItemDataRole.DisplayRole:
            return cidr
        if c == 3 and role == Qt.ItemDataRole.DisplayRole:
            return f"{total} IP addresses"

        if role == Qt.ItemDataRole.TextAlignmentRole:
            return int(Qt.AlignmentFlag.AlignCenter)

        return None

    def setData(self, index: QModelIndex, value, role: int = Qt.ItemDataRole.EditRole) -> bool:
        if not index.isValid():
            return False
        r, c = index.row(), index.column()
        if c != 0 or role != Qt.ItemDataRole.CheckStateRole:
            return False
        prov, cidr, total, _checked = self._rows[r]
        new_checked = (value == Qt.CheckState.Checked)
        if new_checked == _checked:
            return True
        self._rows[r] = (prov, cidr, total, new_checked)
        self.dataChanged.emit(index, index, [Qt.ItemDataRole.CheckStateRole])
        return True

    def flags(self, index: QModelIndex):
        if not index.isValid():
            return Qt.ItemFlag.NoItemFlags
        if index.column() == 0:
            return (
                Qt.ItemFlag.ItemIsEnabled
                | Qt.ItemFlag.ItemIsSelectable
                | Qt.ItemFlag.ItemIsUserCheckable
            )
        return Qt.ItemFlag.ItemIsEnabled | Qt.ItemFlag.ItemIsSelectable

    def checked_ranges(self) -> List[Tuple[str, str]]:
        out: List[Tuple[str, str]] = []
        seen = set()
        for prov, cidr, _total, checked in self._rows:
            if checked and (prov, cidr) not in seen:
                seen.add((prov, cidr))
                out.append((prov, cidr))
        return out

    def rows_state(self) -> List[Tuple[str, str, bool]]:
        """Return (provider, cidr, checked) for all rows."""
        out: List[Tuple[str, str, bool]] = []
        for prov, cidr, _total, checked in self._rows:
            out.append((prov, cidr, checked))
        return out



class ValidIPResultsModel(QAbstractTableModel):
    HEADERS = ["Provider", "IP (click to copy)", "Latency"]

    def __init__(self, providers: Dict[str, Any], rows: Optional[List[Any]] = None, max_latency: int = 1000, parent: QObject | None = None):
        super().__init__(parent)
        self._providers = providers or {}
        self._rows: List[Any] = list(rows or [])
        self._max_latency = int(max_latency or 1000)

    def set_providers(self, providers: Dict[str, Any]) -> None:
        self._providers = providers or {}
        self.layoutChanged.emit()

    def set_provider_icons(self, icons: Dict[str, QIcon]) -> None:
        self._provider_icons = dict(icons or {})
        self.layoutChanged.emit()

    def set_max_latency(self, v: int) -> None:
        v = int(v or 1000)
        if v == self._max_latency:
            return
        self._max_latency = v
        self.dataChanged.emit(self.index(0, 0), self.index(max(0, len(self._rows)-1), 2), [])

    def set_rows(self, rows: List[Any]) -> None:
        self.beginResetModel()
        self._rows = list(rows or [])
        self.endResetModel()

    def rowCount(self, parent: QModelIndex = QModelIndex()) -> int:
        return 0 if parent.isValid() else len(self._rows)

    def columnCount(self, parent: QModelIndex = QModelIndex()) -> int:
        return 0 if parent.isValid() else 3

    def headerData(self, section: int, orientation: Qt.Orientation, role: int = Qt.ItemDataRole.DisplayRole):
        if role == Qt.ItemDataRole.DisplayRole and orientation == Qt.Orientation.Horizontal:
            return self.HEADERS[section]
        return None

    def data(self, index: QModelIndex, role: int = Qt.ItemDataRole.DisplayRole):
        if not index.isValid():
            return None
        r, c = index.row(), index.column()
        if r < 0 or r >= len(self._rows):
            return None
        item = self._rows[r]  # ValidIP(latency, ip, provider)
        prov, ip, lat = item.provider, item.ip, int(item.latency)

        if c == 0:
            if role == Qt.ItemDataRole.DisplayRole:
                return prov
            if role == Qt.ItemDataRole.DecorationRole:
                ic = icon_for_provider(self._providers, prov)
                return ic if (ic is not None and not ic.isNull()) else None

        if c == 1 and role == Qt.ItemDataRole.DisplayRole:
            return ip

        if c == 2:
            if role == Qt.ItemDataRole.DisplayRole:
                return f"{lat} ms"
            if role == Qt.ItemDataRole.ForegroundRole:
                return latency_color(lat, self._max_latency)

        if role == Qt.ItemDataRole.TextAlignmentRole:
            return int(Qt.AlignmentFlag.AlignCenter)

        return None

    def flags(self, index: QModelIndex):
        if not index.isValid():
            return Qt.ItemFlag.NoItemFlags
        return Qt.ItemFlag.ItemIsEnabled | Qt.ItemFlag.ItemIsSelectable



class SpeedTestBatchModel(QAbstractTableModel):
    HEADERS = ["Provider", "Address", "Status", "Ping (ms)", "Server IP", "Country", "Download (MB/s)", "Upload (MB/s)"]

    def __init__(self, providers: Dict[str, Any], rows: Optional[List[Dict[str, Any]]] = None, parent: QObject | None = None):
        super().__init__(parent)
        self._providers = providers or {}
        self._provider_icons: Dict[str, QIcon] = {}
        # each row: dict keys provider,address,status,ping,server_ip,country,download,upload
        self._rows: List[Dict[str, Any]] = list(rows or [])

    def set_providers(self, providers: Dict[str, Any]) -> None:
        self._providers = providers or {}
        self.layoutChanged.emit()

    def set_provider_icons(self, icons: Dict[str, QIcon]) -> None:
        self._provider_icons = dict(icons or {})
        self.layoutChanged.emit()

    def set_items(self, items: List[Tuple[str, str]]) -> None:
        self.beginResetModel()
        self._rows = []
        for prov, addr in (items or []):
            self._rows.append({
                "provider": prov or "",
                "address": addr or "",
                "status": "Pending",
                "ping": "---",
                "server_ip": "---",
                "country": "---",
                "download": "---",
                "upload": "---",
            })
        self.endResetModel()
    def reset_for_batch(self) -> None:
        """Reset all rows to a clean 'Pending' state in one model reset.

        This avoids emitting dataChanged 150k times, which can freeze the UI.
        """
        self.beginResetModel()
        for row in self._rows:
            row["status"] = "Pending"
            row["ping"] = "---"
            row["server_ip"] = "---"
            row["country"] = "---"
            row["download"] = "---"
            row["upload"] = "---"
            row["status_detail"] = ""
        self.endResetModel()


    def rowCount(self, parent: QModelIndex = QModelIndex()) -> int:
        return 0 if parent.isValid() else len(self._rows)

    def columnCount(self, parent: QModelIndex = QModelIndex()) -> int:
        return 0 if parent.isValid() else 8

    def headerData(self, section: int, orientation: Qt.Orientation, role: int = Qt.ItemDataRole.DisplayRole):
        if role == Qt.ItemDataRole.DisplayRole and orientation == Qt.Orientation.Horizontal:
            return self.HEADERS[section]
        return None

    def data(self, index: QModelIndex, role: int = Qt.ItemDataRole.DisplayRole):
        if not index.isValid():
            return None
        r, c = index.row(), index.column()
        if r < 0 or r >= len(self._rows):
            return None
        row = self._rows[r]
        if role == Qt.ItemDataRole.DisplayRole:
            if c == 0: return row["provider"]
            if c == 1: return row["address"]
            if c == 2: return row["status"]
            if c == 3: return row["ping"]
            if c == 4: return row["server_ip"]
            if c == 5: return row["country"]
            if c == 6: return row["download"]
            if c == 7: return row["upload"]
        if role == Qt.ItemDataRole.UserRole:
            if c == 3:
                try:
                    val = str(row.get("ping", "")).strip()
                    if val in ("", "---", "-"):
                        return 10**12
                    if val == "-1":
                        return 10**12 - 1
                    return float(val)
                except Exception:
                    return 10**12
        if role == Qt.ItemDataRole.ToolTipRole and c == 2:
            det = str(row.get("status_detail","") or "")
            return det if det else None
        if role == Qt.ItemDataRole.ForegroundRole:
            if c == 2:
                status = str(row.get("status","")).strip().lower()
                if status == "success":
                    return QColor("#0a7d2c")
                if status == "fail":
                    return QColor("#b00020")
                if status.startswith("running"):
                    return QColor("#1f6feb")
                if status == "pending":
                    return QColor("#6b7280")
            if c == 3:
                val = str(row.get("ping","")).strip()
                if val == "-1":
                    return QColor("#b00020")
                if val not in ("", "---", "-"):
                    return QColor("#0a7d2c")
            if c in (6, 7):
                val = str(row.get("download" if c == 6 else "upload", "")).strip()
                if val == "0":
                    return QColor("#b00020")
        if c == 0 and role == Qt.ItemDataRole.DecorationRole:
            prov = str(row.get("provider",""))
            ic = self._provider_icons.get(prov)
            if ic is None or ic.isNull():
                ic = icon_for_provider(self._providers, prov)
            return ic if (ic is not None and not ic.isNull()) else None
        if role == Qt.ItemDataRole.TextAlignmentRole:
            return int(Qt.AlignmentFlag.AlignCenter)
        return None

    def flags(self, index: QModelIndex):
        if not index.isValid():
            return Qt.ItemFlag.NoItemFlags
        return Qt.ItemFlag.ItemIsEnabled | Qt.ItemFlag.ItemIsSelectable

    def get_item(self, row: int) -> Dict[str, Any]:
        return self._rows[row]

    def _set_row_value(self, row: int, key: str, value: Any, col: int):
        if row < 0 or row >= len(self._rows):
            return
        self._rows[row][key] = value
        idx = self.index(row, col)
        self.dataChanged.emit(idx, idx, [Qt.ItemDataRole.DisplayRole])

    def set_status(self, row: int, text: str) -> None:
        self._set_row_value(row, "status", text, 2)

    def set_status_detail(self, row: int, detail: str) -> None:
        # keep detail in the row; tooltip uses it
        if row < 0 or row >= len(self._rows):
            return
        self._rows[row]["status_detail"] = detail or ""
        idx = self.index(row, 2)
        self.dataChanged.emit(idx, idx, [Qt.ItemDataRole.ToolTipRole])

    def set_proxy_ip(self, row: int, proxy_ip: str) -> None:
        self._set_row_value(row, "server_ip", proxy_ip, 4)

    def set_country(self, row: int, country: str) -> None:
        self._set_row_value(row, "country", country, 5)

    def set_results(self, row: int, results: Dict[str, Any]) -> None:
        if row < 0 or row >= len(self._rows):
            return
        addr = str(results.get("target_address", self._rows[row].get("address","---")))
        self._rows[row]["address"] = addr
        proxy_ip = str(results.get("proxy_ip", "---"))
        self._rows[row]["server_ip"] = proxy_ip
        country_text = str(results.get("country", "---"))
        if (not country_text or country_text.strip() in ("---", "Unknown")) and proxy_ip not in ("---", "Unknown", ""):
            try:
                cname, flag = get_country_info(proxy_ip)
                if cname:
                    country_text = f"{flag} {cname}".strip()
            except Exception:
                pass
        self._rows[row]["country"] = country_text
        errors = results.get("errors") or {}
        skipped = results.get("skipped") or {}

        dl = results.get("download_MBps")
        if skipped.get("download"):
            self._rows[row]["download"] = "-"
        elif errors.get("download"):
            self._rows[row]["download"] = "0"
        else:
            self._rows[row]["download"] = (f"{dl:.2f}" if isinstance(dl, (int, float)) and dl > 0 else "---")

        ul = results.get("upload_MBps")
        if skipped.get("upload"):
            self._rows[row]["upload"] = "-"
        elif errors.get("upload"):
            self._rows[row]["upload"] = "0"
        else:
            self._rows[row]["upload"] = (f"{ul:.2f}" if isinstance(ul, (int, float)) and ul > 0 else "---")

        lat = results.get("ping_ms", results.get("latency_ms"))
        if errors.get("ping"):
            self._rows[row]["ping"] = "-1"
        else:
            self._rows[row]["ping"] = (_fmt_ping_ms(lat) if isinstance(lat, (int, float)) and lat > 0 else "---")
        if errors.get("ping") or not (isinstance(lat, (int, float)) and lat > 0):
            self._rows[row]["status"] = "Fail"
        else:
            self._rows[row]["status"] = "Success"
        self.dataChanged.emit(self.index(row, 0), self.index(row, 7), [Qt.ItemDataRole.DisplayRole, Qt.ItemDataRole.ForegroundRole, Qt.ItemDataRole.ToolTipRole])

class ScanIPTableModel(QAbstractTableModel):
    HEADERS = ["Provider", "IP (click to copy)", "Status", "Latency"]

    def __init__(self, providers: Dict[str, Any], rows: Optional[List[Any]] = None, ip_results: Optional[Dict[str, Tuple[Any, Any, Any]]] = None,
                 max_latency: int = 1000, parent: QObject | None = None):
        super().__init__(parent)
        self._providers = providers or {}
        self._rows: List[Any] = list(rows or [])  # IPRow(ip, provider)
        self._ip_results = ip_results if ip_results is not None else {}
        self._max_latency = int(max_latency or 1000)

    def set_providers(self, providers: Dict[str, Any]) -> None:
        self._providers = providers or {}
        self.layoutChanged.emit()

    def set_provider_icons(self, icons: Dict[str, QIcon]) -> None:
        self._provider_icons = dict(icons or {})
        self.layoutChanged.emit()

    def set_ip_results_ref(self, ip_results: Dict[str, Tuple[Any, Any, Any]]) -> None:
        self._ip_results = ip_results

    def set_max_latency(self, v: int) -> None:
        v = int(v or 1000)
        if v == self._max_latency:
            return
        self._max_latency = v
        if self._rows:
            self.dataChanged.emit(self.index(0, 0), self.index(len(self._rows)-1, 3), [])

    def set_rows(self, rows: List[Any]) -> None:
        self.beginResetModel()
        self._rows = list(rows or [])
        self.endResetModel()

    def rowCount(self, parent: QModelIndex = QModelIndex()) -> int:
        return 0 if parent.isValid() else len(self._rows)

    def columnCount(self, parent: QModelIndex = QModelIndex()) -> int:
        return 0 if parent.isValid() else 4

    def headerData(self, section: int, orientation: Qt.Orientation, role: int = Qt.ItemDataRole.DisplayRole):
        if role == Qt.ItemDataRole.DisplayRole and orientation == Qt.Orientation.Horizontal:
            return self.HEADERS[section]
        return None

    def data(self, index: QModelIndex, role: int = Qt.ItemDataRole.DisplayRole):
        if not index.isValid():
            return None
        r, c = index.row(), index.column()
        if r < 0 or r >= len(self._rows):
            return None
        row = self._rows[r]
        prov = row.provider
        ip = row.ip

        ok, latency, _prov2 = self._ip_results.get(ip, (None, None, None))
        status = "Pending"
        lat_text = "---"
        lat_val = None
        if ok is True:
            status = "Success"
            lat_val = latency if latency is not None else None
            lat_text = str(lat_val) if lat_val is not None else "---"
            if lat_val is not None and lat_val > self._max_latency:
                status = "High Latency"
        elif ok is False:
            status = "Fail"

        if c == 0:
            if role == Qt.ItemDataRole.DisplayRole:
                return prov
            if role == Qt.ItemDataRole.DecorationRole:
                ic = icon_for_provider(self._providers, prov)
                return ic if (ic is not None and not ic.isNull()) else None

        if c == 1 and role == Qt.ItemDataRole.DisplayRole:
            return ip

        if c == 2 and role == Qt.ItemDataRole.DisplayRole:
            return status

        if c == 3:
            if role == Qt.ItemDataRole.DisplayRole:
                return lat_text
            if role == Qt.ItemDataRole.ForegroundRole and lat_val is not None:
                return latency_color(int(lat_val), self._max_latency)

        if role == Qt.ItemDataRole.TextAlignmentRole:
            return int(Qt.AlignmentFlag.AlignCenter)

        return None

    def flags(self, index: QModelIndex):
        if not index.isValid():
            return Qt.ItemFlag.NoItemFlags
        return Qt.ItemFlag.ItemIsEnabled | Qt.ItemFlag.ItemIsSelectable
try:
    from speedtest import Speedtest, ConfigRetrievalError, SpeedtestBestServerFailure
except Exception:
    Speedtest = None
    ConfigRetrievalError = Exception
    SpeedtestBestServerFailure = Exception


try:
    import requests
except Exception:
    requests = None
try:
    import socks  # type: ignore
except Exception:
    socks = None
import urllib.request
import urllib.error


class CancelledError(Exception):
    """Raised when the speed test has been cancelled by the user."""



# -------------------------- Non-blocking large loaders --------------------------

class _ResultWorker(QObject):
    """Run a callable in a QThread and emit the result."""
    progress = pyqtSignal(int, int)   # done, total
    finished = pyqtSignal(object)     # result
    error = pyqtSignal(str)
    cancelled = pyqtSignal()

    def __init__(self, fn, *args, **kwargs):
        super().__init__()
        self._fn = fn
        self._args = args
        self._kwargs = kwargs
        self._cancel = False

    def request_cancel(self):
        self._cancel = True

    def is_cancelled(self) -> bool:
        return bool(self._cancel)

    def run(self):
        try:
            res = self._fn(self, *self._args, **self._kwargs)
            if self._cancel:
                self.cancelled.emit()
                return
            self.finished.emit(res)
        except Exception as e:
            self.error.emit(str(e))


def _chunked_iter(seq, chunk_size: int):
    for i in range(0, len(seq), chunk_size):
        yield i, seq[i:i + chunk_size]

def _default_xray_path() -> Path:
    base_dir = bin_dir()
    if sys.platform.startswith("win"):
        return base_dir / "xray.exe"
    return base_dir / "xray"


def _proxy_scheme_for_inbound(protocol: str) -> str:
    return "socks5h" if (protocol or "").strip().lower() == "socks" else "http"


def _wait_port_open(host: str, port: int, total_deadline_sec: float, socket_timeout_ms: int, interval: float = 0.25) -> bool:
    deadline = time.monotonic() + float(total_deadline_sec)
    per_try_timeout = max(0.001, socket_timeout_ms / 1000.0)
    while time.monotonic() < deadline:
        try:
            with socket.create_connection((host, port), timeout=per_try_timeout):
                return True
        except OSError:
            time.sleep(interval)
    return False


def _pick_free_port(host: str = "127.0.0.1", tries: int = 30) -> int:
    for _ in range(tries):
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.bind((host, 0))
            port = s.getsockname()[1]
        time.sleep(0.02)
        return port
    raise RuntimeError("Unable to pick a free port for inbound.")


def get_public_ip(proxy_url: str | None = None, timeout: float = 6.0) -> str:
    endpoints = [
        "https://api.ipify.org",
        "https://ifconfig.me/ip",
        "https://ipinfo.io/ip",
    ]
    if requests is not None:
        proxies = {"http": proxy_url, "https": proxy_url} if proxy_url else None
        for url in endpoints:
            try:
                resp = requests.get(url, timeout=timeout, proxies=proxies)
                if resp.ok:
                    ip_text = resp.text.strip()
                    try:
                        ipaddress.ip_address(ip_text)
                        return ip_text
                    except ValueError:
                        continue
            except Exception:
                continue

    handlers = []
    if proxy_url:
        handlers.append(urllib.request.ProxyHandler({"http": proxy_url, "https": proxy_url}))
    opener = urllib.request.build_opener(*handlers) if handlers else urllib.request.build_opener()
    urllib.request.install_opener(opener)
    for url in endpoints:
        try:
            with opener.open(url, timeout=timeout) as resp:
                data = resp.read().decode("utf-8").strip()
                try:
                    ipaddress.ip_address(data)
                    return data
                except ValueError:
                    continue
        except Exception:
            continue
    return "Unknown"


def _country_code_to_flag(cc: str) -> str:
    cc = (cc or "").strip().upper()
    if len(cc) != 2 or not cc.isalpha():
        return ""
    return chr(0x1F1E6 + ord(cc[0]) - 65) + chr(0x1F1E6 + ord(cc[1]) - 65)


def get_country_info(ip: str, timeout: float = 4.0) -> tuple[str, str]:
    """Return (country_name, flag_emoji) for an IP using a lightweight geo API."""
    ip = (ip or "").strip()
    if not ip or ip.lower() == "unknown":
        return ("", "")
    if requests is None:
        return ("", "")
    url = f"http://ip-api.com/json/{ip}"
    try:
        r = requests.get(url, timeout=timeout)
        r.raise_for_status()
        data = r.json()
        if data.get("status") != "success":
            return ("", "")
        country = str(data.get("country") or "")
        code = str(data.get("countryCode") or "")
        return (country, _country_code_to_flag(code))
    except Exception:
        return ("", "")


def _strip_geodata_inplace(cfg: dict) -> Dict[str, int]:
    stats = {
        "dns_hosts_removed": 0,
        "dns_server_domains_filtered": 0,
        "dns_server_expectIPs_filtered": 0,
        "routing_rule_removed": 0,
        "routing_rule_domain_items_filtered": 0,
        "routing_rule_ip_items_filtered": 0,
    }

    dns = cfg.get("dns")
    if isinstance(dns, dict):
        hosts = dns.get("hosts")
        if isinstance(hosts, dict):
            keys_to_del = [k for k in list(hosts.keys()) if isinstance(k, str) and (k.lower().startswith("geosite:") or k.lower().startswith("geoip:"))]
            for k in keys_to_del:
                del hosts[k]
            stats["dns_hosts_removed"] += len(keys_to_del)
            if not hosts:
                dns.pop("hosts", None)

        servers = dns.get("servers")
        if isinstance(servers, list):
            for srv in servers:
                if isinstance(srv, dict):
                    doms = srv.get("domains")
                    if isinstance(doms, list):
                        keep = []
                        for d in doms:
                            if isinstance(d, str) and d.strip().lower().startswith("geosite:"):
                                stats["dns_server_domains_filtered"] += 1
                            else:
                                keep.append(d)
                        if keep:
                            srv["domains"] = keep
                        else:
                            srv.pop("domains", None)
                    exips = srv.get("expectIPs")
                    if isinstance(exips, list):
                        keep2 = []
                        for e in exips:
                            if isinstance(e, str) and e.strip().lower().startswith("geoip:"):
                                stats["dns_server_expectIPs_filtered"] += 1
                            else:
                                keep2.append(e)
                        if keep2:
                            srv["expectIPs"] = keep2
                        else:
                            srv.pop("expectIPs", None)

    routing = cfg.get("routing")
    if isinstance(routing, dict):
        rules = routing.get("rules")
        if isinstance(rules, list):
            new_rules = []
            for rule in rules:
                if not isinstance(rule, dict):
                    new_rules.append(rule)
                    continue

                if "domain" in rule and isinstance(rule["domain"], list):
                    kept_domain = []
                    for item in rule["domain"]:
                        if isinstance(item, str) and item.strip().lower().startswith("geosite:"):
                            stats["routing_rule_domain_items_filtered"] += 1
                        else:
                            kept_domain.append(item)
                    if kept_domain:
                        rule["domain"] = kept_domain
                    else:
                        rule.pop("domain", None)

                if "ip" in rule and isinstance(rule["ip"], list):
                    kept_ip = []
                    for item in rule["ip"]:
                        if isinstance(item, str) and item.strip().lower().startswith("geoip:"):
                            stats["routing_rule_ip_items_filtered"] += 1
                        else:
                            kept_ip.append(item)
                    if kept_ip:
                        rule["ip"] = kept_ip
                    else:
                        rule.pop("ip", None)

                keys = set(rule.keys())
                condition_keys = {
                    "domain", "ip", "port", "source",
                    "user", "network", "protocol",
                    "attrs", "inboundTag", "sourcePort",
                    "outboundTag", "type"
                }
                present_conditions = [k for k in keys if k in condition_keys and k not in {"outboundTag", "type"}]
                if not present_conditions:
                    stats["routing_rule_removed"] += 1
                    continue

                new_rules.append(rule)

            routing["rules"] = new_rules

    return stats


def _override_proxy_address_inplace(cfg: dict, new_addr: str) -> bool:
    outbounds = cfg.get("outbounds")
    if not isinstance(outbounds, list):
        return False

    target = None
    for ob in outbounds:
        if isinstance(ob, dict) and ob.get("protocol") in ("vless", "vmess") and ob.get("tag") == "proxy":
            target = ob
            break

    if target is None:
        for ob in outbounds:
            if isinstance(ob, dict) and ob.get("protocol") in ("vless", "vmess"):
                target = ob
                break

    if target is None:
        return False

    settings = target.get("settings")
    if not isinstance(settings, dict):
        return False

    vnext = settings.get("vnext")
    if not isinstance(vnext, list):
        return False

    replaced = False
    for node in vnext:
        if isinstance(node, dict):
            node["address"] = new_addr
            replaced = True
    return replaced


def _extract_current_proxy_address(cfg: dict) -> Optional[str]:
    outbounds = cfg.get("outbounds")
    if not isinstance(outbounds, list):
        return None

    for ob in outbounds:
        if isinstance(ob, dict) and ob.get("protocol") in ("vless", "vmess") and ob.get("tag") == "proxy":
            settings = ob.get("settings")
            if isinstance(settings, dict):
                vnext = settings.get("vnext")
                if isinstance(vnext, list) and vnext:
                    addr = vnext[0].get("address")
                    if isinstance(addr, str):
                        return addr

    for ob in outbounds:
        if isinstance(ob, dict) and ob.get("protocol") in ("vless", "vmess"):
            settings = ob.get("settings")
            if isinstance(settings, dict):
                vnext = settings.get("vnext")
                if isinstance(vnext, list) and vnext:
                    addr = vnext[0].get("address")
                    if isinstance(addr, str):
                        return addr

    return None



# -------------------------- HTTP-based Speed Test (more stable) --------------------------

CACHEFLY_TEMPLATE = "https://cachefly.cachefly.net/{size}mb.test"
HTTPBIN_UPLOAD_URL = "https://httpbin.org/post"
LATENCY_URL = "https://www.google.com/generate_204"

DEFAULT_DL_SIZE_MB = 10
DEFAULT_UL_SIZE_MB = 5

DEFAULT_DL_CONNECT_TO = 8.0
DEFAULT_DL_READ_TO = 45.0
DEFAULT_UL_CONNECT_TO = 8.0
DEFAULT_UL_READ_TO = 60.0


def _fmt_ping_ms(v: float) -> str:
    """Format ping milliseconds as an integer string without decimals."""
    try:
        if isinstance(v, (int, float)) and v > 0:
            return str(int(round(float(v))))
    except Exception:
        pass
    return "-1"


@dataclass
class PingResult:
    attempts: int
    samples_ms: list[float]
    average_ms: float
    median_ms: float
    p95_ms: float


class UploadStream(io.RawIOBase):
    """Deterministic file-like stream for upload with a known Content-Length."""

    def __init__(self, total_bytes: int, chunk_size: int = 256 * 1024,
                 progress_cb=None, cancel_cb=None) -> None:
        super().__init__()
        self._total = int(max(0, total_bytes))
        self._sent = 0
        self._chunk = int(max(1024, chunk_size))
        self._progress_cb = progress_cb
        self._cancel_cb = cancel_cb
        self._pattern = bytes([i % 256 for i in range(1024)])
        self._lock = threading.Lock()

    def readable(self) -> bool:
        return True

    def __len__(self) -> int:
        return self._total

    def tell(self) -> int:
        with self._lock:
            return self._sent

    def read(self, size: int = -1) -> bytes:
        with self._lock:
            if self._cancel_cb and self._cancel_cb():
                raise IOError("Upload cancelled by user")

            if self._sent >= self._total:
                return b""

            if size is None or size < 0:
                size = min(self._chunk, self._total - self._sent)
            else:
                size = min(int(size), self._total - self._sent)

            reps, rem = divmod(size, len(self._pattern))
            chunk = self._pattern * reps + (self._pattern[:rem] if rem else b"")
            self._sent += len(chunk)
            if self._progress_cb:
                self._progress_cb(self._sent, self._total)
            return chunk

    def seekable(self) -> bool:
        return False

    def writable(self) -> bool:
        return False


class SpeedTestWorker(QThread):
    status_update = pyqtSignal(str)
    progress_update = pyqtSignal(int)
    throughput_update = pyqtSignal(str, float)  # "download"|"upload", MB/s
    result_ready = pyqtSignal(dict)
    error_occurred = pyqtSignal(str)
    ip_update = pyqtSignal(str, str)  # "before_proxy"|"after_proxy", ip

    def __init__(
        self,
        use_proxy: bool = True,
        xray_config_json: str | None = None,
        xray_path: Path | None = None,
        use_random_port: bool = True,
        proxy_socket_timeout_ms: int = 1000,
        proxy_ready_deadline_sec: int = 5,
        address_override: Optional[str] = None,
        dl_size_mb: int = DEFAULT_DL_SIZE_MB,
        ul_size_mb: int = DEFAULT_UL_SIZE_MB,
        latency_attempts: int = 1,
        dl_connect_timeout: float = DEFAULT_DL_CONNECT_TO,
        dl_read_timeout: float = DEFAULT_DL_READ_TO,
        ul_connect_timeout: float = DEFAULT_UL_CONNECT_TO,
        ul_read_timeout: float = DEFAULT_UL_READ_TO,
        download_url: Optional[str] = None,
        upload_url: Optional[str] = None,
        ping_url: Optional[str] = None,
        dl_time_limit_enabled: bool = True,
        dl_time_limit_seconds: float = 5.0,
        test_mode: str = "download",
    ) -> None:
        super().__init__()
        self._cancelled = False

        self._use_proxy = True if use_proxy is None else bool(use_proxy)
        self._xray_config_json = xray_config_json or ""
        self._xray_path = xray_path or _default_xray_path()
        self._use_random_port = use_random_port

        self._proxy_socket_timeout_ms = proxy_socket_timeout_ms
        self._proxy_ready_deadline_sec = proxy_ready_deadline_sec

        self._download_MBps = 0.0
        self._upload_MBps = 0.0
        self._latency = 0.0

        # CacheFly method settings
        self._dl_size_mb = int(max(1, dl_size_mb))
        self._ul_size_mb = int(max(1, ul_size_mb))
        self._latency_attempts = int(max(1, latency_attempts))
        self._dl_connect_timeout = float(max(0.1, dl_connect_timeout))
        self._dl_read_timeout = float(max(0.1, dl_read_timeout))
        self._ul_connect_timeout = float(max(0.1, ul_connect_timeout))
        self._ul_read_timeout = float(max(0.1, ul_read_timeout))

        self._test_mode = str(test_mode or "download").strip().lower()
        if self._test_mode not in ("ping_only", "download", "upload", "both"):
            self._test_mode = "download"

        self._step_errors: Dict[str, str] = {}
        self._step_skipped: Dict[str, bool] = {"download": False, "upload": False}
        self._dl_time_limit_enabled = bool(dl_time_limit_enabled)
        self._dl_time_limit_seconds = float(max(1.0, dl_time_limit_seconds))

        raw_dl_url = (download_url or "").strip()
        if raw_dl_url:
            if "{size}" in raw_dl_url:
                self._download_url = raw_dl_url.format(size=self._dl_size_mb)
            else:
                self._download_url = raw_dl_url
        else:
            self._download_url = CACHEFLY_TEMPLATE.format(size=self._dl_size_mb)

        raw_ul_url = (upload_url or "").strip()
        self._upload_url = raw_ul_url if raw_ul_url else HTTPBIN_UPLOAD_URL

        raw_ping_url = (ping_url or "").strip()
        self._latency_url = raw_ping_url if raw_ping_url else LATENCY_URL

        # CacheFly method settings
        self._dl_size_mb = int(max(1, dl_size_mb))
        self._ul_size_mb = int(max(1, ul_size_mb))
        self._latency_attempts = int(max(1, latency_attempts))
        self._dl_connect_timeout = float(max(0.1, dl_connect_timeout))
        self._dl_read_timeout = float(max(0.1, dl_read_timeout))
        self._ul_connect_timeout = float(max(0.1, ul_connect_timeout))
        self._ul_read_timeout = float(max(0.1, ul_read_timeout))

        self._xray_proc: subprocess.Popen | None = None
        self._xray_tmpfile: tempfile.NamedTemporaryFile | None = None
        self._proxy_host = "127.0.0.1"
        self._proxy_port = None  # type: int | None
        self._proxy_url: str | None = None
        self._proxy_public_ip: str | None = None
        self._country_text: str = "---"

        self._saved_env_proxy: Dict[str, str | None] = {}

        self._address_override = address_override
        self._effective_target_address: Optional[str] = None

    def request_cancel(self) -> None:
        self._cancelled = True
        self._stop_xray()

    def run(self) -> None:
        try:
            if not self._use_proxy:
                raise RuntimeError("Direct mode is disabled. Please run the test via Xray proxy.")

            ip_no_proxy = get_public_ip(proxy_url=None)
            self.ip_update.emit("before_proxy", ip_no_proxy)

            self._prepare_and_start_xray()
            if self._cancelled:
                raise CancelledError()

            if self._proxy_url:
                # Apply env proxy for any legacy calls, but do NOT fetch proxy IP yet.
                self._apply_env_proxy(self._proxy_url)

            # ---- Tests order: ping -> (server ip/country) -> download -> upload ----
            # Ping is the success criteria: if we get a latency value, Status=Success, otherwise Fail.
            try:
                self._step_find_server()
            except Exception as exc:
                self._latency = -1.0
                try:
                    self.throughput_update.emit("ping", -1.0)
                except Exception:
                    pass
                self._step_errors["ping"] = str(exc)

            # If ping succeeded, now fetch the proxy public IP and country (Server IP / Country columns).
            if "ping" not in self._step_errors and self._proxy_url:
                try:
                    ip_via_proxy = get_public_ip(proxy_url=self._proxy_url)
                    self._proxy_public_ip = ip_via_proxy
                    self.ip_update.emit("after_proxy", ip_via_proxy)
                    country_name, flag = get_country_info(ip_via_proxy)
                    if country_name:
                        self._country_text = (f"{flag} {country_name}".strip())
                        self.ip_update.emit("country", self._country_text)
                except Exception:
                    # Non-fatal: keep proxy IP unknown; tests can still proceed.
                    pass

            if self._cancelled:
                raise CancelledError()

            # Decide which throughput tests to run
            run_dl = self._test_mode in ("download", "both")
            run_ul = self._test_mode in ("upload", "both")

            if not run_dl:
                self._step_skipped["download"] = True
            if not run_ul:
                self._step_skipped["upload"] = True

            # If latency failed, skip the rest (proxy likely not ready / routing issue)
            if "ping" not in self._step_errors:
                if run_dl:
                    try:
                        self._step_download()
                    except Exception as exc:
                        self._download_MBps = -1.0
                        self.throughput_update.emit("download", -1.0)
                        self._step_errors["download"] = str(exc)

                    if self._cancelled:
                        raise CancelledError()

                if run_ul:
                    try:
                        self._step_upload()
                    except Exception as exc:
                        self._upload_MBps = -1.0
                        self.throughput_update.emit("upload", -1.0)
                        self._step_errors["upload"] = str(exc)

                    if self._cancelled:
                        raise CancelledError()
            else:
                # Keep table clear: mark download/upload as skipped when latency fails
                self._step_skipped["download"] = True
                self._step_skipped["upload"] = True

            self.progress_update.emit(100)
        except CancelledError:
            self.status_update.emit("Test cancelled by user.")
            self.progress_update.emit(0)
        except Exception as exc:
            tb = traceback.format_exc()
            message = f"{str(exc)}\n\n{tb}"
            self.error_occurred.emit(message)
        finally:
            self._restore_env_proxy()
            self._stop_xray()

    def _parse_inbound(self, cfg: dict) -> Tuple[dict, str]:
        inbounds = cfg.get("inbounds", [])
        if not isinstance(inbounds, list) or not inbounds:
            raise RuntimeError("Xray config lacks a valid 'inbounds' section.")
        preferred = ("mixed", "http", "socks")
        selected = None
        for p in preferred:
            for inbound in inbounds:
                if isinstance(inbound, dict) and inbound.get("protocol") == p:
                    selected = inbound
                    break
            if selected:
                break
        if selected is None:
            selected = inbounds[0]
        protocol = selected.get("protocol", "")
        return selected, protocol

    def _prepare_and_start_xray(self) -> None:
        if not self._xray_path.exists():
            raise RuntimeError(f"Xray executable not found:\n{self._xray_path}")

        self.status_update.emit("Preparing Xray configuration ...")
        self.progress_update.emit(3)

        try:
            cfg = json.loads(self._xray_config_json)
        except json.JSONDecodeError as e:
            raise RuntimeError(f"Invalid JSON configuration:\n{e}") from e

        strip_stats = _strip_geodata_inplace(cfg)
        removed_total = sum(strip_stats.values())
        if removed_total > 0:
            self.status_update.emit(f"Removed geosite/geoip references (total: {removed_total})")
        else:
            self.status_update.emit("No geosite/geoip references found.")

        if self._address_override:
            ok = _override_proxy_address_inplace(cfg, self._address_override.strip())
            if not ok:
                raise RuntimeError(
                    "Unable to override 'address' in outbounds → vless/vmess → settings → vnext.\n"
                    "Check config structure (tag='proxy' or first vless/vmess)."
                )
            self._effective_target_address = self._address_override.strip()
        else:
            self._effective_target_address = _extract_current_proxy_address(cfg) or "Unknown"

        inbound, protocol = self._parse_inbound(cfg)

        host = inbound.get("listen", "127.0.0.1")
        if host in ("0.0.0.0", "::"):
            host = "127.0.0.1"
        if self._use_random_port or not isinstance(inbound.get("port"), int):
            port = _pick_free_port(host)
            inbound["port"] = port
        else:
            port = int(inbound.get("port"))
        inbound["listen"] = host

        self._proxy_host, self._proxy_port = host, port
        scheme = _proxy_scheme_for_inbound(protocol)
        self._proxy_url = f"{scheme}://{host}:{port}"

        self._xray_tmpfile = tempfile.NamedTemporaryFile(prefix="xray_cfg_", suffix=".json", delete=False)
        self._xray_tmpfile.write(json.dumps(cfg, ensure_ascii=False).encode("utf-8"))
        self._xray_tmpfile.flush()
        self._xray_tmpfile.close()

        cmd = [str(self._xray_path), "run", "-c", self._xray_tmpfile.name]

        creationflags = 0
        startupinfo = None
        if sys.platform.startswith("win"):
            creationflags = getattr(subprocess, "CREATE_NO_WINDOW", 0)

        self._xray_proc = subprocess.Popen(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            creationflags=creationflags,
            startupinfo=startupinfo,
            cwd=str(self._xray_path.parent),
        )
        _raise_process_priority(self._xray_proc.pid)

        self.status_update.emit(f"Waiting for proxy to be ready at {host}:{port} ...")

        ready = _wait_port_open(
            host=host,
            port=port,
            total_deadline_sec=float(self._proxy_ready_deadline_sec),
            socket_timeout_ms=int(self._proxy_socket_timeout_ms),
            interval=0.2,
        )
        if ready:
            self.status_update.emit(f"Xray is ready (random inbound port: {port}).")
            self.progress_update.emit(10)

            # Extra readiness: make sure the proxy can actually reach the internet (and that the
            # overridden address is applied) before running tests.
            # Some configs start listening fast but need a moment to establish outbound connectivity.
            preflight_deadline = time.time() + max(3.0, float(self._proxy_ready_deadline_sec))
            last_ip = "Unknown"
            while time.time() < preflight_deadline and not self._cancelled:
                last_ip = get_public_ip(proxy_url=self._proxy_url, timeout=4.0)
                if last_ip != "Unknown":
                    break
                time.sleep(0.4)

            if last_ip == "Unknown":
                raise RuntimeError(
                    "Xray inbound is listening but the proxy could not reach the internet (IP check failed). "
                    "Please verify outbound settings / routing and that the target address is reachable."
                )

            return


        status_msg = (
            f"Proxy did not become ready (Timeout: {self._proxy_ready_deadline_sec}s, "
            f"Socket={self._proxy_socket_timeout_ms}ms)"
        )
        self.status_update.emit(status_msg)

        if self._xray_proc and self._xray_proc.poll() is not None:
            try:
                out, err = self._xray_proc.communicate(timeout=1.0)
            except Exception:
                out, err = b"", b""
            out_txt = out.decode("utf-8", errors="ignore")
            err_txt = err.decode("utf-8", errors="ignore")
            raise RuntimeError(
                status_msg + "\n"
                "Xray execution terminated with error.\n"
                f"Exit code: {self._xray_proc.returncode}\n"
                f"Stdout:\n{out_txt[-1500:]}\n\nStderr:\n{err_txt[-1500:]}\n"
                "Please check xray executable path and config validity."
            )

        raise RuntimeError(status_msg)

    def _stop_xray(self) -> None:
        try:
            if self._xray_proc and self._xray_proc.poll() is None:
                self._xray_proc.terminate()
                try:
                    self._xray_proc.wait(timeout=3)
                except subprocess.TimeoutExpired:
                    self._xray_proc.kill()
        except Exception:
            pass
        finally:
            self._xray_proc = None
            if self._xray_tmpfile:
                try:
                    Path(self._xray_tmpfile.name).unlink(missing_ok=True)
                except Exception:
                    pass
                self._xray_tmpfile = None

    def _apply_env_proxy(self, proxy_url: str) -> None:
        keys = ["HTTP_PROXY", "http_proxy", "HTTPS_PROXY", "https_proxy"]
        self._saved_env_proxy = {k: os.environ.get(k) for k in keys}
        for k in keys:
            os.environ[k] = proxy_url

    def _restore_env_proxy(self) -> None:
        if not self._saved_env_proxy:
            return
        for k, v in self._saved_env_proxy.items():
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v
        self._saved_env_proxy = {}


# -------------------------- CacheFly measurement helpers --------------------------

def _create_session(self):
    if requests is None or HTTPAdapter is None or Retry is None:
        raise RuntimeError("The 'requests' dependency is required for CacheFly method.")

    session = requests.Session()
    # Don't rely on global environment variables; wire the proxy explicitly.
    session.trust_env = False
    if getattr(self, "_proxy_url", None):
        if str(self._proxy_url).startswith("socks") and socks is None:
            raise RuntimeError("PySocks is required for SOCKS proxy support. Please install requests[socks].")
        session.proxies.update({"http": self._proxy_url, "https": self._proxy_url})

    retry_strategy = Retry(
        total=2,
        read=2,
        connect=2,
        status=2,
        status_forcelist=[429, 500, 502, 503, 504],
        backoff_factor=0.4,
    )
    adapter = HTTPAdapter(max_retries=retry_strategy, pool_maxsize=4)
    session.mount("http://", adapter)
    session.mount("https://", adapter)
    session.headers.update(
        {
            "User-Agent": "PyQt-SpeedTest/CacheFly (+https://example.com)",
            "Accept-Encoding": "identity",
        }
    )
    return session


def _measure_latency(self, session) -> PingResult:
    """Measure 'ping' via an HTTP(S) request through the proxy.

    Many proxy clients display latency as an *HTTP ping* (time to get a response code)
    through the tunnel. We measure the time to receive response headers from:
        https://www.google.com/generate_204

    IMPORTANT: we intentionally disable automatic retries/backoff for this request,
    otherwise a transient failure can inflate the displayed ping to seconds.
    """
    self._check_cancelled()

    # You can override these from config if needed.
    url = getattr(self, "_latency_url", "https://www.google.com/generate_204")
    attempts = int(getattr(self, "_latency_attempts", 1))
    attempts = max(1, attempts)

    # Keep timeouts small; this endpoint returns 204 quickly when reachable.
    connect_to = float(getattr(self, "_latency_connect_timeout", 2.0))
    read_to = float(getattr(self, "_latency_read_timeout", 2.0))

    samples: list[float] = []

    # Build a *dedicated* session for latency with NO retries/backoff.
    try:
        import requests  # type: ignore
        from requests.adapters import HTTPAdapter  # type: ignore
    except Exception as e:
        raise RuntimeError(f"requests is required for latency check: {e}")

    ping_sess = requests.Session()
    ping_sess.trust_env = False
    # Reuse the already computed proxy URL (works for both HTTP and SOCKS proxies when supported).
    if getattr(self, "_proxy_url", None):
        if str(self._proxy_url).startswith("socks") and socks is None:
            raise RuntimeError("PySocks is required for SOCKS proxy support. Please install requests[socks].")
        ping_sess.proxies.update({"http": self._proxy_url, "https": self._proxy_url})

    # Disable retries entirely for a clean latency number.
    no_retry_adapter = HTTPAdapter(max_retries=0, pool_maxsize=2)
    ping_sess.mount("http://", no_retry_adapter)
    ping_sess.mount("https://", no_retry_adapter)

    # Some networks slow down if the connection is force-closed; let requests reuse if possible.
    headers = {
        "Cache-Control": "no-cache",
        "Pragma": "no-cache",
        "Accept": "*/*",
        "User-Agent": "latency-check/1.0",
    }

    for _ in range(attempts):
        self._check_cancelled()
        start = time.perf_counter()
        resp = None
        try:
            # HEAD is enough (no body), and measures TLS+HTTP response time.
            resp = ping_sess.head(
                url,
                timeout=(connect_to, read_to),
                allow_redirects=False,
                headers=headers,
            )
            sc = int(getattr(resp, "status_code", 0) or 0)
            # Accept 2xx/3xx as reachable. (generate_204 should be 204.)
            if sc and sc < 400:
                elapsed_ms = (time.perf_counter() - start) * 1000.0
                if elapsed_ms > 0:
                    samples.append(elapsed_ms)
            else:
                raise RuntimeError(f"Latency URL returned status {sc}")
        except Exception:
            # Ignore failed attempts; we'll return FAIL if none succeed.
            pass
        finally:
            try:
                if resp is not None:
                    resp.close()
            except Exception:
                pass

    try:
        ping_sess.close()
    except Exception:
        pass

    if not samples:
        return PingResult(attempts=0, samples_ms=[], average_ms=float("inf"), median_ms=float("inf"), p95_ms=float("inf"))

    # Robust aggregation: median as primary, also compute avg and p95.
    avg = float(sum(samples) / len(samples))
    try:
        med = float(statistics.median(samples))
    except Exception:
        med = avg
    try:
        # Use p95 to show worst-case; keep it around for UI if needed.
        p95 = float(statistics.quantiles(samples, n=20)[-1]) if len(samples) >= 2 else avg
    except Exception:
        p95 = avg

    return PingResult(
        attempts=len(samples),
        samples_ms=samples,
        average_ms=avg,
        median_ms=med,
        p95_ms=p95,
    )

def _measure_download(self, session) -> None:
    self._check_cancelled()
    if getattr(self, "_dl_time_limit_enabled", False):
        self.status_update.emit("Downloading (time window) ...")
    else:
        self.status_update.emit(f"Downloading from CacheFly ({self._dl_size_mb} MB) ...")
    self.progress_update.emit(45)
    self.throughput_update.emit("download", 0.0)

    bytes_downloaded = 0
    start_time = time.perf_counter()

    resp = session.get(
        self._download_url,
        stream=True,
        timeout=(self._dl_connect_timeout, self._dl_read_timeout),
        allow_redirects=True,
    )
    resp.raise_for_status()

    total_bytes = None
    cl = resp.headers.get("Content-Length")
    if cl and str(cl).isdigit():
        total_bytes = int(cl)

    chunk_size = 256 * 1024
    window = deque()
    window_bytes = 0

    try:
        peak_MBps = 0.0
        for chunk in resp.iter_content(chunk_size=chunk_size):
            self._check_cancelled()
            if not chunk:
                continue

            now = time.perf_counter()
            blen = len(chunk)
            bytes_downloaded += blen

            window.append((now, blen))
            window_bytes += blen

            one_sec_ago = now - 1.0
            while window and window[0][0] < one_sec_ago:
                _, b_old = window.popleft()
                window_bytes -= b_old

            instant_MBps = window_bytes / (1024 * 1024)
            if instant_MBps > peak_MBps:
                peak_MBps = instant_MBps
            self.throughput_update.emit("download", float(instant_MBps))

            if getattr(self, "_dl_time_limit_enabled", False):
                elapsed_now = now - start_time
                pct = min(70, 45 + int((elapsed_now / self._dl_time_limit_seconds) * 25))
                self.progress_update.emit(pct)
                if elapsed_now >= self._dl_time_limit_seconds:
                    break
            elif total_bytes:
                pct = min(70, 45 + int((bytes_downloaded / total_bytes) * 25))
                self.progress_update.emit(pct)
    finally:
        try:
            resp.close()
        except Exception:
            pass

    elapsed = time.perf_counter() - start_time
    if elapsed <= 0 or bytes_downloaded == 0:
        raise RuntimeError("Download failed; no data received.")

    if getattr(self, "_dl_time_limit_enabled", False):
        self._download_MBps = float(peak_MBps)
    else:
        self._download_MBps = bytes_downloaded / (elapsed * 1024 * 1024)
    self.progress_update.emit(70)
    self.throughput_update.emit("download", float(self._download_MBps))

def _measure_upload(self, session) -> None:
    self._check_cancelled()
    size_bytes = int(self._ul_size_mb * 1024 * 1024)
    self.status_update.emit(f"Uploading to HTTPBin ({self._ul_size_mb} MB) ...")
    self.progress_update.emit(80)
    self.throughput_update.emit("upload", 0.0)

    window = deque()
    window_bytes = 0
    last_sent = 0
    last_time = time.perf_counter()

    def on_progress(sent: int, total: int):
        nonlocal window, window_bytes, last_sent, last_time
        now = time.perf_counter()
        delta_b = sent - last_sent
        dt = now - last_time
        last_sent = sent
        last_time = now

        if delta_b < 0:
            delta_b = 0
        if dt <= 0:
            dt = 1e-6

        window.append((now, delta_b))
        window_bytes += delta_b

        one_sec_ago = now - 1.0
        while window and window[0][0] < one_sec_ago:
            _, b_old = window.popleft()
            window_bytes -= b_old

        instant_MBps = window_bytes / (1024 * 1024)
        self.throughput_update.emit("upload", float(instant_MBps))

        pct = 80 + int((sent / total) * 15) if total else 80
        self.progress_update.emit(min(95, pct))

    stream = UploadStream(
        total_bytes=size_bytes,
        chunk_size=256 * 1024,
        progress_cb=on_progress,
        cancel_cb=lambda: self._cancelled,
    )

    headers = {
        "Content-Type": "application/octet-stream",
        "Content-Length": str(size_bytes),
    }

    start_time = time.perf_counter()
    resp = session.post(
        self._upload_url,
        data=stream,
        headers=headers,
        timeout=(self._ul_connect_timeout, self._ul_read_timeout),
    )
    resp.raise_for_status()
    elapsed = time.perf_counter() - start_time

    sent = stream.tell()
    if elapsed <= 0 or sent == 0:
        raise RuntimeError("Upload failed; no data sent.")

    self._upload_MBps = sent / (elapsed * 1024 * 1024)
    self.progress_update.emit(95)
    self.throughput_update.emit("upload", float(self._upload_MBps))

def _step_find_server(self) -> None:
    # Latency is measured via HTTPS request to generate_204 through the proxy.
    session = self._create_session()
    try:
        latency = self._measure_latency(session)
        val = float(latency.median_ms) if latency is not None else float("inf")
        # If no successful samples (or non-finite), treat as ping failure.
        if (not getattr(latency, "attempts", 0)) or (not math.isfinite(val)) or val <= 0:
            self._latency = -1.0
            try:
                self.throughput_update.emit("ping", -1.0)
            except Exception:
                pass
            raise RuntimeError("Ping failed (no successful generate_204 response).")

        self._latency = val
        try:
            self.throughput_update.emit("ping", float(self._latency))
        except Exception:
            pass
    finally:
        session.close()

def _step_download(self) -> None:
    session = self._create_session()
    try:
        self._measure_download(session)
    finally:
        session.close()

def _step_upload(self) -> None:
    session = self._create_session()
    try:
        self._measure_upload(session)
    finally:
        session.close()

    results: Dict[str, float | str] = {
        "download_MBps": self._download_MBps,
        "upload_MBps": self._upload_MBps,
        "ping_ms": self._latency,
        "server_host": "cachefly.cachefly.net",
        "server_name": "CacheFly Test",
        "server_sponsor": "CacheFly",
        "server_country": "",
        "target_address": self._effective_target_address or "Unknown",
        "proxy_ip": self._proxy_public_ip or "Unknown",
        "country": getattr(self, "_country_text", "") or "---",
        "errors": dict(self._step_errors),
        "skipped": dict(self._step_skipped),
    }
    self.result_ready.emit(results)

def _check_cancelled(self) -> None:
    if self._cancelled:
        raise CancelledError()

# ---- Bind CacheFly helper functions to the worker class (in case file edits moved them out of the class) ----
# This keeps SpeedTestWorker self._step_* calls working reliably.
SpeedTestWorker._create_session = _create_session
SpeedTestWorker._measure_latency = _measure_latency
SpeedTestWorker._measure_download = _measure_download
SpeedTestWorker._measure_upload = _measure_upload
SpeedTestWorker._step_find_server = _step_find_server
SpeedTestWorker._step_download = _step_download
SpeedTestWorker._step_upload = _step_upload
SpeedTestWorker._check_cancelled = _check_cancelled



class SpeedTestGUI(QMainWindow):
    def __init__(self, embed_mode: bool = False) -> None:
        super().__init__()
        self.worker: SpeedTestWorker | None = None
        self._xray_path = _default_xray_path()
        self._config_text: str = ""

        # embedding mode (used by main IP scanner app)
        self._embed_mode = bool(embed_mode)

        # provider → icon mapping (optional, supplied by host app)
        self._provider_icons: Dict[str, QIcon] = {}


        # providers data (from ip.json in host app) + compiled IPv4 networks for fast detection
        self._providers: Dict[str, dict] = {}
        self._provider_networks: Dict[str, List[ipaddress.IPv4Network]] = {}

        # JSON config mode
        self._use_per_provider_json: bool = False
        self._global_config_text: str | None = None
        self._provider_configs: Dict[str, str] = {}

        # Batch state
        self._batch_mode: bool = False
        self._batch_abort: bool = False
        self._batch_ips: List[Tuple[str, str]] = []  # (provider, address)
        self._batch_current_row: int = -1
        self._batch_success_count: int = 0

        # Single test context row
        self._single_context_row: int = -1

        self._setup_window()
        self._build_layout()
        self._build_settings_dialog()

        self.results_table.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.results_table.customContextMenuRequested.connect(self._table_context_menu)
        self.results_table.setSortingEnabled(True)

    def _setup_window(self) -> None:
        self.setWindowTitle("Internet Speed Test (Xray Proxy)")
        if not self._embed_mode:
            self.resize(980, 900)

    def _build_layout(self) -> None:
        main_widget = QWidget()
        if self._embed_mode:
            # when embedded, we expose the central widget to host layout
            self.setCentralWidget(main_widget)
        else:
            self.setCentralWidget(main_widget)

        layout = QVBoxLayout()
        if self._embed_mode:
            layout.setContentsMargins(6, 6, 6, 6)
            layout.setSpacing(4)
        if not self._embed_mode:
            layout.setAlignment(Qt.AlignmentFlag.AlignTop)
        main_widget.setLayout(layout)
        if not self._embed_mode:

            title = QLabel("Internet Speed Test")
            title_font = QFont()
            title_font.setPointSize(16 if self._embed_mode else 18)
            title_font.setBold(True)
            title.setFont(title_font)
            title.setAlignment(Qt.AlignmentFlag.AlignCenter)
            layout.addWidget(title)

        # Xray config group kept only in standalone mode (embedded view is compact)
        if not self._embed_mode:
            xray_group = QGroupBox("")
            xray_layout = QVBoxLayout(xray_group)

            btns = QHBoxLayout()
            self.btn_load_json_file = QPushButton("Load JSON File")
            self.btn_load_json_file.clicked.connect(self._load_from_json_file)
            btns.addWidget(self.btn_load_json_file)

            self.btn_load_json_clipboard = QPushButton("Load JSON from Clipboard")
            self.btn_load_json_clipboard.clicked.connect(self._load_json_from_clipboard)
            btns.addWidget(self.btn_load_json_clipboard)

            self.config_status_label = QLabel("Config: not loaded")
            self.config_status_label.setStyleSheet("color: rgba(255,255,255,0.65);")
            btns.addStretch(1)
            btns.addWidget(self.config_status_label)
            xray_layout.addLayout(btns)

            layout.addWidget(xray_group)
        else:
            self.btn_load_json_file = None
            self.btn_load_json_clipboard = None
            self.config_status_label = QLabel("")

        # ---- Settings button ----
        settings_row = QHBoxLayout()
        self.btn_open_settings = QPushButton("Open Settings")
        self.btn_open_settings.clicked.connect(self._open_settings_dialog)
        settings_row.addWidget(self.btn_open_settings)

        self.settings_summary_label = QLabel("Settings: default")
        self.settings_summary_label.setStyleSheet("color: rgba(255,255,255,0.65);")
        settings_row.addWidget(self.settings_summary_label)
        settings_row.addStretch(1)
        layout.addLayout(settings_row)

        # Batch IP group
        batch_group = QGroupBox("Batch Test with IP/Address List")
        batch_layout = QVBoxLayout(batch_group)
        if not self._embed_mode:
            batch_hint = QLabel("Items are provided by the main window or loaded from TXT when standalone.")
            batch_hint.setWordWrap(True)
            batch_hint.setStyleSheet("color: rgba(255,255,255,0.65);")
            batch_layout.addWidget(batch_hint)

        ip_btns_row = QHBoxLayout()
        if not self._embed_mode:
            self.btn_load_ip_file = QPushButton("Load IP List (TXT)")
            self.btn_load_ip_file.clicked.connect(self._load_ip_list_file)
            ip_btns_row.addWidget(self.btn_load_ip_file)
        else:
            self.btn_load_ip_file = None

        self.batch_start_button = QPushButton("Start Batch Test")
        self.batch_start_button.clicked.connect(self._handle_batch_start)
        ip_btns_row.addWidget(self.batch_start_button)

        self.btn_remove_failed_batch = QPushButton("Remove Failed")
        self.btn_remove_failed_batch.clicked.connect(self._remove_failed_batch)
        ip_btns_row.addWidget(self.btn_remove_failed_batch)

        self.btn_save_success_ips = QPushButton("Save Success IPs")
        self.btn_save_success_ips.clicked.connect(self._show_save_success_menu)
        ip_btns_row.addWidget(self.btn_save_success_ips)

        self.btn_clear_batch_list = QPushButton("Clear List")
        self.btn_clear_batch_list.clicked.connect(self._clear_batch_list)
        ip_btns_row.addWidget(self.btn_clear_batch_list)

        ip_btns_row.addStretch(1)
        batch_layout.addLayout(ip_btns_row)

        counters_row = QHBoxLayout()
        self.ip_count_label = QLabel("Loaded items: 0")
        self.batch_progress_label = QLabel("Batch progress: -/-")
        self.success_count_label = QLabel("Success count: 0")
        for lb in (self.ip_count_label, self.batch_progress_label, self.success_count_label):
            lb.setStyleSheet("font-size: 13px; color: rgba(255,255,255,0.75);")
        counters_row.addWidget(self.ip_count_label)
        counters_row.addStretch(1)
        counters_row.addWidget(self.batch_progress_label)
        counters_row.addStretch(1)
        counters_row.addWidget(self.success_count_label)
        batch_layout.addLayout(counters_row)

        sort_row = QHBoxLayout()
        self.chk_sort_ping = QCheckBox("Sort by lowest ping during test")
        self.chk_sort_ping.stateChanged.connect(self._on_sort_ping_changed)
        sort_row.addWidget(self.chk_sort_ping)
        sort_row.addStretch(1)
        batch_layout.addLayout(sort_row)

        # Results table now includes Provider column with icon
        # Results table now includes Provider column with icon (virtualized model for large lists)
        self.results_table = QTableView()
        self.results_table.setAlternatingRowColors(True)
        self.results_table.setStyleSheet("QTableView { gridline-color: rgba(255,255,255,0.08); }")
        if self._embed_mode:
            self.results_table.setMinimumHeight(650)
        self.results_table.setSortingEnabled(False)

        self.results_model = SpeedTestBatchModel({}, [])
        self.results_proxy = QSortFilterProxyModel(self.results_table)
        self.results_proxy.setSourceModel(self.results_model)
        self.results_proxy.setSortCaseSensitivity(Qt.CaseSensitivity.CaseInsensitive)
        self.results_proxy.setSortRole(Qt.ItemDataRole.UserRole)
        self.results_table.setModel(self.results_proxy)

        header = self.results_table.horizontalHeader()
        header.setSectionResizeMode(0, QHeaderView.ResizeMode.ResizeToContents)  # Provider
        header.setSectionResizeMode(1, QHeaderView.ResizeMode.Stretch)          # Address
        header.setSectionResizeMode(2, QHeaderView.ResizeMode.ResizeToContents) # Status
        header.setSectionResizeMode(3, QHeaderView.ResizeMode.ResizeToContents) # Ping
        header.setSectionResizeMode(4, QHeaderView.ResizeMode.ResizeToContents) # Server IP
        header.setSectionResizeMode(5, QHeaderView.ResizeMode.ResizeToContents) # Country
        header.setSectionResizeMode(6, QHeaderView.ResizeMode.ResizeToContents) # Download
        header.setSectionResizeMode(7, QHeaderView.ResizeMode.ResizeToContents) # Upload

        batch_layout.addWidget(self.results_table)

        layout.addWidget(batch_group, 1)

        self.status_label = QLabel("Ready. Load JSON config and IP list to begin.")
        self.status_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        if not self._embed_mode:
            layout.addWidget(self.status_label)

        self.ip_before_label = QLabel("IP without proxy: ---")
        self.ip_after_label = QLabel("IP via proxy: ---")
        for il in (self.ip_before_label, self.ip_after_label):
            il.setAlignment(Qt.AlignmentFlag.AlignCenter)
            il.setStyleSheet("font-size: 13px; color: rgba(255,255,255,0.75);")
            if not self._embed_mode:
                layout.addWidget(il)

        self.progress_bar = QProgressBar()
        self.progress_bar.setRange(0, 100)
        layout.addWidget(self.progress_bar)

        buttons_layout = QHBoxLayout()
        layout.addLayout(buttons_layout)

        self.cancel_button = QPushButton("Cancel Test")
        self.cancel_button.setEnabled(False)
        self.cancel_button.clicked.connect(self._handle_cancel)
        buttons_layout.addWidget(self.cancel_button)

        self.download_label = QLabel("Download speed: --- MB/s")
        self.upload_label = QLabel("Upload speed: --- MB/s")
        self.latency_label = QLabel("Ping: --- ms")
        self.server_label = QLabel("Selected server: ---")

        for label in (
            self.download_label,
            self.upload_label,
            self.latency_label,
            self.server_label,
        ):
            label.setAlignment(Qt.AlignmentFlag.AlignCenter)
            label.setStyleSheet("font-size: 14px;")
            layout.addWidget(label)

        if self._embed_mode:
            for w in (self.progress_bar, self.download_label, self.upload_label, self.latency_label, self.server_label, self.ip_before_label, self.ip_after_label, self.status_label):
                try:
                    w.setVisible(False)
                except Exception:
                    pass

    def _build_settings_dialog(self) -> None:
        self.settings_dialog = QDialog(self)
        self.settings_dialog.setWindowTitle("Settings")
        self.settings_dialog.setModal(False)

        dlg_layout = QVBoxLayout()
        self.settings_dialog.setLayout(dlg_layout)

        # ---- Proxy Settings ----
        proxy_group = QGroupBox("Proxy Settings")
        proxy_layout = QVBoxLayout()
        proxy_group.setLayout(proxy_layout)

        proxy_row = QHBoxLayout()
        lbl_sock = QLabel("Socket Timeout (ms):")
        self.spin_socket_timeout_ms = QSpinBox()
        self.spin_socket_timeout_ms.setRange(100, 60000)
        self.spin_socket_timeout_ms.setSingleStep(100)
        self.spin_socket_timeout_ms.setValue(1000)

        lbl_deadline = QLabel("Proxy Ready Deadline (sec):")
        self.spin_proxy_deadline_sec = QSpinBox()
        self.spin_proxy_deadline_sec.setRange(1, 60)
        self.spin_proxy_deadline_sec.setValue(5)

        proxy_row.addWidget(lbl_sock)
        proxy_row.addWidget(self.spin_socket_timeout_ms)
        proxy_row.addSpacing(20)
        proxy_row.addWidget(lbl_deadline)
        proxy_row.addWidget(self.spin_proxy_deadline_sec)
        proxy_row.addStretch(1)
        proxy_layout.addLayout(proxy_row)
        dlg_layout.addWidget(proxy_group)

        # ---- Speed Test Settings ----
        settings_group = QGroupBox("Speed Test Settings")
        settings_layout = QVBoxLayout()
        settings_group.setLayout(settings_layout)

        sizes_row = QHBoxLayout()
        lbl_dl_size = QLabel("Download size (MB):")
        self.combo_dl_size = QComboBox()
        for mb in (1, 5, 10, 50):
            self.combo_dl_size.addItem(str(mb), mb)
        self.combo_dl_size.setCurrentIndex(2)  # 10 MB default

        lbl_ul_size = QLabel("Upload size (MB):")
        self.combo_ul_size = QComboBox()
        for mb in (1, 5, 10, 50):
            self.combo_ul_size.addItem(str(mb), mb)
        self.combo_ul_size.setCurrentIndex(1)  # 5 MB default

        sizes_row.addWidget(lbl_dl_size)
        sizes_row.addWidget(self.combo_dl_size)
        sizes_row.addSpacing(20)
        sizes_row.addWidget(lbl_ul_size)
        sizes_row.addWidget(self.combo_ul_size)
        sizes_row.addStretch(1)
        settings_layout.addLayout(sizes_row)

        mode_row = QHBoxLayout()
        lbl_mode = QLabel("Test mode:")
        self.combo_test_mode = QComboBox()
        self.combo_test_mode.addItem("Ping Only", "ping_only")
        self.combo_test_mode.addItem("Download Only", "download")
        self.combo_test_mode.addItem("Upload Only", "upload")
        self.combo_test_mode.addItem("Download & Upload", "both")
        self.combo_test_mode.setCurrentIndex(1)  # default: Download Only
        mode_row.addWidget(lbl_mode)
        mode_row.addWidget(self.combo_test_mode)
        mode_row.addStretch(1)
        settings_layout.addLayout(mode_row)

        timeouts_row = QHBoxLayout()
        lbl_dl_conn = QLabel("DL connect timeout (s):")
        self.spin_dl_connect = QSpinBox()
        self.spin_dl_connect.setRange(1, 120)
        self.spin_dl_connect.setValue(10)

        lbl_dl_read = QLabel("DL read timeout (s):")
        self.spin_dl_read = QSpinBox()
        self.spin_dl_read.setRange(1, 300)
        self.spin_dl_read.setValue(30)

        lbl_ul_conn = QLabel("UL connect timeout (s):")
        self.spin_ul_connect = QSpinBox()
        self.spin_ul_connect.setRange(1, 120)
        self.spin_ul_connect.setValue(10)

        lbl_ul_read = QLabel("UL read timeout (s):")
        self.spin_ul_read = QSpinBox()
        self.spin_ul_read.setRange(1, 300)
        self.spin_ul_read.setValue(30)

        timeouts_row.addWidget(lbl_dl_conn)
        timeouts_row.addWidget(self.spin_dl_connect)
        timeouts_row.addSpacing(12)
        timeouts_row.addWidget(lbl_dl_read)
        timeouts_row.addWidget(self.spin_dl_read)
        timeouts_row.addSpacing(12)
        timeouts_row.addWidget(lbl_ul_conn)
        timeouts_row.addWidget(self.spin_ul_connect)
        timeouts_row.addSpacing(12)
        timeouts_row.addWidget(lbl_ul_read)
        timeouts_row.addWidget(self.spin_ul_read)
        timeouts_row.addStretch(1)
        settings_layout.addLayout(timeouts_row)

        settings_note = QLabel("Larger sizes improve accuracy but take longer. Timeouts apply to the HTTP requests used for CacheFly / HTTPBin tests.")
        settings_note.setWordWrap(True)
        settings_note.setStyleSheet("color: #666;")
        settings_layout.addWidget(settings_note)

        dlg_layout.addWidget(settings_group)

        # ---- Endpoints ----
        endpoints_group = QGroupBox("Endpoints")
        endpoints_layout = QVBoxLayout()
        endpoints_group.setLayout(endpoints_layout)

        ping_row = QHBoxLayout()
        lbl_ping = QLabel("Ping URL:")
        self.edit_ping_url = QLineEdit()
        self.edit_ping_url.setText(LATENCY_URL)
        ping_row.addWidget(lbl_ping)
        ping_row.addWidget(self.edit_ping_url)
        endpoints_layout.addLayout(ping_row)

        dl_row = QHBoxLayout()
        lbl_dl_url = QLabel("Download URL:")
        self.edit_download_url = QLineEdit()
        self.edit_download_url.setText("https://cachefly.cachefly.net/50mb.test")
        dl_row.addWidget(lbl_dl_url)
        dl_row.addWidget(self.edit_download_url)
        endpoints_layout.addLayout(dl_row)

        self.chk_dl_time_limit = QCheckBox("Limit download test window")
        self.chk_dl_time_limit.setChecked(True)
        dl_time_row = QHBoxLayout()
        dl_time_row.addWidget(self.chk_dl_time_limit)
        dl_time_row.addWidget(QLabel("Seconds:"))
        self.spin_dl_time_seconds = QSpinBox()
        self.spin_dl_time_seconds.setRange(1, 60)
        self.spin_dl_time_seconds.setValue(5)
        dl_time_row.addWidget(self.spin_dl_time_seconds)
        dl_time_row.addStretch(1)
        endpoints_layout.addLayout(dl_time_row)

        ul_row = QHBoxLayout()
        lbl_ul_url = QLabel("Upload URL:")
        self.edit_upload_url = QLineEdit()
        self.edit_upload_url.setText(HTTPBIN_UPLOAD_URL)
        ul_row.addWidget(lbl_ul_url)
        ul_row.addWidget(self.edit_upload_url)
        endpoints_layout.addLayout(ul_row)

        endpoints_note = QLabel("Tip: use {size} in the download URL to inject the selected MB size.")
        endpoints_note.setWordWrap(True)
        endpoints_note.setStyleSheet("color: #666;")
        endpoints_layout.addWidget(endpoints_note)

        dlg_layout.addWidget(endpoints_group)

        # ---- Dialog controls ----
        controls_row = QHBoxLayout()
        controls_row.addStretch(1)
        btn_close = QPushButton("Close")
        btn_close.clicked.connect(self.settings_dialog.close)
        controls_row.addWidget(btn_close)
        dlg_layout.addLayout(controls_row)

        self.settings_dialog.finished.connect(lambda _: self._refresh_settings_summary())
        self._refresh_settings_summary()

    def _open_settings_dialog(self) -> None:
        if self.settings_dialog.isVisible():
            self.settings_dialog.raise_()
            self.settings_dialog.activateWindow()
            return
        self.settings_dialog.show()

    def _refresh_settings_summary(self) -> None:
        try:
            dl_mb = int(self.combo_dl_size.currentData())
            ul_mb = int(self.combo_ul_size.currentData())
            mode_text = self.combo_test_mode.currentText()
            self.settings_summary_label.setText(f"Settings: DL {dl_mb}MB, UL {ul_mb}MB, {mode_text}")
        except Exception:
            self.settings_summary_label.setText("Settings: custom")

    def _on_sort_ping_changed(self) -> None:
        try:
            if self.chk_sort_ping.isChecked():
                self.results_table.setSortingEnabled(True)
                self.results_proxy.sort(3, Qt.SortOrder.AscendingOrder)
                self.results_table.horizontalHeader().setSortIndicatorShown(True)
                self.results_table.horizontalHeader().setSortIndicator(3, Qt.SortOrder.AscendingOrder)
            else:
                self.results_table.setSortingEnabled(False)
                self.results_proxy.sort(-1)
                self.results_table.horizontalHeader().setSortIndicatorShown(False)
        except Exception:
            pass

    # ---- public APIs for embedded mode ----
    def set_global_config_text(self, text: str, label: str = "") -> None:
        self._global_config_text = text
        self._config_text = text
        if label:
            self.config_status_label.setText(f"Global config: {label}")
        else:
            self.config_status_label.setText("Global config loaded")

    def set_provider_config_text(self, provider: str, text: str, label: str = "") -> None:
        self._provider_configs[provider] = text
        if label:
            self.config_status_label.setText(f"Config for {provider}: {label}")

    def set_use_per_provider_json(self, enabled: bool) -> None:
        self._use_per_provider_json = bool(enabled)

    def set_provider_icons(self, mapping: Dict[str, QIcon]) -> None:
        self._provider_icons = dict(mapping or {})
        try:
            self.results_model.set_provider_icons(self._provider_icons)
        except Exception:
            pass


    def set_providers(self, providers: Dict[str, dict]) -> None:
        """Provide ip.json providers mapping to the embedded Speed Test tab.

        Used for accurate provider detection (by CIDR ranges) and icon fallback.
        """
        self._providers = dict(providers or {})
        # build a cached list of IPv4Network per provider for fast membership tests
        nets: Dict[str, List[ipaddress.IPv4Network]] = {}
        for prov, meta in self._providers.items():
            cidrs = meta.get("ipv4", [])
            if not isinstance(cidrs, list):
                continue
            nn: List[ipaddress.IPv4Network] = []
            for c in cidrs:
                try:
                    if isinstance(c, str) and "/" in c:
                        nn.append(ipaddress.IPv4Network(c.strip(), strict=False))
                except Exception:
                    continue
            nets[prov] = nn
        self._provider_networks = nets
        try:
            self.results_model.set_providers(self._providers)
        except Exception:
            pass

    def detect_provider_for_ip(self, ip: str) -> str:
        ip = (ip or "").strip()
        try:
            ip_obj = ipaddress.IPv4Address(ip)
        except Exception:
            return ""

        best_provider = ""
        best_prefix = -1

        # Use stable provider ordering and prefer the most specific (largest prefix) match.
        for prov in sorted((self._provider_networks or {}).keys()):
            for net in self._provider_networks.get(prov, []):
                try:
                    if ip_obj in net:
                        if net.prefixlen > best_prefix:
                            best_prefix = net.prefixlen
                            best_provider = prov
                except Exception:
                    continue
        return best_provider


    def load_ip_items(self, items: List[Tuple[str, str]]) -> None:
        # items: list of (provider, ip)
        fixed: List[Tuple[str, str]] = []
        for prov, ip in (items or []):
            p = (prov or '').strip()
            addr = (ip or '').strip()
            if not p or (self._providers and p not in self._providers):
                dp = self.detect_provider_for_ip(addr)
                if dp:
                    p = dp
            fixed.append((p, addr))
        self._batch_ips = list(fixed)
        try:
            # keep provider icons
            # the model uses icon_for_provider; we can pass a pseudo-providers dict by storing icons separately if needed
            self.results_model.set_items(self._batch_ips)
        except Exception:
            pass

        self.ip_count_label.setText(f"Loaded items: {len(self._batch_ips)}")

        # keep insertion order by clearing any active sort
        try:
            self.results_proxy.sort(-1)
            self.results_table.horizontalHeader().setSortIndicatorShown(False)
        except Exception:
            pass
        self.batch_progress_label.setText(f"Batch progress: 0/{len(items)}")
        self.success_count_label.setText("Success count: 0")


    def _load_from_json_file(self) -> None:
        file_path, _ = QFileDialog.getOpenFileName(self, "Select JSON File", "", "JSON Files (*.json);;All Files (*)")
        if not file_path:
            return
        try:
            with open(file_path, "r", encoding="utf-8") as f:
                text = f.read()
            json.loads(text)
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Failed to load/validate JSON:\n{e}")
            return
        self._config_text = text
        self.config_status_label.setText(f"Config: loaded from {Path(file_path).name}")

    def _load_json_from_clipboard(self) -> None:
        text = QGuiApplication.clipboard().text()
        if not text or not text.strip():
            QMessageBox.warning(self, "Warning", "Clipboard is empty.")
            return
        try:
            json.loads(text)
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Clipboard does not contain valid JSON:\n{e}")
            return
        self._config_text = text
        self.config_status_label.setText("Config: loaded from clipboard")

    def _load_ip_list_file(self) -> None:
        file_path, _ = QFileDialog.getOpenFileName(self, "Select IP/Address List (TXT)", "", "Text Files (*.txt);;All Files (*)")
        if not file_path:
            return
        try:
            with open(file_path, "r", encoding="utf-8") as f:
                lines = f.read().splitlines()
            cleaned = [ln.strip() for ln in lines if ln.strip()]
            if not cleaned:
                QMessageBox.warning(self, "Warning", "Selected file is empty.")
                return

            self._populate_table_from_ip_list(cleaned)
            self.ip_count_label.setText(f"Loaded items: {len(cleaned)}")
            self.batch_progress_label.setText(f"Batch progress: -/{len(cleaned)}")
            self.success_count_label.setText("Success count: 0")
            self.status_label.setText("IP list loaded.")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Failed to read file:\n{e}")

    def _populate_table_from_ip_list(self, items: List[str]) -> None:
        # Standalone fallback: no provider info
        tuples = [("", addr) for addr in (items or [])]
        self._batch_ips = tuples
        try:
            self.results_model.set_items(tuples)
        except Exception:
            pass

    # -------- Context menu (single test & copy IP) --------
    def _table_context_menu(self, pos: QPoint) -> None:
        index = self.results_table.indexAt(pos)
        if not index.isValid():
            return
        row = index.row()
        item = self.results_model.get_item(self.results_proxy.mapToSource(index).row()) if hasattr(self, "results_proxy") else self.results_model.get_item(row)
        address = str(item.get("address","")).strip()
        if not address:
            return

        menu = QMenu(self)
        act_run = QAction("Run Single Test", self)
        act_copy = QAction("Copy IP", self)

        act_run.triggered.connect(lambda: self._start_single_from_row(row))
        act_copy.triggered.connect(lambda: self._copy_ip_from_row(row))

        # Disable run while any test running
        if self.worker is not None and self.worker.isRunning():
            act_run.setEnabled(False)

        menu.addAction(act_run)
        menu.addAction(act_copy)
        menu.exec(self.results_table.viewport().mapToGlobal(pos))

    def _copy_ip_from_row(self, row: int) -> None:
        try:
            src_row = self.results_proxy.mapToSource(self.results_proxy.index(row, 0)).row() if hasattr(self, "results_proxy") else row
            item = self.results_model.get_item(src_row)
            ip = str(item.get("address","")).strip()
            if ip:
                QGuiApplication.clipboard().setText(ip)
                self.status_label.setText(f"Copied IP: {ip}")
        except Exception:
            pass

    def _start_single_from_row(self, row: int) -> None:
        if self.worker is not None and self.worker.isRunning():
            return
        try:
            src_row = self.results_proxy.mapToSource(self.results_proxy.index(row, 0)).row() if hasattr(self, "results_proxy") else row
            item = self.results_model.get_item(src_row)
            address = str(item.get("address","")).strip()
            provider = str(item.get("provider","")).strip()
        except Exception:
            address = ""
            provider = ""
        if not address:
            QMessageBox.warning(self, "Warning", "Selected row has no address.")
            return

        cfg = self._select_config_for_provider(provider)
        if not cfg:
            QMessageBox.warning(self, "Warning", "No JSON config available (global or per-provider).")
            return
        self._config_text = cfg

        self._reset_ui_single()
        self.status_label.setText(f"Starting single test for: {address}")
        self.progress_bar.setValue(0)
        self.cancel_button.setEnabled(True)
        self.batch_start_button.setEnabled(False)
        self.btn_clear_batch_list.setEnabled(False)
        if getattr(self, "btn_remove_failed_batch", None):
            self.btn_remove_failed_batch.setEnabled(False)
        self.results_table.setSortingEnabled(False)

        self._single_context_row = src_row
        self._set_table_status(src_row, "Running ...")

        self._cleanup_worker()

        self._cleanup_worker()

        self.worker = SpeedTestWorker(
            use_proxy=True,
            xray_config_json=self._config_text,
            xray_path=self._xray_path,
            use_random_port=True,
            proxy_socket_timeout_ms=self.spin_socket_timeout_ms.value(),
            proxy_ready_deadline_sec=self.spin_proxy_deadline_sec.value(),
            address_override=address,
            dl_size_mb=int(self.combo_dl_size.currentData()),
            ul_size_mb=int(self.combo_ul_size.currentData()),
            latency_attempts=5,
            dl_connect_timeout=self.spin_dl_connect.value(),
            dl_read_timeout=self.spin_dl_read.value(),
            ul_connect_timeout=self.spin_ul_connect.value(),
            ul_read_timeout=self.spin_ul_read.value(),
            download_url=self.edit_download_url.text().strip(),
            upload_url=self.edit_upload_url.text().strip(),
            ping_url=self.edit_ping_url.text().strip(),
            dl_time_limit_enabled=bool(self.chk_dl_time_limit.isChecked()),
            dl_time_limit_seconds=float(self.spin_dl_time_seconds.value()),
            test_mode=str(self.combo_test_mode.currentData()),
        )
        self._connect_worker_signals(single_mode=True, use_table_row=row)
        self.worker.start()

    # -------- Batch test --------
    def _handle_batch_start(self) -> None:
        if self.worker is not None and self.worker.isRunning():
            return
        self._cleanup_worker()
        if not self._batch_ips:
            # standalone fallback: read from table
            items: List[Tuple[str, str]] = []
            for r in range(self.results_model.rowCount()):
                item = self.results_model.get_item(r)
                prov = str(item.get("provider","")).strip()
                addr = str(item.get("address","")).strip()
                if addr:
                    items.append((prov, addr))
            if not items:
                QMessageBox.warning(self, "Warning", "No IP/address items in the table.")
                return
            self._batch_ips = items

        total = len(self._batch_ips)
        self._batch_current_row = -1
        self._batch_mode = True
        self._batch_abort = False
        self._batch_success_count = 0

        self.ip_count_label.setText(f"Loaded items: {total}")
        self.batch_progress_label.setText(f"Batch progress: 0/{total}")
        self.success_count_label.setText("Success count: 0")

        self._reset_ui_single()
        self.status_label.setText("Starting batch test ...")
        self.progress_bar.setValue(0)
        self.cancel_button.setEnabled(True)
        self.batch_start_button.setEnabled(False)
        self.btn_clear_batch_list.setEnabled(False)
        self.results_table.setSortingEnabled(False)
        # Bulk reset for large tables (no per-row UI updates)
        self.results_model.reset_for_batch()
        self._refresh_success_count()
        try:
            if getattr(self, "chk_sort_ping", None) and self.chk_sort_ping.isChecked():
                self.results_table.setSortingEnabled(True)
                self.results_proxy.sort(3, Qt.SortOrder.AscendingOrder)
        except Exception:
            pass
        try:
            self.results_table.scrollToTop()
        except Exception:
            pass

        QTimer.singleShot(0, self._start_next_batch_item)

    def _clear_batch_list(self) -> None:
        """
        Clear Speed Test batch list safely (no UI freeze).
        If a batch is running, abort it and cleanup worker first.
        """
        # While a test is running, Clear is disabled; guard anyway.
        if self.worker is not None and self.worker.isRunning():
            return

        # Abort running batch/worker safely
        self._batch_abort = True
        self._batch_mode = False
        try:
            self._cleanup_worker()
        except Exception:
            pass

        self._batch_ips = []
        self._batch_current_row = -1
        self._batch_success_count = 0

        # Clear model rows (fast reset)
        self.results_model.set_items([])

        # Reset UI counters/labels
        try:
            self.ip_count_label.setText("Loaded items: 0")
        except Exception:
            pass
        try:
            self.batch_progress_label.setText("Batch progress: 0/0")
        except Exception:
            pass
        try:
            self.success_count_label.setText("Success count: 0")
        except Exception:
            pass
        if getattr(self, "btn_remove_failed_batch", None):
            self.btn_remove_failed_batch.setEnabled(True)

    def _start_next_batch_item(self) -> None:
        if self._batch_abort:
            self._finish_batch()
            return
        self._batch_current_row += 1
        if self._batch_current_row >= len(self._batch_ips):
            self._finish_batch()
            return

        provider, address = self._batch_ips[self._batch_current_row]
        cfg = self._select_config_for_provider(provider)
        if not cfg:
            self._set_table_status(self._batch_current_row, "No config")
            self._start_next_batch_item()
            return
        self._config_text = cfg

        self._set_table_status(self._batch_current_row, "Running ...")
        self.batch_progress_label.setText(f"Batch progress: {self._batch_current_row + 1}/{len(self._batch_ips)}")

        self.worker = SpeedTestWorker(
            use_proxy=True,
            xray_config_json=self._config_text,
            xray_path=self._xray_path,
            use_random_port=True,
            proxy_socket_timeout_ms=self.spin_socket_timeout_ms.value(),
            proxy_ready_deadline_sec=self.spin_proxy_deadline_sec.value(),
            address_override=address,
            dl_size_mb=int(self.combo_dl_size.currentData()),
            ul_size_mb=int(self.combo_ul_size.currentData()),
            latency_attempts=5,
            dl_connect_timeout=self.spin_dl_connect.value(),
            dl_read_timeout=self.spin_dl_read.value(),
            ul_connect_timeout=self.spin_ul_connect.value(),
            ul_read_timeout=self.spin_ul_read.value(),
            download_url=self.edit_download_url.text().strip(),
            upload_url=self.edit_upload_url.text().strip(),
            ping_url=self.edit_ping_url.text().strip(),
            dl_time_limit_enabled=bool(self.chk_dl_time_limit.isChecked()),
            dl_time_limit_seconds=float(self.spin_dl_time_seconds.value()),
            test_mode=str(self.combo_test_mode.currentData()),
        )
        self._connect_worker_signals(single_mode=False, use_table_row=self._batch_current_row)
        self.worker.start()

    def _finish_batch(self) -> None:
        self._cleanup_worker()
        self._batch_mode = False
        self._batch_abort = False
        total = len(self._batch_ips)
        self._batch_ips = []
        self._batch_current_row = -1
        self.status_label.setText("Batch test finished.")
        self.batch_progress_label.setText(f"Batch progress: {total}/{total}" if total > 0 else "Batch progress: -/-")
        self.cancel_button.setEnabled(False)
        self.batch_start_button.setEnabled(True)
        self.btn_clear_batch_list.setEnabled(True)
        if getattr(self, "btn_remove_failed_batch", None):
            self.btn_remove_failed_batch.setEnabled(True)
        self.results_table.setSortingEnabled(True)

    
    def _cleanup_worker(self) -> None:
        """Disconnect and delete the current worker (safe between batch items)."""
        w = self.worker
        if w is None:
            return
        try:
            # disconnect all signals from this worker
            for sig_name in ("status_update", "progress_update", "throughput_update", "result_ready", "error_occurred", "finished", "ip_update"):
                try:
                    getattr(w, sig_name).disconnect()
                except Exception:
                    pass
        except Exception:
            pass
        try:
            if w.isRunning():
                # request cancel and let it stop in background; we avoid blocking UI here
                w.request_cancel()
        except Exception:
            pass
        try:
            w.deleteLater()
        except Exception:
            pass
        self.worker = None

# -------- Common helpers --------
    def _set_table_status(self, row: int, text: str) -> None:
        try:
            self.results_model.set_status(row, text)
        except Exception:
            pass
        self._refresh_success_count()

    def _set_table_proxy_ip(self, row: int, proxy_ip: str) -> None:
        try:
            self.results_model.set_proxy_ip(row, proxy_ip)
        except Exception:
            pass
        # Try to fill country if empty
        try:
            item = self.results_model.get_item(row)
            cur_country = str(item.get("country", "")).strip()
            if (not cur_country or cur_country in ("---", "Unknown")) and proxy_ip not in ("---", "Unknown", ""):
                cname, flag = get_country_info(proxy_ip)
                if cname:
                    self.results_model.set_country(row, f"{flag} {cname}".strip())
        except Exception:
            pass

    def _set_table_results(self, row: int, results: dict) -> None:
        try:
            self.results_model.set_results(row, results)
        except Exception:
            pass
        self._refresh_success_count()

    def _select_config_for_provider(self, provider: str) -> Optional[str]:
        provider = (provider or "").strip()

        # Per-provider mode: ONLY use that provider's JSON (no fallback).
        if self._use_per_provider_json:
            if provider and provider in self._provider_configs:
                return self._provider_configs[provider]
            return None

        # Global mode (default): use the explicitly loaded global JSON if present,
        # otherwise fall back to the current config text (standalone mode).
        if self._global_config_text:
            return self._global_config_text
        return self._config_text or None

    # -------- Worker signal handlers --------
    def _connect_worker_signals(self, single_mode: bool, use_table_row: Optional[int] = None) -> None:
        # Clean old connections
        for sig_name in ("status_update", "progress_update", "throughput_update", "result_ready", "error_occurred", "finished", "ip_update"):
            try:
                if self.worker:
                    getattr(self.worker, sig_name).disconnect()
            except Exception:
                pass

        self.worker.status_update.connect(self.status_label.setText)
        self.worker.progress_update.connect(self.progress_bar.setValue)
        self.worker.throughput_update.connect(self._update_realtime_speed)

        # Always update IP labels
        self.worker.ip_update.connect(self._update_ip_labels)

        if use_table_row is not None:
            # Update table row in both modes
            self.worker.result_ready.connect(lambda results, r=use_table_row: self._set_table_results(r, results))
            # Error handler: only mark status as 'fail' in the table
            self.worker.error_occurred.connect(lambda message, r=use_table_row: self._on_table_row_error(r, message))
            # Also update Proxy IP in the table when proxy IP is available
            self.worker.ip_update.connect(lambda stage, ip, r=use_table_row: self._set_table_proxy_ip(r, ip) if stage == "after_proxy" else None)

        if single_mode:
            # Also update the top summary labels
            self.worker.result_ready.connect(self._display_results)
            self.worker.finished.connect(self._on_finished_single)
        else:
            self.worker.result_ready.connect(self._on_batch_result_ready)
            self.worker.finished.connect(self._on_batch_finished_one)

    def _handle_cancel(self) -> None:
        if self.worker and self.worker.isRunning():
            self.worker.request_cancel()
            self.status_label.setText("Cancelling test ... (please wait)")
            self.cancel_button.setEnabled(False)
            if self._batch_mode:
                self._batch_abort = True

    # -------- Single test slots --------
    def _update_realtime_speed(self, stage: str, speed_MBps: float) -> None:
        # In embed mode, show live speeds directly inside the table to keep UI compact.
        if self._embed_mode:
            row = self._batch_current_row if self._batch_mode else self._single_context_row
            if row is None or row < 0:
                return
            try:
                if stage == "ping":
                    self.results_model._set_row_value(row, "ping", _fmt_ping_ms(speed_MBps) if speed_MBps > 0 else "-1", 3)
                    self._set_table_status(row, "Success" if speed_MBps > 0 else "Fail")
                elif stage == "download":
                    if speed_MBps < 0:
                        self.results_model._set_row_value(row, "download", "0", 6)
                    else:
                        self.results_model._set_row_value(row, "download", f"{speed_MBps:.2f}", 6)
                elif stage == "upload":
                    if speed_MBps < 0:
                        self.results_model._set_row_value(row, "upload", "0", 7)
                    else:
                        self.results_model._set_row_value(row, "upload", f"{speed_MBps:.2f}", 7)
            except Exception:
                pass
            return

        # Non-embedded mode keeps the dedicated labels.
        if stage == "download":
            self.download_label.setText(f"Download speed: {speed_MBps:.2f} MB/s")
        elif stage == "upload":
            self.upload_label.setText(f"Upload speed: {speed_MBps:.2f} MB/s")
        elif stage == "ping":
            try:
                self.latency_label.setText(f"Ping: {speed_MBps:.2f} ms" if speed_MBps > 0 else "Ping: -")
            except Exception:
                pass

    def _update_ip_labels(self, stage: str, ip: str) -> None:
        if self._embed_mode:
            # Only the proxy IP is useful in embedded view; write it into the table.
            if stage == "after_proxy":
                row = self._batch_current_row if self._batch_mode else self._single_context_row
                if row is not None and row >= 0:
                    self._set_table_proxy_ip(row, ip)
            return

        if stage == "before_proxy":
            self.ip_before_label.setText(f"IP without proxy: {ip}")
        elif stage == "after_proxy":
            self.ip_after_label.setText(f"IP via proxy: {ip}")

    def _display_results(self, results: dict) -> None:
        ping = results.get("ping_ms", results.get("latency_ms", -1))
        dl = results.get("download_MBps", -1)
        ul = results.get("upload_MBps", -1)

        # Ping
        self.latency_label.setText(f"Ping: {ping:.2f} ms" if isinstance(ping, (int, float)) else "Ping: --- ms")

        if not isinstance(ping, (int, float)) or ping <= 0:
            self.download_label.setText("Download speed: -")
            self.upload_label.setText("Upload speed: -")
            self.server_label.setText("Selected server: -")
            self.status_label.setText("Status: Fail (ping failed)")
            return

        self.download_label.setText(
            "Download speed: -"
            if not isinstance(dl, (int, float)) or dl <= 0
            else f"Download speed: {dl:.2f} MB/s"
        )
        self.upload_label.setText(
            "Upload speed: -"
            if not isinstance(ul, (int, float)) or ul <= 0
            else f"Upload speed: {ul:.2f} MB/s"
        )

        sponsor = results.get("server_sponsor", "")
        name = results.get("server_name", "")
        host = results.get("server_host", "")
        country = results.get("server_country", "")
        self.server_label.setText(f"Selected server: {sponsor} - {name} ({country}) | {host}".strip())
        self.status_label.setText("Status: Success")

    def _on_table_row_error(self, row: int, message: str) -> None:
        # On any error, write 'fail' in Status column; keep a short reason as tooltip.
        self._set_table_status(row, "Fail")
        try:
            first = (message or "").splitlines()[0].strip()
            if first:
                self.results_model.set_status_detail(row, first[:160])
                # also show a short message in the main status label (helps debugging)
                self.status_label.setText(first[:200])
        except Exception:
            pass
        self.progress_bar.setValue(0)

    def _on_finished_single(self) -> None:
        self.cancel_button.setEnabled(False)
        self.batch_start_button.setEnabled(True)
        self.btn_clear_batch_list.setEnabled(True)
        self.results_table.setSortingEnabled(True)
        self._single_context_row = -1
        self._cleanup_worker()

    def _reset_ui_single(self) -> None:
        self.download_label.setText("Download speed: --- MB/s")
        self.upload_label.setText("Upload speed: --- MB/s")
        self.latency_label.setText("Ping: --- ms")
        self.server_label.setText("Selected server: ---")
        self.ip_before_label.setText("IP without proxy: ---")
        self.ip_after_label.setText("IP via proxy: ---")

    # -------- Batch slots --------
    def _on_batch_result_ready(self, results: dict) -> None:
        if self._batch_mode and 0 <= self._batch_current_row < self.results_model.rowCount():
            # Table row updated via lambda connection
            self._refresh_success_count()

    def _on_batch_finished_one(self) -> None:
        # Guard: ignore stale finished signals from old workers
        sender = self.sender()
        if sender is not None and sender is not self.worker:
            try:
                sender.deleteLater()
            except Exception:
                pass
            return

        self._cleanup_worker()

        if self._batch_abort:
            self._finish_batch()
            return
        self._start_next_batch_item()

    def _remove_failed_batch(self) -> None:
        if self.worker is not None and self.worker.isRunning():
            QMessageBox.warning(self, "Busy", "Please stop the batch test first.")
            return
        rows: List[Tuple[str, str]] = []
        for r in range(self.results_model.rowCount()):
            item = self.results_model.get_item(r)
            status = str(item.get("status", "")).strip().lower()
            if status != "fail":
                rows.append((str(item.get("provider", "")), str(item.get("address", ""))))
        self._batch_ips = list(rows)
        self.results_model.set_items(self._batch_ips)
        self.ip_count_label.setText(f"Loaded items: {len(self._batch_ips)}")
        self.batch_progress_label.setText(f"Batch progress: 0/{len(self._batch_ips)}")
        self._batch_success_count = 0
        self.success_count_label.setText("Success count: 0")

    def _refresh_success_count(self) -> None:
        try:
            count = 0
            for row in self.results_model._rows:
                if str(row.get("status", "")).strip().lower() == "success":
                    count += 1
            self._batch_success_count = count
            self.success_count_label.setText(f"Success count: {self._batch_success_count}")
        except Exception:
            pass

    # NEW: Save Success IPs to TXT (only raw IPs/addresses)
    def _show_save_success_menu(self) -> None:
        grouped = self._success_ips_grouped()
        total = sum(len(v) for v in grouped.values())
        if total == 0:
            QMessageBox.information(self, "Info", "No successful IPs to save.")
            return

        menu = QMenu(self)
        act_all = menu.addAction("Save Success (All)")
        act_all.triggered.connect(self._save_success_all)

        act_all_with_provider = menu.addAction("Save All Success (Provider + IP)")
        act_all_with_provider.triggered.connect(self._save_success_all_with_provider)

        menu.addSeparator()
        for prov in sorted(grouped.keys()):
            act = menu.addAction(f"Save Success ({prov})")
            act.triggered.connect(lambda _=False, p=prov: self._save_success_by_provider(p))

        menu.exec(self.btn_save_success_ips.mapToGlobal(self.btn_save_success_ips.rect().bottomLeft()))

    def _success_ips_grouped(self) -> Dict[str, List[str]]:
        grouped: Dict[str, List[str]] = {}
        for r in range(self.results_model.rowCount()):
            item = self.results_model.get_item(r)
            status_text = str(item.get("status", "")).strip().lower()
            if status_text != "success":
                continue
            addr = str(item.get("address", "")).strip()
            prov = str(item.get("provider", "")).strip()
            if addr:
                grouped.setdefault(prov, []).append(addr)
        return grouped

    def _save_txt_list(self, items: List[str], default_name: str) -> None:
        save_path, _ = QFileDialog.getSaveFileName(self, "Save Success IPs", default_name, "Text Files (*.txt);;All Files (*)")
        if not save_path:
            return
        try:
            with open(save_path, "w", encoding="utf-8") as f:
                f.write("\n".join(items))
            QMessageBox.information(self, "Saved", f"Saved {len(items)} item(s) to:\n{save_path}")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Failed to save file:\n{e}")

    def _save_success_all(self) -> None:
        grouped = self._success_ips_grouped()
        ips: List[str] = []
        for prov in sorted(grouped.keys()):
            ips.extend(grouped[prov])
        self._save_txt_list(ips, "success_ips_all.txt")

    def _save_success_all_with_provider(self) -> None:
        grouped = self._success_ips_grouped()
        rows: List[str] = []
        for prov in sorted(grouped.keys()):
            for ip in grouped[prov]:
                rows.append(f"{prov}\t{ip}".strip())
        self._save_txt_list(rows, "success_ips_with_provider.txt")

    def _save_success_by_provider(self, provider: str) -> None:
        grouped = self._success_ips_grouped()
        ips = grouped.get(provider, [])
        if not ips:
            QMessageBox.information(self, "Info", f"No successful IPs for {provider}.")
            return
        safe = re.sub(r"[^a-zA-Z0-9_-]+", "_", provider or "provider")
        self._save_txt_list(ips, f"success_ips_{safe}.txt")

    # Update proxy IP in table when worker emits IP via proxy (unused legacy method)
    def _on_batch_ip_update(self, stage: str, ip: str) -> None:
        if stage == "after_proxy" and self._batch_mode and 0 <= self._batch_current_row < self.results_model.rowCount():
            self._set_table_proxy_ip(self._batch_current_row, ip)

# -------------------- IP Clean Scanner App (single-file) --------------------

#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
IP Clean Scanner By Farhad~UK (PyQt6)

- Reads providers + IPv4 CIDR ranges from ip.json next to the EXE (or .py)
- Shows provider icons from paths stored in ip.json (asset/icon/...)
- Update ip.json by fetching provider sources (IPv4 only; IPv6 ignored)

Tabs
1) Ranges
   - Choose providers + individual CIDR ranges (checkbox)
   - Shows total IP count per range + totals

2) Scan Range
   - Scans IPs in selected ranges (Sequential / Random / Shuffle unique)
   - Auto-switch range options (disabled in Shuffle)
   - Optional "Move on after first success in a range" (disabled in Shuffle)
   - Option to send working IPs automatically to "Scan IP" tab list

3) Scan IP
   - Load a TXT file and extract IPv4 addresses automatically
   - Auto-detect provider (based on loaded provider CIDR ranges)
   - Test each IP and show Status (SUCCESS / FAIL) + latency
   - Copy IP by clicking, export results (CSV/JSON)
"""


import ipaddress
import json
import random
import re
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterator, List, Optional, Tuple

import requests
from requests.exceptions import Timeout, RequestException

from PyQt6.QtCore import Qt, QThread, pyqtSignal
from PyQt6.QtGui import QColor, QFont, QIcon, QPalette
from PyQt6.QtWidgets import (
    QApplication,
    QCheckBox,
    QComboBox,
    QFileDialog,
    QFrame,
    QGridLayout,
    QGroupBox,
    QHBoxLayout,
    QLabel,
    QLineEdit,
    QMainWindow,
    QMessageBox,
    QPushButton,
    QScrollArea,
    QSplitter,
    QTabWidget,
    QTableView,
    QAbstractItemView,
    QVBoxLayout,
    QWidget,
)

# ------------------------- Config ---------------------------------------------

USER_AGENT = "Mozilla/5.0 (IP-Clean-Scanner-PyQt6)"
TRY_CHARS = ["", "|", "/", "-", "\\"]  # visual "spinner"
MAX_TRIES = len(TRY_CHARS)

_IPV4_CIDR_RE = re.compile(r"\b(?:\d{1,3}\.){3}\d{1,3}/\d{1,2}\b")
_IPV4_RE = re.compile(r"\b(?:\d{1,3}\.){3}\d{1,3}\b")


# ------------------------- Paths ----------------------------------------------

def app_root_dir() -> Path:
    """Folder next to the running app (EXE when frozen, .py when not)."""
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


def config_dir() -> Path:
    return app_root_dir() / "config"


def bin_dir() -> Path:
    return app_root_dir() / "bin"


def bundled_dir() -> Path:
    """PyInstaller onefile extraction dir (sys._MEIPASS) if present, else app_root_dir()."""
    if getattr(sys, "frozen", False) and hasattr(sys, "_MEIPASS"):
        return Path(sys._MEIPASS).resolve()
    return app_root_dir()


def ip_json_path() -> Path:
    return config_dir() / "ip.json"


def app_settings_path() -> Path:
    """Persistent UI/app settings stored next to the EXE/.py."""
    return config_dir() / "app_settings.json"


def load_app_icon() -> QIcon:
    """Loads app icon. Prefer bundled icon.ico (PyInstaller --add-data), else beside EXE."""
    for root in (bundled_dir(), app_root_dir()):
        for name in ('icon.ico', 'icon.icon'):
            p = root / name
            if p.exists():
                return QIcon(str(p))
        base = root / 'icon'
        for ext in ('.ico', '.png', '.svg', '.jpg', '.jpeg'):
            q = base.with_suffix(ext)
            if q.exists():
                return QIcon(str(q))
    return QIcon()


# ------------------------- IP helpers -----------------------------------------

def is_valid_ipv4(ip: str) -> bool:
    try:
        parts = ip.split(".")
        if len(parts) != 4:
            return False
        o = [int(p) for p in parts]
        return all(0 <= x <= 255 for x in o)
    except Exception:
        return False


def is_valid_ipv4_cidr(s: str) -> bool:
    try:
        ip, mask = s.split("/")
        if not is_valid_ipv4(ip):
            return False
        m = int(mask)
        return 0 <= m <= 32
    except Exception:
        return False


def extract_ipv4_cidrs(text: str) -> List[str]:
    found = []
    for m in _IPV4_CIDR_RE.findall(text or ""):
        if is_valid_ipv4_cidr(m):
            found.append(m)
    seen = set()
    out: List[str] = []
    for x in found:
        if x not in seen:
            seen.add(x)
            out.append(x)
    return out


def extract_ipv4s(text: str) -> List[str]:
    found = []
    for m in _IPV4_RE.findall(text or ""):
        if is_valid_ipv4(m):
            found.append(m)
    # unique preserve order
    seen = set()
    out: List[str] = []
    for x in found:
        if x not in seen:
            seen.add(x)
            out.append(x)
    return out


def ipv4_count(cidr: str) -> int:
    try:
        return int(ipaddress.IPv4Network(cidr, strict=False).num_addresses)
    except Exception:
        return 0


def fetch_user_ip_info() -> Tuple[str, str]:
    try:
        r = requests.get("https://freeipapi.com/api/json/", timeout=6, headers={"User-Agent": USER_AGENT})
        r.raise_for_status()
        data = r.json()
        ip = str(data.get("ipAddress", "") or "")
        ip_version = data.get("ipVersion", 4)
        if ip_version == 4:
            region = data.get("regionName", "")
            country = data.get("countryName", "")
            loc = ", ".join([p for p in (region, country) if p]).strip() or "Unknown"
        else:
            loc = "..."
        return ip, loc
    except Exception:
        return "0.0.0.0", "Unknown"


# ------------------------- ip.json helpers ------------------------------------

def load_ip_json() -> Dict[str, dict]:
    p = ip_json_path()
    p.parent.mkdir(parents=True, exist_ok=True)
    if not p.exists():
        sample = {
            "fastly": {
                "source": "https://api.fastly.com/public-ip-list",
                "icon": "asset/icon/fastly.icon",
                "ipv4": [],
            }
        }
        p.write_text(json.dumps(sample, ensure_ascii=False, indent=2), encoding="utf-8")
        return sample

    try:
        data = json.loads(p.read_text(encoding="utf-8"))
    except Exception:
        data = {}

    norm: Dict[str, dict] = {}
    if isinstance(data, dict):
        for k, v in data.items():
            if not isinstance(v, dict):
                continue
            src = str(v.get("source", "")).strip()
            icon = str(v.get("icon", "")).strip()
            ipv4_raw = v.get("ipv4", [])
            if not isinstance(ipv4_raw, list):
                ipv4_raw = []
            ipv4 = [s.strip() for s in ipv4_raw if isinstance(s, str) and is_valid_ipv4_cidr(s.strip())]
            norm[str(k)] = {"source": src, "icon": icon, "ipv4": ipv4}

    if not norm:
        norm = {
            "fastly": {
                "source": "https://api.fastly.com/public-ip-list",
                "icon": "asset/icon/fastly.icon",
                "ipv4": [],
            }
        }
    return norm


def save_ip_json(providers: Dict[str, dict]) -> None:
    p = ip_json_path()
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(providers, ensure_ascii=False, indent=2), encoding="utf-8")


def icon_for_provider(providers: Dict[str, dict], key: str) -> QIcon:
    icon_rel = str(providers.get(key, {}).get("icon", "")).strip()
    if not icon_rel:
        return QIcon()
    base = app_root_dir() / icon_rel
    if base.exists():
        return QIcon(str(base))
    for ext in (".ico", ".png", ".jpg", ".jpeg", ".svg"):
        p = base.with_suffix(ext)
        if p.exists():
            return QIcon(str(p))
    return QIcon()


def fetch_provider_ipv4(source_url: str, timeout: float = 12.0) -> List[str]:
    r = requests.get(source_url, timeout=timeout, headers={"User-Agent": USER_AGENT})
    r.raise_for_status()
    ct = (r.headers.get("content-type") or "").lower()

    # Fastly: JSON with addresses (v4) and ipv6_addresses (v6)
    if "application/json" in ct or source_url.rstrip("/").endswith("public-ip-list"):
        try:
            data = r.json()
            if isinstance(data, dict) and isinstance(data.get("addresses"), list):
                ipv4 = [str(x).strip() for x in data["addresses"] if isinstance(x, str)]
                ipv4 = [x for x in ipv4 if is_valid_ipv4_cidr(x)]
                seen = set()
                out: List[str] = []
                for x in ipv4:
                    if x not in seen:
                        seen.add(x)
                        out.append(x)
                return out
        except Exception:
            pass

    return extract_ipv4_cidrs(r.text)


# ------------------------- Scan generators ------------------------------------

def iter_range_sequential(cidr: str, rx: Optional[re.Pattern[str]]) -> Iterator[str]:
    net = ipaddress.IPv4Network(cidr, strict=False)
    for ip in net:
        s = str(ip)
        if rx and not rx.search(s):
            continue
        yield s


def iter_range_random_unique(cidr: str, rx: Optional[re.Pattern[str]], limit: int) -> Iterator[str]:
    net = ipaddress.IPv4Network(cidr, strict=False)
    size = int(net.num_addresses)
    base = int(net.network_address)
    k = min(limit, size)
    offsets = random.sample(range(size), k)  # unique
    for off in offsets:
        s = str(ipaddress.IPv4Address(base + int(off)))
        if rx and not rx.search(s):
            continue
        yield s


def latency_color(latency_ms: int, max_latency: int) -> QColor:
    if max_latency <= 0:
        max_latency = 1
    if latency_ms <= int(max_latency * 0.40):
        return QColor(81, 207, 102)   # green
    if latency_ms <= int(max_latency * 0.75):
        return QColor(255, 212, 59)   # yellow
    return QColor(255, 107, 107)      # red


def apply_dark_theme(app) -> None:
    """Apply a dark Fusion palette (safe no-op if Qt isn't available)."""
    try:
        from PyQt6.QtWidgets import QStyleFactory
        from PyQt6.QtGui import QPalette, QColor
        from PyQt6.QtCore import Qt
    except Exception:
        return

    try:
        app.setStyle(QStyleFactory.create("Fusion"))
        palette = QPalette()
        palette.setColor(QPalette.ColorRole.Window, QColor(53, 53, 53))
        palette.setColor(QPalette.ColorRole.WindowText, Qt.GlobalColor.white)
        palette.setColor(QPalette.ColorRole.Base, QColor(35, 35, 35))
        palette.setColor(QPalette.ColorRole.AlternateBase, QColor(53, 53, 53))
        palette.setColor(QPalette.ColorRole.ToolTipBase, Qt.GlobalColor.white)
        palette.setColor(QPalette.ColorRole.ToolTipText, Qt.GlobalColor.white)
        palette.setColor(QPalette.ColorRole.Text, Qt.GlobalColor.white)
        palette.setColor(QPalette.ColorRole.Button, QColor(53, 53, 53))
        palette.setColor(QPalette.ColorRole.ButtonText, Qt.GlobalColor.white)
        palette.setColor(QPalette.ColorRole.BrightText, Qt.GlobalColor.red)
        palette.setColor(QPalette.ColorRole.Link, QColor(42, 130, 218))
        palette.setColor(QPalette.ColorRole.Highlight, QColor(42, 130, 218))
        palette.setColor(QPalette.ColorRole.HighlightedText, Qt.GlobalColor.black)
        app.setPalette(palette)
    except Exception:
        return


    palette.setColor(QPalette.ColorRole.Window, QColor(24, 24, 28))
    palette.setColor(QPalette.ColorRole.WindowText, QColor(235, 235, 235))
    palette.setColor(QPalette.ColorRole.Base, QColor(18, 18, 22))
    palette.setColor(QPalette.ColorRole.AlternateBase, QColor(28, 28, 34))
    palette.setColor(QPalette.ColorRole.ToolTipBase, QColor(235, 235, 235))
    palette.setColor(QPalette.ColorRole.ToolTipText, QColor(30, 30, 30))
    palette.setColor(QPalette.ColorRole.Text, QColor(235, 235, 235))
    palette.setColor(QPalette.ColorRole.Button, QColor(34, 34, 40))
    palette.setColor(QPalette.ColorRole.ButtonText, QColor(235, 235, 235))
    palette.setColor(QPalette.ColorRole.BrightText, QColor(255, 80, 80))
    palette.setColor(QPalette.ColorRole.Link, QColor(120, 170, 255))
    palette.setColor(QPalette.ColorRole.Highlight, QColor(120, 170, 255))
    palette.setColor(QPalette.ColorRole.HighlightedText, QColor(15, 15, 15))
    palette.setColor(QPalette.ColorRole.PlaceholderText, QColor(160, 160, 160))

    app.setPalette(palette)

    app.setStyleSheet("""
        QGroupBox {
            border: 1px solid rgba(255,255,255,0.10);
            border-radius: 12px;
            margin-top: 10px;
            padding: 10px;
        }
        QGroupBox::title {
            subcontrol-origin: margin;
            left: 10px;
            padding: 0 6px;
        }
        QPushButton {
            padding: 8px 12px;
            border-radius: 10px;
            border: 1px solid rgba(255,255,255,0.12);
        }
        QPushButton:hover { border: 1px solid rgba(255,255,255,0.22); }
        QPushButton:disabled { color: rgba(255,255,255,0.35); border: 1px solid rgba(255,255,255,0.08); }
        QLineEdit, QComboBox, QPlainTextEdit {
            padding: 7px;
            border-radius: 10px;
            border: 1px solid rgba(255,255,255,0.12);
        }
        QLineEdit::placeholder, QPlainTextEdit::placeholder {
            color: rgba(190,190,190,0.65);
        }
        QTableView {
            border: 1px solid rgba(255,255,255,0.10);
            border-radius: 12px;
            gridline-color: rgba(255,255,255,0.08);
        }
        QHeaderView::section {
            background-color: rgba(255,255,255,0.06);
            padding: 8px;
            border: 1px solid rgba(255,255,255,0.08);
        }
        QLabel#Subtle {
            color: rgba(255,255,255,0.65);
        }
    """)


# ------------------------- Data models ----------------------------------------

@dataclass(order=True)
class ValidIP:
    latency: int
    ip: str
    provider: str


@dataclass
class RangeRow:
    provider: str
    cidr: str


@dataclass
class IPRow:
    ip: str
    provider: str  # auto-detected or "custom"


# ------------------------- Worker threads -------------------------------------

class UpdateWorker(QThread):
    status = pyqtSignal(str)
    finished_ok = pyqtSignal(dict, str)
    finished_err = pyqtSignal(str)

    def __init__(self, providers: Dict[str, dict], parent=None):
        super().__init__(parent)
        self.providers = json.loads(json.dumps(providers))

    def run(self):
        try:
            updated = 0
            for key, info in self.providers.items():
                src = str(info.get("source", "")).strip()
                if not src:
                    continue
                self.status.emit(f"Updating {key} ...")
                ipv4 = fetch_provider_ipv4(src)
                if ipv4:
                    info["ipv4"] = ipv4
                    updated += 1
            save_ip_json(self.providers)
            self.finished_ok.emit(self.providers, f"Update complete. Updated {updated} provider(s). Saved ip.json.")
        except Exception as e:
            self.finished_err.emit(str(e))


class RangeScannerWorker(QThread):
    progress = pyqtSignal(int, str, str, int, str)   # test_no, ip, try_char, current_latency, color
    found = pyqtSignal(str, str, int)                # provider, ip, latency
    status = pyqtSignal(str)
    errored = pyqtSignal(str)
    finished_ok = pyqtSignal()

    def __init__(
        self,
        ranges: List[Tuple[str, str]],
        scan_mode: str,  # "sequential" | "random" | "shuffle"
        max_latency: int,
        max_found: Optional[int],
        ip_regex: str,
        switch_after_minutes: Optional[int],
        switch_after_percent: Optional[int],
        switch_after_found: Optional[int],
        focus_productive: bool,
        move_on_first_success: bool,
    ):
        super().__init__()
        self.ranges = [(p, c) for p, c in ranges if is_valid_ipv4_cidr(c)]
        self.scan_mode = scan_mode
        self.max_latency = int(max_latency)
        self.max_found = int(max_found) if max_found is not None else None
        self.ip_regex = ip_regex

        # auto-switch range (disabled in shuffle)
        self.switch_after_minutes = switch_after_minutes
        self.switch_after_percent = switch_after_percent
        self.switch_after_found = switch_after_found
        self.focus_productive = bool(focus_productive)
        self.move_on_first_success = bool(move_on_first_success)

        self._stop = False
        self._test_no = 0
        self._found_total = 0

        self._session = requests.Session()
        self._session.headers.update({"User-Agent": USER_AGENT})
        try:
            requests.packages.urllib3.disable_warnings()  # type: ignore[attr-defined]
        except Exception:
            pass

        self._rx: Optional[re.Pattern[str]] = None
        if self.ip_regex.strip():
            self._rx = re.compile(self.ip_regex)

    def stop(self):
        self._stop = True

    def _range_limit(self, cidr: str) -> int:
        size = ipv4_count(cidr)
        if self.switch_after_percent is None:
            return size
        limit = int((self.switch_after_percent / 100.0) * size)
        return max(1, min(size, limit))

    def _should_switch_time(self, start_ts: float) -> bool:
        if self.switch_after_minutes is None:
            return False
        return (time.perf_counter() - start_ts) >= (self.switch_after_minutes * 60)

    def _test_one_ip(self, ip: str) -> Optional[int]:
        self._test_no += 1
        url = f"https://{ip}/__down"
        start_time = time.perf_counter()

        multiply = 1.5 if self.max_latency <= 500 else (1.2 if self.max_latency <= 1000 else 1.0)
        success_attempts = 0

        for i in range(MAX_TRIES):
            if self._stop:
                return None

            try_char = TRY_CHARS[i] if i < len(TRY_CHARS) else ""
            if i == 0:
                timeout_ms = int(multiply * self.max_latency)
                color = "red"
                current_latency = 0
            else:
                timeout_ms = int(1.2 * multiply * self.max_latency)
                color = "green"
                elapsed_ms = int((time.perf_counter() - start_time) * 1000.0)
                current_latency = max(0, elapsed_ms // (i + 1))

            self.progress.emit(self._test_no, ip, try_char, current_latency, color)

            try:
                self._session.get(url, timeout=timeout_ms / 1000.0, verify=False)
                success_attempts += 1
            except Timeout:
                pass
            except RequestException:
                success_attempts += 1

        total_ms = int((time.perf_counter() - start_time) * 1000.0)
        latency = max(0, total_ms // MAX_TRIES)

        if success_attempts == MAX_TRIES:
            return latency
        return None

    def run(self):
        try:
            # In Shuffle: disable auto-switch & focus & move-on-first-success (as requested)
            if self.scan_mode == "shuffle":
                self.switch_after_minutes = None
                self.switch_after_percent = None
                self.switch_after_found = None
                self.focus_productive = False
                self.move_on_first_success = False

            limits = {(p, c): self._range_limit(c) for p, c in self.ranges}

            if self.scan_mode == "shuffle":
                # Unique random per range, interleaved across ranges
                buckets = []
                for p, c in self.ranges:
                    net = ipaddress.IPv4Network(c, strict=False)
                    size = int(net.num_addresses)
                    base = int(net.network_address)
                    offsets = random.sample(range(size), size)  # full unique permutation
                    buckets.append({
                        "provider": p,
                        "cidr": c,
                        "base": base,
                        "offsets": offsets,
                        "idx": 0,
                    })
                random.shuffle(buckets)

                while buckets and not self._stop:
                    random.shuffle(buckets)
                    i = 0
                    while i < len(buckets) and not self._stop:
                        b = buckets[i]
                        if b["idx"] >= len(b["offsets"]):
                            buckets.pop(i)
                            continue

                        off = b["offsets"][b["idx"]]
                        b["idx"] += 1
                        ip = str(ipaddress.IPv4Address(b["base"] + int(off)))
                        if self._rx and not self._rx.search(ip):
                            continue

                        latency = self._test_one_ip(ip)
                        if latency is not None and latency <= self.max_latency:
                            self._found_total += 1
                            self.found.emit(b["provider"], ip, latency)
                            if self.max_found is not None and self._found_total >= self.max_found:
                                self.status.emit("Reached the requested number of working IPs. Stopping scan.")
                                self._stop = True
                                break

                        i += 1
                return

            # sequential/random: range-by-range
            for provider, cidr in self.ranges:
                if self._stop:
                    break

                per_found = 0
                per_tested = 0
                start_ts = time.perf_counter()
                limit = limits[(provider, cidr)]

                self.status.emit(f"Scanning range: {provider} {cidr}")

                if self.scan_mode == "sequential":
                    ip_iter = iter_range_sequential(cidr, self._rx)
                else:
                    ip_iter = iter_range_random_unique(cidr, self._rx, limit)

                for ip in ip_iter:
                    if self._stop:
                        break

                    # auto-switch rules (ignored once range is productive if focus is enabled)
                    if (not self.focus_productive or per_found == 0) and self._should_switch_time(start_ts):
                        self.status.emit(f"Switching range (time): {provider} {cidr}")
                        break
                    if (not self.focus_productive or per_found == 0) and self.switch_after_found is not None and per_found >= self.switch_after_found:
                        self.status.emit(f"Switching range (found): {provider} {cidr}")
                        break
                    if (not self.focus_productive or per_found == 0) and per_tested >= limit:
                        self.status.emit(f"Switching range (limit): {provider} {cidr}")
                        break

                    latency = self._test_one_ip(ip)
                    per_tested += 1
                    if latency is not None and latency <= self.max_latency:
                        per_found += 1
                        if self.focus_productive and per_found == 1:
                            # keep scanning this range longer
                            limit = ipv4_count(cidr)
                            start_ts = time.perf_counter()

                        self._found_total += 1
                        self.found.emit(provider, ip, latency)
                        if self.max_found is not None and self._found_total >= self.max_found:
                            self.status.emit("Reached the requested number of working IPs. Stopping scan.")
                            self._stop = True
                            break

                        if self.move_on_first_success and per_found >= 1:
                            self.status.emit(f"Move on after success: {provider} {cidr}")
                            break

        except Exception as e:
            self.errored.emit(str(e))
        finally:
            self.finished_ok.emit()


class IPScannerWorker(QThread):
    progress = pyqtSignal(int, str, str, int, str)    # test_no, ip, try_char, current_latency, color
    result = pyqtSignal(str, str, bool, int)          # provider, ip, success, latency
    status = pyqtSignal(str)
    errored = pyqtSignal(str)
    finished_ok = pyqtSignal()

    def __init__(
        self,
        ips: List[Tuple[str, str]],  # (provider, ip)
        max_latency: int,
    ):
        super().__init__()
        self.ips = list(ips)
        self.max_latency = int(max_latency)
        self._stop = False
        self._test_no = 0

        self._session = requests.Session()
        self._session.headers.update({"User-Agent": USER_AGENT})
        try:
            requests.packages.urllib3.disable_warnings()  # type: ignore[attr-defined]
        except Exception:
            pass

    def stop(self):
        self._stop = True

    def _test_one_ip(self, ip: str) -> Tuple[bool, int]:
        self._test_no += 1
        url = f"https://{ip}/__down"
        start_time = time.perf_counter()

        multiply = 1.5 if self.max_latency <= 500 else (1.2 if self.max_latency <= 1000 else 1.0)
        success_attempts = 0

        for i in range(MAX_TRIES):
            if self._stop:
                return False, 0

            try_char = TRY_CHARS[i] if i < len(TRY_CHARS) else ""
            if i == 0:
                timeout_ms = int(multiply * self.max_latency)
                color = "red"
                current_latency = 0
            else:
                timeout_ms = int(1.2 * multiply * self.max_latency)
                color = "green"
                elapsed_ms = int((time.perf_counter() - start_time) * 1000.0)
                current_latency = max(0, elapsed_ms // (i + 1))

            self.progress.emit(self._test_no, ip, try_char, current_latency, color)

            try:
                self._session.get(url, timeout=timeout_ms / 1000.0, verify=False)
                success_attempts += 1
            except Timeout:
                pass
            except RequestException:
                success_attempts += 1

        total_ms = int((time.perf_counter() - start_time) * 1000.0)
        latency = max(0, total_ms // MAX_TRIES)
        success = (success_attempts == MAX_TRIES and latency <= self.max_latency)
        return success, latency

    def run(self):
        try:
            for provider, ip in self.ips:
                if self._stop:
                    break
                self.status.emit(f"Testing {ip} ...")
                success, latency = self._test_one_ip(ip)
                self.result.emit(provider, ip, success, latency)
        except Exception as e:
            self.errored.emit(str(e))
        finally:
            self.finished_ok.emit()


# ------------------------- Main Window ----------------------------------------

class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()

        self.providers: Dict[str, dict] = load_ip_json()
        self._speedtest_provider_json_labels: Dict[str, str] = {}

        self.provider_checks: Dict[str, QCheckBox] = {}
        self.range_checks: Dict[str, bool] = {}  # "{provider}|{cidr}" -> checked

        # For provider detection in Scan IP
        self._provider_networks: Dict[str, List[ipaddress.IPv4Network]] = {}

        # Range scan results
        self.range_valid_ips: List[ValidIP] = []
        self.range_found_counts: Dict[str, int] = {}

        # Scan IP list + results
        self.ip_list: List[IPRow] = []
        self.ip_results: Dict[str, Tuple[bool, int, str]] = {}  # ip -> (success, latency, provider)

        self.range_worker: Optional[RangeScannerWorker] = None
        self.ip_worker: Optional[IPScannerWorker] = None
        self.up_worker: Optional[UpdateWorker] = None

        self.setWindowTitle("IP Clean Scanner By Farhad~UK")
        self.setMinimumSize(1180, 760)

        icon = load_app_icon()
        if icon is not None and hasattr(icon, 'isNull') and not icon.isNull():
            self.setWindowIcon(icon)

        splitter = QSplitter(Qt.Orientation.Horizontal)
        splitter.setHandleWidth(8)
        self.setCentralWidget(splitter)

        # ---------------- Left: Providers ----------------
        left = QWidget()
        left_layout = QVBoxLayout(left)
        left_layout.setContentsMargins(12, 12, 12, 12)
        left_layout.setSpacing(10)

        title = QLabel("Providers")
        title.setFont(QFont("Segoe UI", 14, QFont.Weight.Bold))
        left_layout.addWidget(title)

        subtitle = QLabel("Select which providers to show. Icons and sources come from ip.json.")
        subtitle.setObjectName("Subtle")
        subtitle.setWordWrap(True)
        left_layout.addWidget(subtitle)

        btn_row = QHBoxLayout()
        self.btn_prov_all = QPushButton("Select all")
        self.btn_prov_none = QPushButton("Select none")
        btn_row.addWidget(self.btn_prov_all)
        btn_row.addWidget(self.btn_prov_none)
        left_layout.addLayout(btn_row)

        btn_row2 = QHBoxLayout()
        self.btn_reload = QPushButton("Reload ip.json")
        self.btn_update = QPushButton("Update ip.json (fetch IPv4)")
        btn_row2.addWidget(self.btn_reload)
        btn_row2.addWidget(self.btn_update)
        left_layout.addLayout(btn_row2)

        btn_row3 = QHBoxLayout()
        self.btn_save_all_settings = QPushButton("Save all settings")
        btn_row3.addWidget(self.btn_save_all_settings)
        left_layout.addLayout(btn_row3)

        self.lbl_left_status = QLabel("Ready.")
        self.lbl_left_status.setObjectName("Subtle")
        self.lbl_left_status.setWordWrap(True)
        left_layout.addWidget(self.lbl_left_status)

        # ---- Provider / Range Management ----
        manage_box = QGroupBox("Provider Tools")
        mg = QVBoxLayout(manage_box)
        mg.setSpacing(8)

        self.btn_add_provider = QPushButton("Add Provider...")
        self.btn_add_provider.clicked.connect(self.open_add_provider_dialog)
        mg.addWidget(self.btn_add_provider)

        self.btn_add_range = QPushButton("Add IPv4 Range to Provider...")
        self.btn_add_range.clicked.connect(self.open_add_range_dialog)
        mg.addWidget(self.btn_add_range)

        left_layout.addWidget(manage_box)

        line = QFrame()
        line.setFrameShape(QFrame.Shape.HLine)
        line.setFrameShadow(QFrame.Shadow.Sunken)
        left_layout.addWidget(line)

        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll_body = QWidget()
        self.providers_layout = QVBoxLayout(scroll_body)
        self.providers_layout.setContentsMargins(6, 6, 6, 6)
        self.providers_layout.setSpacing(8)
        scroll.setWidget(scroll_body)
        left_layout.addWidget(scroll, 1)

        footer = QLabel("IP Clean Scanner By Farhad~UK")
        footer.setObjectName("Subtle")
        footer.setAlignment(Qt.AlignmentFlag.AlignCenter)
        left_layout.addWidget(footer)

        splitter.addWidget(left)

        # ---------------- Right: Tabs ----------------
        right = QWidget()
        right_layout = QVBoxLayout(right)
        right_layout.setContentsMargins(12, 12, 12, 12)
        right_layout.setSpacing(10)

        header = QLabel("IPv4 Range Manager & Scanner")
        header.setFont(QFont("Segoe UI", 16, QFont.Weight.Bold))
        right_layout.addWidget(header)

        self.tabs = QTabWidget()
        right_layout.addWidget(self.tabs, 1)
        splitter.addWidget(right)
        splitter.setStretchFactor(1, 1)
        splitter.setSizes([320, 860])

        # ---- Tab: Ranges ----
        tab_ranges = QWidget()
        tr_layout = QVBoxLayout(tab_ranges)
        tr_layout.setContentsMargins(0, 0, 0, 0)
        tr_layout.setSpacing(10)

        self.ranges_table = QTableView()
        self.ranges_table.setAlternatingRowColors(True)
        self.ranges_table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.ranges_table.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.ranges_table.customContextMenuRequested.connect(self._ranges_table_context_menu)

        self.ranges_model = RangesTableModel(self.providers, [])
        self.ranges_table.setModel(self.ranges_model)
        self.ranges_table.horizontalHeader().setStretchLastSection(True)
        self.ranges_table.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)

        tr_layout.addWidget(self.ranges_table, 1)

        self.lbl_ranges_summary = QLabel("")
        self.lbl_ranges_selected = QLabel("")
        self.lbl_ips_total = QLabel("")
        self.lbl_ips_selected = QLabel("")
        for w in (self.lbl_ranges_summary, self.lbl_ranges_selected, self.lbl_ips_total, self.lbl_ips_selected):
            w.setObjectName("Subtle")
        tr_layout.addWidget(self.lbl_ranges_summary)
        tr_layout.addWidget(self.lbl_ranges_selected)
        tr_layout.addWidget(self.lbl_ips_total)
        tr_layout.addWidget(self.lbl_ips_selected)

        self.tabs.addTab(tab_ranges, "Ranges")

        # ---- Tab: Scan Range ----
        tab_scan_range = QWidget()
        sr_layout = QVBoxLayout(tab_scan_range)
        sr_layout.setContentsMargins(0, 0, 0, 0)
        sr_layout.setSpacing(10)

        settings = QGroupBox("Scan Range settings")
        gs = QGridLayout(settings)
        gs.setHorizontalSpacing(10)
        gs.setVerticalSpacing(10)

        self.scan_mode = QComboBox()
        self.scan_mode.addItems(["Sequential", "Random", "Shuffle (unique)"])
        self.scan_mode.setCurrentText("Shuffle (unique)")
        self.scan_mode.currentIndexChanged.connect(self.on_scan_mode_changed)

        self.max_latency_range = QComboBox()
        # Use editable combo for nicer feel (preset common values)
        self.max_latency_range.setEditable(True)
        self.max_latency_range.addItems(["500", "800", "1000", "1200", "1500", "2000"])
        self.max_latency_range.setCurrentText("1000")

        self.max_found_range = QLineEdit()
        self.max_found_range.setPlaceholderText("Unlimited (leave blank)")

        self.regex_range = QLineEdit()
        self.regex_range.setPlaceholderText(r"^104\.17\.|^141\.")

        # auto switch options (disabled in shuffle)
        self.opt_switch_found5 = QCheckBox("Auto switch range after 5 working IPs in the current range")
        self.opt_switch_3min = QCheckBox("Auto switch range after 3 minutes in the current range")
        self.opt_switch_10 = QCheckBox("Auto switch range after scanning 10% of the current range")
        self.opt_switch_30 = QCheckBox("Auto switch range after scanning 30% of the current range")
        self.opt_switch_50 = QCheckBox("Auto switch range after scanning 50% of the current range")
        self.opt_focus_productive = QCheckBox("Focus on productive ranges (keep scanning ranges that find working IPs)")
        self.opt_move_on_success = QCheckBox("Move on after first SUCCESS in each range")
        self.opt_send_to_ip_tab = QCheckBox("Send working IPs to 'Scan IP' list automatically")

        gs.addWidget(QLabel("Mode:"), 0, 0)
        gs.addWidget(self.scan_mode, 0, 1)
        gs.addWidget(QLabel("Max acceptable latency (ms):"), 0, 2)
        gs.addWidget(self.max_latency_range, 0, 3)

        gs.addWidget(QLabel("Stop after N working IPs:"), 1, 0)
        gs.addWidget(self.max_found_range, 1, 1)
        gs.addWidget(QLabel("IP filter (regex):"), 1, 2)
        gs.addWidget(self.regex_range, 1, 3)

        gs.addWidget(self.opt_switch_found5, 2, 0, 1, 4)
        gs.addWidget(self.opt_switch_3min, 3, 0, 1, 2)
        gs.addWidget(self.opt_switch_10, 3, 2, 1, 2)
        gs.addWidget(self.opt_switch_30, 4, 0, 1, 2)
        gs.addWidget(self.opt_switch_50, 4, 2, 1, 2)
        gs.addWidget(self.opt_focus_productive, 5, 0, 1, 4)
        gs.addWidget(self.opt_move_on_success, 6, 0, 1, 2)
        gs.addWidget(self.opt_send_to_ip_tab, 6, 2, 1, 2)

        self.user_ip_label = QLabel("Your IP: ...")
        self.user_loc_label = QLabel("Location: ...")
        self.user_ip_label.setObjectName("Subtle")
        self.user_loc_label.setObjectName("Subtle")
        gs.addWidget(self.user_ip_label, 7, 0, 1, 2)
        gs.addWidget(self.user_loc_label, 7, 2, 1, 2)

        # move settings into a dialog, and show with a button
        self.scan_range_settings_dialog = QDialog(self)
        self.scan_range_settings_dialog.setWindowTitle("Scan Range settings")
        self.scan_range_settings_dialog.setModal(True)
        dlg_layout = QVBoxLayout(self.scan_range_settings_dialog)
        dlg_layout.addWidget(settings)
        dlg_btns = QHBoxLayout()
        btn_close = QPushButton("Close")
        btn_close.clicked.connect(self.scan_range_settings_dialog.close)
        dlg_btns.addStretch(1)
        dlg_btns.addWidget(btn_close)
        dlg_layout.addLayout(dlg_btns)

        self.btn_open_range_settings = QPushButton("Open Scan Range Settings...")
        self.btn_open_range_settings.clicked.connect(self.open_scan_range_settings)
        sr_layout.addWidget(self.btn_open_range_settings)

        ctl = QHBoxLayout()
        self.btn_start_range = QPushButton("Start scan")
        self.btn_stop_range = QPushButton("Stop")
        self.btn_stop_range.setEnabled(False)
        self.lbl_scan_range_status = QLabel("Tip: Disable VPN for best results.")
        self.lbl_scan_range_status.setObjectName("Subtle")
        self.lbl_scan_range_status.setAlignment(Qt.AlignmentFlag.AlignCenter)
        ctl.addWidget(self.btn_start_range)
        ctl.addWidget(self.btn_stop_range)
        ctl.addWidget(self.lbl_scan_range_status, 1)
        sr_layout.addLayout(ctl)

        live = QHBoxLayout()
        self.range_test_no_label = QLabel("Test: 0")
        self.range_current_ip_label = QLabel("0.0.0.0")
        self.range_try_char_label = QLabel("Try: •")
        self.range_latency_label = QLabel("Latency: 0 ms")
        for w in (self.range_test_no_label, self.range_current_ip_label, self.range_try_char_label, self.range_latency_label):
            w.setAlignment(Qt.AlignmentFlag.AlignCenter)
        live.addWidget(self.range_test_no_label)
        live.addWidget(self.range_current_ip_label)
        live.addWidget(self.range_try_char_label)
        live.addWidget(self.range_latency_label)

        self.range_found_total_label = QLabel("Found: 0 (total)")
        self.range_found_total_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.range_found_total_label.setObjectName("Subtle")
        live.addWidget(self.range_found_total_label)

        self.range_found_by_provider_label = QLabel("By provider: -")
        self.range_found_by_provider_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.range_found_by_provider_label.setObjectName("Subtle")
        live.addWidget(self.range_found_by_provider_label)

        self.btn_export_range_csv = QPushButton("Export as CSV")
        self.btn_export_range_json = QPushButton("Export as JSON")
        self.btn_save_range_success = QPushButton("Save Successful IPs (TXT)")
        self.btn_export_range_csv.setEnabled(False)
        self.btn_export_range_json.setEnabled(False)
        self.btn_save_range_success.setEnabled(False)
        self.btn_export_range_csv.clicked.connect(lambda: self.export_range_results("csv"))
        self.btn_export_range_json.clicked.connect(lambda: self.export_range_results("json"))
        self.btn_save_range_success.clicked.connect(self.show_save_success_menu_range)
        live.addWidget(self.btn_export_range_csv)
        live.addWidget(self.btn_export_range_json)
        live.addWidget(self.btn_save_range_success)

        sr_layout.addLayout(live)

        # Results table (no # column; table has row numbers)
        self.range_res_table = QTableView()
        self.range_res_table.setAlternatingRowColors(True)
        self.range_res_table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.range_res_table.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.range_res_table.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.range_res_table.customContextMenuRequested.connect(self._range_table_context_menu)

        self.range_res_model = ValidIPResultsModel(self.providers, [], max_latency=1000)
        self.range_res_table.setModel(self.range_res_model)
        self.range_res_table.horizontalHeader().setStretchLastSection(True)

        sr_layout.addWidget(self.range_res_table, 1)

        self.tabs.addTab(tab_scan_range, "Scan Range")

        # ---- Tab: Scan IP ----
        tab_scan_ip = QWidget()
        si_layout = QVBoxLayout(tab_scan_ip)
        si_layout.setContentsMargins(0, 0, 0, 0)
        si_layout.setSpacing(10)

        ip_settings = QGroupBox("Scan IP settings")
        ig = QGridLayout(ip_settings)
        ig.setHorizontalSpacing(10)
        ig.setVerticalSpacing(10)

        self.btn_load_txt = QPushButton("Load TXT (extract IPv4)")
        self.btn_load_from_range = QPushButton("Load IPs from Scan Range")
        self.btn_clear_ip_list = QPushButton("Clear List")
        self.btn_remove_fail = QPushButton("Remove Failed IPs")

        self.max_latency_ip = QComboBox()
        self.max_latency_ip.setEditable(True)
        self.max_latency_ip.addItems(["500", "800", "1000", "1200", "1500", "2000"])
        self.max_latency_ip.setCurrentText("1000")

        self.btn_start_ip = QPushButton("Start scan")
        self.btn_stop_ip = QPushButton("Stop")
        self.btn_stop_ip.setEnabled(False)

        self.lbl_scan_ip_status = QLabel("Load IPs from a TXT file or import them from Scan Range.")
        self.chk_sort_latency = QCheckBox("Sort by Latency (Successful IPs First)")
        self.chk_sort_latency.setChecked(False)
        self.lbl_scan_ip_status.setObjectName("Subtle")
        self.lbl_scan_ip_status.setWordWrap(True)

        ig.addWidget(self.btn_load_txt, 0, 0)
        ig.addWidget(self.btn_load_from_range, 0, 1)
        ig.addWidget(self.btn_clear_ip_list, 0, 2)
        ig.addWidget(QLabel("Max acceptable latency (ms):"), 0, 3)
        ig.addWidget(self.max_latency_ip, 0, 4)

        ig.addWidget(self.btn_start_ip, 1, 0)
        ig.addWidget(self.btn_stop_ip, 1, 1)
        ig.addWidget(self.btn_remove_fail, 1, 2)
        ig.addWidget(self.lbl_scan_ip_status, 1, 3, 1, 2)
        ig.addWidget(self.chk_sort_latency, 2, 0, 1, 5)

        si_layout.addWidget(ip_settings)

        ip_live = QHBoxLayout()
        self.ip_test_no_label = QLabel("Test: 0")
        self.ip_current_ip_label = QLabel("0.0.0.0")
        self.ip_try_char_label = QLabel("Try: •")
        self.ip_latency_label = QLabel("Latency: 0 ms")
        for w in (self.ip_test_no_label, self.ip_current_ip_label, self.ip_try_char_label, self.ip_latency_label):
            w.setAlignment(Qt.AlignmentFlag.AlignCenter)
        ip_live.addWidget(self.ip_test_no_label)
        ip_live.addWidget(self.ip_current_ip_label)
        ip_live.addWidget(self.ip_try_char_label)
        ip_live.addWidget(self.ip_latency_label)

        self.ip_done_label = QLabel("Done: 0 / 0")
        self.ip_done_label.setObjectName("Subtle")
        self.ip_done_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        ip_live.addWidget(self.ip_done_label)

        self.btn_export_ip_csv = QPushButton("Export as CSV")
        self.btn_export_ip_json = QPushButton("Export as JSON")
        self.btn_save_success_txt = QPushButton("Save SUCCESS IPs (TXT)")
        self.btn_export_ip_csv.setEnabled(False)
        self.btn_export_ip_json.setEnabled(False)
        self.btn_save_success_txt.setEnabled(False)
        self.btn_save_success_txt.setEnabled(False)
        self.btn_export_ip_csv.clicked.connect(lambda: self.export_ip_results("csv"))
        self.btn_export_ip_json.clicked.connect(lambda: self.export_ip_results("json"))
        self.btn_save_success_txt.clicked.connect(self.show_save_success_menu_ip)
        ip_live.addWidget(self.btn_export_ip_csv)
        ip_live.addWidget(self.btn_export_ip_json)
        ip_live.addWidget(self.btn_save_success_txt)

        si_layout.addLayout(ip_live)

        # Scan IP results table
        self.ip_res_table = QTableView()
        self.ip_res_table.setAlternatingRowColors(True)
        self.ip_res_table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.ip_res_table.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.ip_res_table.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.ip_res_table.customContextMenuRequested.connect(self._ip_table_context_menu)

        self.ip_res_model = ScanIPTableModel(self.providers, [], self.ip_results, max_latency=1000)
        self.ip_res_table.setModel(self.ip_res_model)
        self.ip_res_table.horizontalHeader().setStretchLastSection(True)

        si_layout.addWidget(self.ip_res_table, 1)

        self.tabs.addTab(tab_scan_ip, "Scan IP")

        # ---- Tab: Speed Test ----
        tab_speed = QWidget()
        sp_layout = QVBoxLayout(tab_speed)
        sp_layout.setContentsMargins(6, 6, 6, 6)
        sp_layout.setSpacing(6)

        # compact setup row above the table
        setup_box = QGroupBox("Speed Test Setup")
        sg = QGridLayout(setup_box)
        sg.setContentsMargins(8, 8, 8, 8)
        sg.setHorizontalSpacing(8)
        sg.setVerticalSpacing(6)

        # mode: global vs per-provider (radio buttons)
        self.speedtest_use_global_json = QRadioButton("Global JSON (apply to all)")
        self.speedtest_use_per_provider = QRadioButton("Per-provider JSON")
        self.speedtest_mode_group = QButtonGroup(self)
        self.speedtest_mode_group.addButton(self.speedtest_use_global_json)
        self.speedtest_mode_group.addButton(self.speedtest_use_per_provider)
        self.speedtest_use_global_json.setChecked(True)

        self.speedtest_btn_load_global_json = QPushButton("Load Global JSON")
        self.speedtest_btn_load_global_json.clicked.connect(self.speedtest_load_global_json)
        self.speedtest_global_json_path: Optional[Path] = None

        # per-provider config widgets
        self.speedtest_provider_combo = QComboBox()
        self.speedtest_provider_combo.setEditable(False)
        self.speedtest_btn_load_provider_json = QPushButton("Load Provider JSON")
        self.speedtest_btn_load_provider_json.clicked.connect(self.speedtest_load_provider_json)

        self.speedtest_provider_cfg_label = QLabel("Provider config: ---")
        self.speedtest_provider_cfg_label.setStyleSheet("color: rgba(255,255,255,0.75);")

        # load IPs buttons
        self.btn_speed_load_from_range = QPushButton("Load IPs from Scan Range")
        self.btn_speed_load_from_ip = QPushButton("Load IPs from Scan IP List")
        self.btn_speed_load_from_txt = QPushButton("Load IPs from TXT")
        self.btn_speed_load_from_range.clicked.connect(self.speedtest_load_ips_from_range)
        self.btn_speed_load_from_ip.clicked.connect(self.speedtest_load_ips_from_scanip)
        self.btn_speed_load_from_txt.clicked.connect(self.speedtest_load_ips_from_txt)

        # layout grid (two compact rows)
        sg.addWidget(self.speedtest_use_global_json, 0, 0)
        sg.addWidget(self.speedtest_btn_load_global_json, 0, 1)
        sg.addWidget(self.speedtest_use_per_provider, 0, 2)

        sg.addWidget(QLabel("Provider:"), 1, 0)
        sg.addWidget(self.speedtest_provider_combo, 1, 1)
        sg.addWidget(self.speedtest_btn_load_provider_json, 1, 2)
        sg.addWidget(self.speedtest_provider_cfg_label, 2, 0, 1, 3)

        ip_row = QHBoxLayout()
        ip_row.setSpacing(8)
        ip_row.addWidget(self.btn_speed_load_from_range)
        ip_row.addWidget(self.btn_speed_load_from_ip)
        ip_row.addWidget(self.btn_speed_load_from_txt)
        ip_row.addStretch(1)
        sg.addLayout(ip_row, 3, 0, 1, 3)

        sp_layout.addWidget(setup_box)
# embed SpeedTestGUI as child widget
        self.speed_test_widget = SpeedTestGUI(embed_mode=True)
        sp_layout.addWidget(self.speed_test_widget, 1)

        # wire up speed-test config controls
        self.speedtest_provider_combo.currentIndexChanged.connect(self._on_speedtest_provider_changed)
        self.speedtest_use_per_provider.toggled.connect(self._on_speedtest_json_mode_changed)
        self.speedtest_use_global_json.toggled.connect(self._on_speedtest_json_mode_changed)

        # push provider icons into the speed test table
        try:
            icon_map = {prov: icon_for_provider(self.providers, prov) for prov in self.providers.keys()}
            self.speed_test_widget.set_provider_icons(icon_map)
            self.speed_test_widget.set_providers(self.providers)
        except Exception:
            pass

        self._on_speedtest_provider_changed()
        self._on_speedtest_json_mode_changed()

        self.tabs.addTab(tab_speed, "Speed Test")

        # ---- Tab: Tools ----
        tab_tools = QWidget()
        tl = QVBoxLayout(tab_tools)
        tl.setContentsMargins(0, 0, 0, 0)
        tl.setSpacing(10)

        tools_btn_row = QHBoxLayout()
        self.btn_open_tools_cidr = QPushButton("CIDR → IPv4...")
        self.btn_open_tools_cidr.clicked.connect(self.open_tools_cidr_dialog)
        tools_btn_row.addWidget(self.btn_open_tools_cidr)
        self.btn_open_tools_ipcfg = QPushButton("IP to Config...")
        self.btn_open_tools_ipcfg.clicked.connect(self.open_tools_ipcfg_dialog)
        tools_btn_row.addWidget(self.btn_open_tools_ipcfg)
        tools_btn_row.addStretch(1)
        tl.addLayout(tools_btn_row)

        tools_box = QGroupBox("CIDR → IPv4")
        tg = QGridLayout(tools_box)
        tg.setHorizontalSpacing(10)
        tg.setVerticalSpacing(10)

        self.tools_cidr = QLineEdit()
        self.tools_cidr.setPlaceholderText("Example: 103.244.50.0/24")
        self.btn_tools_convert = QPushButton("Convert CIDR")
        self.btn_tools_save = QPushButton("Save as TXT")
        self.btn_tools_move = QPushButton('Move IPs to "Scan IP" List')
        self.btn_tools_save.setEnabled(False)
        self.btn_tools_move.setEnabled(False)
        self.btn_tools_move_speed = QPushButton('Move IPs to "Speed Test"')
        self.btn_tools_move_speed.setEnabled(False)

        self.btn_tools_clear = QPushButton("Clear List")
        self.btn_tools_clear.clicked.connect(self.tools_clear_list)
        self.btn_tools_clear.setEnabled(False)

        self.tools_info = QLabel("Convert CIDR an IPv4 CIDR block into a list of individual IP addresses.")
        self.tools_info.setObjectName("Subtle")
        self.tools_info.setWordWrap(True)

        tg.addWidget(QLabel("CIDR:"), 0, 0)
        tg.addWidget(self.tools_cidr, 0, 1, 1, 3)
        tg.addWidget(self.btn_tools_convert, 0, 4)
        tg.addWidget(self.btn_tools_save, 1, 2)
        tg.addWidget(self.btn_tools_move, 1, 3)
        tg.addWidget(self.btn_tools_move_speed, 1, 4)
        tg.addWidget(self.tools_info, 2, 0, 1, 5)

        self.tools_table = QTableView()
        self.tools_table.setAlternatingRowColors(True)
        self.tools_table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.tools_table.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)

        self.tools_model = ToolsIPModel([])
        self.tools_table.setModel(self.tools_model)
        self.tools_table.horizontalHeader().setStretchLastSection(True)
        self.tools_table.clicked.connect(self.on_tools_cell_clicked)

        # ---- IP to Config ----
        ipcfg_box = QGroupBox("IP to Config")
        ipcfg_layout = QVBoxLayout(ipcfg_box)

        ipcfg_src_row = QHBoxLayout()
        self.btn_ipcfg_load_speed = QPushButton('Load from "Speed Test"')
        self.btn_ipcfg_load_speed.clicked.connect(self.tools_ipcfg_load_from_speedtest)
        ipcfg_src_row.addWidget(self.btn_ipcfg_load_speed)

        self.btn_ipcfg_load_scan = QPushButton('Load from "Scan IP"')
        self.btn_ipcfg_load_scan.clicked.connect(self.tools_ipcfg_load_from_scanip)
        ipcfg_src_row.addWidget(self.btn_ipcfg_load_scan)

        self.btn_ipcfg_load_txt = QPushButton("Load IPs from TXT")
        self.btn_ipcfg_load_txt.clicked.connect(self.tools_ipcfg_load_from_txt)
        ipcfg_src_row.addWidget(self.btn_ipcfg_load_txt)
        ipcfg_src_row.addStretch(1)
        ipcfg_layout.addLayout(ipcfg_src_row)

        self.ipcfg_loaded_label = QLabel("Loaded: 0")
        ipcfg_layout.addWidget(self.ipcfg_loaded_label)

        ipcfg_input_row = QHBoxLayout()
        self.ipcfg_input = QPlainTextEdit()
        self.ipcfg_input.setPlaceholderText("Enter IPs (one per line)")
        ipcfg_input_row.addWidget(self.ipcfg_input)
        ipcfg_layout.addLayout(ipcfg_input_row)

        tmpl_row = QHBoxLayout()
        self.ipcfg_template = QLineEdit()
        self.ipcfg_template.setPlaceholderText("Paste vless/vmess template URL with [ip] placeholder")
        tmpl_row.addWidget(QLabel("Template:"))
        tmpl_row.addWidget(self.ipcfg_template)
        ipcfg_layout.addLayout(tmpl_row)

        gen_row = QHBoxLayout()
        self.btn_ipcfg_generate = QPushButton("Generate")
        self.btn_ipcfg_generate.clicked.connect(self.tools_ipcfg_generate)
        gen_row.addWidget(self.btn_ipcfg_generate)

        self.btn_ipcfg_copy = QPushButton("Copy to Clipboard")
        self.btn_ipcfg_copy.clicked.connect(self.tools_ipcfg_copy)
        gen_row.addWidget(self.btn_ipcfg_copy)

        self.btn_ipcfg_save = QPushButton("Save as TXT")
        self.btn_ipcfg_save.clicked.connect(self.tools_ipcfg_save)
        gen_row.addWidget(self.btn_ipcfg_save)
        gen_row.addStretch(1)
        ipcfg_layout.addLayout(gen_row)

        self.ipcfg_output = QPlainTextEdit()
        self.ipcfg_output.setReadOnly(True)
        self.ipcfg_output.setPlaceholderText("Generated configs will appear here (one per line)")
        ipcfg_layout.addWidget(self.ipcfg_output)

        # ---- Tools dialogs ----
        self.tools_cidr_dialog = QDialog(self)
        self.tools_cidr_dialog.setWindowTitle("CIDR → IPv4")
        self.tools_cidr_dialog.setModal(True)
        tools_dlg_layout = QVBoxLayout(self.tools_cidr_dialog)
        tools_dlg_layout.addWidget(tools_box)
        tools_dlg_layout.addWidget(self.tools_table, 1)
        tools_dlg_btns = QHBoxLayout()
        btn_tools_close = QPushButton("Close")
        btn_tools_close.clicked.connect(self.tools_cidr_dialog.close)
        tools_dlg_btns.addStretch(1)
        tools_dlg_btns.addWidget(btn_tools_close)
        tools_dlg_layout.addLayout(tools_dlg_btns)

        self.tools_ipcfg_dialog = QDialog(self)
        self.tools_ipcfg_dialog.setWindowTitle("IP to Config")
        self.tools_ipcfg_dialog.setModal(True)
        ipcfg_dlg_layout = QVBoxLayout(self.tools_ipcfg_dialog)
        ipcfg_dlg_layout.addWidget(ipcfg_box)
        ipcfg_dlg_btns = QHBoxLayout()
        btn_ipcfg_close = QPushButton("Close")
        btn_ipcfg_close.clicked.connect(self.tools_ipcfg_dialog.close)
        ipcfg_dlg_btns.addStretch(1)
        ipcfg_dlg_btns.addWidget(btn_ipcfg_close)
        ipcfg_dlg_layout.addLayout(ipcfg_dlg_btns)


        self.tabs.addTab(tab_tools, "Tools")

        self.btn_tools_convert.clicked.connect(self.tools_convert_cidr)
        self.btn_tools_save.clicked.connect(self.tools_save_txt)
        self.btn_tools_move.clicked.connect(self.tools_move_to_scanip)
        self.btn_tools_move_speed.clicked.connect(self.tools_move_to_speedtest)

        # Buttons wiring
        self.btn_prov_all.clicked.connect(self.select_all_providers)
        self.btn_prov_none.clicked.connect(self.select_none_providers)
        self.btn_reload.clicked.connect(self.reload_ip_json)
        self.btn_update.clicked.connect(self.update_ip_json)
        self.btn_save_all_settings.clicked.connect(self.save_all_settings)

        self.btn_start_range.clicked.connect(self.start_range_scan)
        self.btn_stop_range.clicked.connect(self.stop_range_scan)

        self.btn_load_txt.clicked.connect(self.load_txt_ips)
        self.btn_load_from_range.clicked.connect(self.load_ips_from_scan_range)
        self.btn_clear_ip_list.clicked.connect(self.clear_ip_list)
        self.btn_remove_fail.clicked.connect(self.remove_fail_ips)
        self.chk_sort_latency.stateChanged.connect(self.refresh_ip_table)
        self.btn_start_ip.clicked.connect(self.start_ip_scan)
        self.btn_stop_ip.clicked.connect(self.stop_ip_scan)

        # Initial build
        self.rebuild_provider_checkboxes()
        self.refresh_ranges_table()
        self.rebuild_provider_networks()

        # fill provider combo for speed test
        self._rebuild_speedtest_provider_combo()
        self._refresh_provider_add_combo()

        ip, loc = fetch_user_ip_info()
        self.user_ip_label.setText(f"Your IP: {ip}")
        self.user_loc_label.setText(f"Location: {loc}")

        self.on_scan_mode_changed()

        # restore previous session (if any)
        self.load_all_settings()

    # ---------------- Provider detection (Scan IP) ----------------

    def rebuild_provider_networks(self):
        nets: Dict[str, List[ipaddress.IPv4Network]] = {}
        for prov, info in self.providers.items():
            cidrs = info.get("ipv4", []) or []
            tmp: List[ipaddress.IPv4Network] = []
            for cidr in cidrs:
                try:
                    tmp.append(ipaddress.IPv4Network(str(cidr), strict=False))
                except Exception:
                    continue
            nets[prov] = tmp
        self._provider_networks = nets

    def detect_provider_for_ip(self, ip: str) -> str:
        ip = (ip or "").strip()
        try:
            ip_obj = ipaddress.IPv4Address(ip)
        except Exception:
            return "custom"

        best_provider = "custom"
        best_prefix = -1

        # Prefer the most specific (largest prefixlen) match
        for prov in sorted((getattr(self, "_provider_networks", {}) or {}).keys()):
            for net in (self._provider_networks or {}).get(prov, []):
                try:
                    if ip_obj in net and net.prefixlen > best_prefix:
                        best_prefix = net.prefixlen
                        best_provider = prov
                except Exception:
                    continue

        return best_provider

    def rebuild_provider_checkboxes(self):
        while self.providers_layout.count():
            item = self.providers_layout.takeAt(0)
            w = item.widget()
            if w:
                w.deleteLater()

        self.provider_checks.clear()

        for prov in sorted(self.providers.keys()):
            count = len((self.providers.get(prov, {}).get("ipv4", []) or []))
            cb = QCheckBox(f"{prov}  ({count} ranges)")
            cb.setProperty("provider_key", prov)
            cb.setChecked(True)
            ic = icon_for_provider(self.providers, prov)
            if not ic.isNull():
                cb.setIcon(ic)
            cb.stateChanged.connect(self.refresh_ranges_table)
            self.providers_layout.addWidget(cb)
            self.provider_checks[prov] = cb

        self.providers_layout.addStretch(1)

    def selected_providers(self) -> List[str]:
        return [k for k, cb in self.provider_checks.items() if cb.isChecked()]

    def select_all_providers(self):
        for cb in self.provider_checks.values():
            cb.setChecked(True)

    def select_none_providers(self):
        for cb in self.provider_checks.values():
            cb.setChecked(False)

    # ---------------- Ranges tab ----------------

    def build_rows(self) -> List[RangeRow]:
        rows: List[RangeRow] = []
        selected = set(self.selected_providers())
        for prov, info in self.providers.items():
            if prov not in selected:
                continue
            for cidr in info.get("ipv4", []) or []:
                if isinstance(cidr, str) and is_valid_ipv4_cidr(cidr.strip()):
                    rows.append(RangeRow(provider=prov, cidr=cidr.strip()))
        rows.sort(key=lambda r: (r.provider, r.cidr))
        return rows

    def refresh_ranges_table(self):
        rows = self.build_rows()

        selected_ranges = 0
        total_ips = 0
        selected_ips = 0

        model_rows: List[Tuple[str, str, int, bool]] = []

        for r in rows:
            key = f"{r.provider}|{r.cidr}"
            if key not in self.range_checks:
                self.range_checks[key] = True
            checked = bool(self.range_checks.get(key, True))

            cnt = ipv4_count(r.cidr)
            total_ips += cnt
            if checked:
                selected_ranges += 1
                selected_ips += cnt

            model_rows.append((r.provider, r.cidr, cnt, checked))

        # Push to model (virtualized; no per-cell item allocations)
        try:
            self.ranges_model.set_providers(self.providers)
            self.ranges_model.set_rows(model_rows)
        except Exception:
            pass

        self.lbl_ranges_summary.setText(f"Showing {len(rows)} ranges from {len(self.selected_providers())} provider(s).")
        self.lbl_ranges_selected.setText(f"Selected ranges: {selected_ranges}")
        self.lbl_ips_total.setText(f"Total IPs (shown): {total_ips}")
        self.lbl_ips_selected.setText(f"Total IPs (selected): {selected_ips}")

    def on_range_item_changed(self, *args, **kwargs):
        # QAbstractTableModel handles checkbox state directly.
        return

    def selected_ranges_for_scan(self) -> List[Tuple[str, str]]:
        try:
            # sync persistent selection state
            for prov, cidr, checked in self.ranges_model.rows_state():
                self.range_checks[f"{prov}|{cidr}"] = bool(checked)
            ranges = self.ranges_model.checked_ranges()
        except Exception:
            ranges = []
        return list(ranges)

    # ---------------- ip.json actions ----------------

    def reload_ip_json(self):
        self.providers = load_ip_json()
        self._after_providers_changed()
        QMessageBox.information(self, "Reloaded", "ip.json loaded from disk.")

    def update_ip_json(self):
        if not self.providers:
            QMessageBox.warning(self, "No providers", "ip.json does not contain any providers.")
            return

        self.btn_update.setEnabled(False)
        self.btn_update.setText("Updating...")
        self.lbl_left_status.setText("Downloading provider IP lists...")

        self.up_worker = UpdateWorker(self.providers, self)
        self.up_worker.status.connect(self.lbl_left_status.setText)

        def ok(new_providers: dict, msg: str):
            self.providers = new_providers
            self._after_providers_changed()
            self.btn_update.setEnabled(True)
            self.btn_update.setText("Update ip.json (fetch IPv4)")
            self.lbl_left_status.setText("Ready.")
            QMessageBox.information(self, "Update complete", msg)

        def err(msg: str):
            self.btn_update.setEnabled(True)
            self.btn_update.setText("Update ip.json (fetch IPv4)")
            self.lbl_left_status.setText("Ready.")
            QMessageBox.warning(self, "Update failed", msg)

        self.up_worker.finished_ok.connect(ok)
        self.up_worker.finished_err.connect(err)
        self.up_worker.start()

    def _refresh_provider_add_combo(self) -> None:
        # kept for dialog population; no inline combo anymore
        return

    def _after_providers_changed(self) -> None:
        self.rebuild_provider_checkboxes()
        self.refresh_ranges_table()
        self.rebuild_provider_networks()
        self._rebuild_speedtest_provider_combo()
        self._refresh_provider_add_combo()
        try:
            icon_map = {prov: icon_for_provider(self.providers, prov) for prov in self.providers.keys()}
            self.speed_test_widget.set_provider_icons(icon_map)
            self.speed_test_widget.set_providers(self.providers)
            self.range_res_model.set_providers(self.providers)
            self.ip_res_model.set_providers(self.providers)
        except Exception:
            pass

    def open_add_provider_dialog(self) -> None:
        dlg = QDialog(self)
        dlg.setWindowTitle("Add Provider")
        dlg.setModal(True)
        layout = QVBoxLayout(dlg)

        form = QGridLayout()
        form.setHorizontalSpacing(8)
        form.setVerticalSpacing(6)

        name_edit = QLineEdit()
        name_edit.setPlaceholderText("Example: fastly")
        source_edit = QLineEdit()
        source_edit.setPlaceholderText("https://api.fastly.com/public-ip-list")
        icon_edit = QLineEdit()
        icon_edit.setPlaceholderText("asset/icon/fastly.icon")
        cidr_edit = QPlainTextEdit()
        cidr_edit.setPlaceholderText("IPv4 CIDR list (one per line)")

        form.addWidget(QLabel("Name:"), 0, 0)
        form.addWidget(name_edit, 0, 1)
        form.addWidget(QLabel("Source:"), 1, 0)
        form.addWidget(source_edit, 1, 1)
        form.addWidget(QLabel("Icon:"), 2, 0)
        form.addWidget(icon_edit, 2, 1)
        form.addWidget(QLabel("IPv4 CIDR:"), 3, 0)
        form.addWidget(cidr_edit, 3, 1)

        layout.addLayout(form)

        btns = QHBoxLayout()
        btn_ok = QPushButton("Add Provider")
        btn_cancel = QPushButton("Cancel")
        btns.addStretch(1)
        btns.addWidget(btn_cancel)
        btns.addWidget(btn_ok)
        layout.addLayout(btns)

        btn_cancel.clicked.connect(dlg.reject)

        def _apply():
            name = name_edit.text().strip()
            source = source_edit.text().strip()
            icon = icon_edit.text().strip()
            cidr_text = cidr_edit.toPlainText().strip()

            if not name or not source or not icon:
                QMessageBox.warning(self, "Missing fields", "Please fill Name, Source, and Icon.")
                return

            cidrs = extract_ipv4_cidrs(cidr_text)
            if not cidrs:
                QMessageBox.warning(self, "Invalid IPv4 CIDR", "Please enter at least one valid IPv4 CIDR.")
                return

            if name in self.providers:
                res = QMessageBox.question(
                    self,
                    "Overwrite provider?",
                    f"Provider '{name}' already exists. Overwrite it?",
                )
                if res != QMessageBox.StandardButton.Yes:
                    return

            self.providers[name] = {
                "source": source,
                "icon": icon,
                "ipv4": cidrs,
            }
            save_ip_json(self.providers)
            self._after_providers_changed()
            QMessageBox.information(self, "Saved", f"Provider '{name}' saved to ip.json.")
            dlg.accept()

        btn_ok.clicked.connect(_apply)
        dlg.exec()

    def open_add_range_dialog(self) -> None:
        if not self.providers:
            QMessageBox.warning(self, "No providers", "ip.json does not contain any providers.")
            return

        dlg = QDialog(self)
        dlg.setWindowTitle("Add IPv4 Range to Provider")
        dlg.setModal(True)
        layout = QVBoxLayout(dlg)

        form = QGridLayout()
        form.setHorizontalSpacing(8)
        form.setVerticalSpacing(6)

        provider_combo = QComboBox()
        for prov in sorted(self.providers.keys()):
            provider_combo.addItem(icon_for_provider(self.providers, prov), prov)
        cidr_edit = QPlainTextEdit()
        cidr_edit.setPlaceholderText("IPv4 CIDR list (one per line)")

        form.addWidget(QLabel("Provider:"), 0, 0)
        form.addWidget(provider_combo, 0, 1)
        form.addWidget(QLabel("IPv4 CIDR:"), 1, 0)
        form.addWidget(cidr_edit, 1, 1)

        layout.addLayout(form)

        btns = QHBoxLayout()
        btn_ok = QPushButton("Add Range(s)")
        btn_cancel = QPushButton("Cancel")
        btns.addStretch(1)
        btns.addWidget(btn_cancel)
        btns.addWidget(btn_ok)
        layout.addLayout(btns)

        btn_cancel.clicked.connect(dlg.reject)

        def _apply():
            provider = provider_combo.currentText().strip()
            if not provider or provider not in self.providers:
                QMessageBox.warning(self, "No provider", "Please select a provider.")
                return

            cidr_text = cidr_edit.toPlainText().strip()
            cidrs = extract_ipv4_cidrs(cidr_text)
            if not cidrs:
                QMessageBox.warning(self, "Invalid IPv4 CIDR", "Please enter at least one valid IPv4 CIDR.")
                return

            existing = set(self.providers.get(provider, {}).get("ipv4", []) or [])
            added = 0
            for c in cidrs:
                if c not in existing:
                    existing.add(c)
                    added += 1
            self.providers[provider]["ipv4"] = sorted(existing)
            save_ip_json(self.providers)
            self._after_providers_changed()
            QMessageBox.information(self, "Saved", f"Added {added} new range(s) to '{provider}'.")
            dlg.accept()

        btn_ok.clicked.connect(_apply)
        dlg.exec()

    def speedtest_load_global_json(self):
        path, _ = QFileDialog.getOpenFileName(self, "Select global Xray JSON", "", "JSON Files (*.json);;All Files (*)")
        if not path:
            return
        try:
            txt = Path(path).read_text(encoding="utf-8")
            json.loads(txt)
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Failed to load/validate JSON:\n{e}")
            return
        self.speedtest_global_json_path = Path(path)
        self.speedtest_use_global_json.setChecked(True)
        self.speed_test_widget.set_global_config_text(txt, Path(path).name)

    def speedtest_load_provider_json(self):
        prov_key = None
        try:
            prov_key = self.speedtest_provider_combo.currentData(Qt.ItemDataRole.UserRole)
        except Exception:
            prov_key = None
        prov = (prov_key or self.speedtest_provider_combo.currentText().strip())
        # if text contains label suffix, keep only the provider name
        if "  [" in prov:
            prov = prov.split("  [", 1)[0].strip()
        if not prov:
            QMessageBox.warning(self, "Warning", "No provider selected.")
            return
        path, _ = QFileDialog.getOpenFileName(self, f"Select JSON for {prov}", "", "JSON Files (*.json);;All Files (*)")
        if not path:
            return
        try:
            txt = Path(path).read_text(encoding="utf-8")
            json.loads(txt)
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Failed to load/validate JSON:\n{e}")
            return

        label = Path(path).name
        self._speedtest_provider_json_labels[prov] = label
        # refresh combo text to show the label
        self._rebuild_speedtest_provider_combo()
        # keep current selection on the same provider
        for i in range(self.speedtest_provider_combo.count()):
            if self.speedtest_provider_combo.itemData(i, Qt.ItemDataRole.UserRole) == prov:
                self.speedtest_provider_combo.setCurrentIndex(i)
                break

        self.speedtest_provider_cfg_label.setText(f"Provider config: {prov} → {label}")
        self.speed_test_widget.set_provider_config_text(prov, txt, label)

    def speedtest_load_ips_from_range(self):
        if not self.range_valid_ips:
            QMessageBox.information(self, "Nothing to load", "No working IPs in Scan Range.")
            return
        items = [(self.detect_provider_for_ip(v.ip) or v.provider, v.ip) for v in self.range_valid_ips]
        self.speed_test_widget.load_ip_items(items)
        self.tabs.setCurrentWidget(self.speed_test_widget.parentWidget())


    def speedtest_load_ips_from_scanip(self):
        if not self.ip_list:
            QMessageBox.information(self, "Nothing to load", "No IPs in Scan IP list.")
            return
        items = [(self.detect_provider_for_ip(row.ip) or row.provider, row.ip) for row in self.ip_list]
        self.speed_test_widget.load_ip_items(items)
        self.tabs.setCurrentWidget(self.speed_test_widget.parentWidget())


    def speedtest_load_ips_from_txt(self):
        path, _ = QFileDialog.getOpenFileName(self, "Open TXT (Speed Test)", "", "Text Files (*.txt);;All Files (*)")
        if not path:
            return

        # snapshot networks for thread-safe provider detection
        provider_networks = getattr(self, "_provider_networks", {}) or {}
        provider_networks = {k: list(v) for k, v in provider_networks.items()}

        def _work(worker: _ResultWorker, file_path: str, nets: Dict[str, List[ipaddress.IPv4Network]]):
            text = Path(file_path).read_text(encoding="utf-8", errors="ignore")
            ips = extract_ipv4s(text)
            if not ips:
                return []

            seen = set()
            items = []
            total = len(ips)

            # stable provider order
            prov_keys = sorted(nets.keys())

            for idx, ip in enumerate(ips, 1):
                if worker.is_cancelled():
                    return []
                if ip in seen:
                    continue
                seen.add(ip)
                prov = "custom"
                try:
                    addr = ipaddress.IPv4Address(ip)
                    for p in prov_keys:
                        for net in nets[p]:
                            if addr in net:
                                prov = p
                                raise StopIteration
                except StopIteration:
                    pass
                except Exception:
                    prov = "custom"
                items.append((prov, ip))
                if idx % 2000 == 0:
                    worker.progress.emit(idx, total)

            worker.progress.emit(total, total)
            return items

        def _done(items: List[Tuple[str, str]]):
            if not items:
                QMessageBox.information(self, "No IPs found", "No IPv4 addresses were found in the selected TXT.")
                return
            self.speed_test_widget.load_ip_items(items)
            self.tabs.setCurrentWidget(self.speed_test_widget.parentWidget())

        self._run_in_thread("Loading", "Reading TXT and preparing items…", _work, _done, path, provider_networks)

    def _collect_provider_selection(self) -> Dict[str, bool]:
        out: Dict[str, bool] = {}
        for prov, chk in (self.provider_checks or {}).items():
            try:
                out[prov] = bool(chk.isChecked())
            except Exception:
                out[prov] = False
        return out

    def _collect_range_checks(self) -> Dict[str, bool]:
        # refresh from table (source of truth)
        out: Dict[str, bool] = {}
        try:
            for r in range(self.ranges_table.rowCount()):
                chk_item = self.ranges_table.item(r, 0)
                prov_item = self.ranges_table.item(r, 1)
                cidr_item = self.ranges_table.item(r, 2)
                if not chk_item or not prov_item or not cidr_item:
                    continue
                key = f"{prov_item.text().strip()}|{cidr_item.text().strip()}"
                out[key] = (chk_item.checkState() == Qt.CheckState.Checked)
        except Exception:
            pass
        return out

    def save_all_settings(self):
        # Save UI toggles + loaded Xray JSON texts so next launch restores everything.
        try:
            settings: Dict[str, Any] = {}

            settings["providers_selected"] = self._collect_provider_selection()
            settings["range_checks"] = self._collect_range_checks()

            # Scan Range tab settings
            settings["scan_range"] = {
                "scan_mode": self.scan_mode.currentText(),
                "max_latency": self.max_latency_range.currentText(),
                "max_found": self.max_found_range.text(),
                "regex": self.regex_range.text(),
                "opt_switch_found5": bool(self.opt_switch_found5.isChecked()),
                "opt_switch_3min": bool(self.opt_switch_3min.isChecked()),
                "opt_switch_10": bool(self.opt_switch_10.isChecked()),
                "opt_switch_30": bool(self.opt_switch_30.isChecked()),
                "opt_switch_50": bool(self.opt_switch_50.isChecked()),
                "opt_focus_productive": bool(self.opt_focus_productive.isChecked()),
                "opt_move_first_success": bool(getattr(self, "opt_move_first_success", QCheckBox()).isChecked()) if hasattr(self, "opt_move_first_success") else False,
            }

            # Scan IP tab settings
            settings["scan_ip"] = {
                "max_latency": self.max_latency_ip.currentText(),
                "sort_latency": bool(self.chk_sort_latency.isChecked()),
            }

            # Speed Test settings + JSON configs (store text)
            st = {
                "use_global": bool(self.speedtest_use_global_json.isChecked()),
                "use_per_provider": bool(self.speedtest_use_per_provider.isChecked()),
                "global_json_label": str(getattr(self.speed_test_widget, "config_status_label", QLabel()).text()),
                "global_json_text": str(getattr(self.speed_test_widget, "_global_config_text", "") or ""),
                "provider_json_labels": dict(self._speedtest_provider_json_labels or {}),
                "provider_json_texts": dict(getattr(self.speed_test_widget, "_provider_configs", {}) or {}),
                "socket_timeout_ms": int(self.speed_test_widget.spin_socket_timeout_ms.value()),
                "proxy_ready_deadline_sec": int(self.speed_test_widget.spin_proxy_deadline_sec.value()),
                "dl_size_mb": int(getattr(self.speed_test_widget, "combo_dl_size", QComboBox()).currentData() or DEFAULT_DL_SIZE_MB),
                "ul_size_mb": int(getattr(self.speed_test_widget, "combo_ul_size", QComboBox()).currentData() or DEFAULT_UL_SIZE_MB),
                "dl_connect_timeout": int(getattr(self.speed_test_widget, "spin_dl_connect", QSpinBox()).value() or int(DEFAULT_DL_CONNECT_TO)),
                "dl_read_timeout": int(getattr(self.speed_test_widget, "spin_dl_read", QSpinBox()).value() or int(DEFAULT_DL_READ_TO)),
                "ul_connect_timeout": int(getattr(self.speed_test_widget, "spin_ul_connect", QSpinBox()).value() or int(DEFAULT_UL_CONNECT_TO)),
                "ul_read_timeout": int(getattr(self.speed_test_widget, "spin_ul_read", QSpinBox()).value() or int(DEFAULT_UL_READ_TO)),
                "test_mode": str(getattr(self.speed_test_widget, "combo_test_mode", QComboBox()).currentData() or "ping_only"),
                "ping_url": str(getattr(self.speed_test_widget, "edit_ping_url", QLineEdit()).text() or ""),
                "download_url": str(getattr(self.speed_test_widget, "edit_download_url", QLineEdit()).text() or ""),
                "upload_url": str(getattr(self.speed_test_widget, "edit_upload_url", QLineEdit()).text() or ""),
                "dl_time_limit_enabled": bool(getattr(self.speed_test_widget, "chk_dl_time_limit", QCheckBox()).isChecked() if hasattr(self.speed_test_widget, "chk_dl_time_limit") else True),
                "dl_time_limit_seconds": int(getattr(self.speed_test_widget, "spin_dl_time_seconds", QSpinBox()).value() if hasattr(self.speed_test_widget, "spin_dl_time_seconds") else 5),
            }
            settings["speedtest"] = st

            p = app_settings_path()
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(json.dumps(settings, ensure_ascii=False, indent=2), encoding="utf-8")
            QMessageBox.information(self, "Saved", f"All settings saved to:\n{app_settings_path()}")
        except Exception as e:
            QMessageBox.warning(self, "Save failed", str(e))

    def load_all_settings(self):
        p = app_settings_path()
        if not p.exists():
            return
        try:
            settings = json.loads(p.read_text(encoding="utf-8"))
        except Exception:
            return

        # provider checkbox selection
        sel = settings.get("providers_selected", {})
        if isinstance(sel, dict):
            for prov, chk in (self.provider_checks or {}).items():
                if prov in sel:
                    try:
                        chk.setChecked(bool(sel.get(prov)))
                    except Exception:
                        pass

        # range check states
        rng = settings.get("range_checks", {})
        if isinstance(rng, dict):
            self.range_checks = dict(rng)
            try:
                # temporarily block signals to avoid noisy refresh
                self.ranges_table.blockSignals(True)
                for r in range(self.ranges_table.rowCount()):
                    chk_item = self.ranges_table.item(r, 0)
                    prov_item = self.ranges_table.item(r, 1)
                    cidr_item = self.ranges_table.item(r, 2)
                    if not chk_item or not prov_item or not cidr_item:
                        continue
                    key = f"{prov_item.text().strip()}|{cidr_item.text().strip()}"
                    if key in rng:
                        chk_item.setCheckState(Qt.CheckState.Checked if rng.get(key) else Qt.CheckState.Unchecked)
                self.ranges_table.blockSignals(False)
            except Exception:
                try:
                    self.ranges_table.blockSignals(False)
                except Exception:
                    pass

        # Scan Range settings
        sr = settings.get("scan_range", {})
        if isinstance(sr, dict):
            try:
                if sr.get("scan_mode"):
                    self.scan_mode.setCurrentText(str(sr.get("scan_mode")))
                if sr.get("max_latency"):
                    self.max_latency_range.setCurrentText(str(sr.get("max_latency")))
                self.max_found_range.setText(str(sr.get("max_found", "")))
                self.regex_range.setText(str(sr.get("regex", "")))

                for name in (
                    "opt_switch_found5", "opt_switch_3min", "opt_switch_10",
                    "opt_switch_30", "opt_switch_50", "opt_focus_productive",
                ):
                    w = getattr(self, name, None)
                    if w is not None and hasattr(w, "setChecked"):
                        w.setChecked(bool(sr.get(name, False)))

                if hasattr(self, "opt_move_first_success") and "opt_move_first_success" in sr:
                    try:
                        self.opt_move_first_success.setChecked(bool(sr.get("opt_move_first_success")))
                    except Exception:
                        pass
            except Exception:
                pass

        # Scan IP settings
        si = settings.get("scan_ip", {})
        if isinstance(si, dict):
            try:
                if si.get("max_latency"):
                    self.max_latency_ip.setCurrentText(str(si.get("max_latency")))
                self.chk_sort_latency.setChecked(bool(si.get("sort_latency", False)))
            except Exception:
                pass

        # Speed Test settings + restore JSONs
        st = settings.get("speedtest", {})
        if isinstance(st, dict):
            try:
                use_global = bool(st.get("use_global", True))
                use_per = bool(st.get("use_per_provider", False))
                if use_per:
                    self.speedtest_use_per_provider.setChecked(True)
                else:
                    self.speedtest_use_global_json.setChecked(True)

                # restore embedded widget knobs
                try:
                    self.speed_test_widget.spin_socket_timeout_ms.setValue(int(st.get("socket_timeout_ms", 1000)))
                    self.speed_test_widget.spin_proxy_deadline_sec.setValue(int(st.get("proxy_ready_deadline_sec", 5)))

                    # HTTP speed-test knobs
                    if hasattr(self.speed_test_widget, "combo_dl_size"):
                        dl = int(st.get("dl_size_mb", DEFAULT_DL_SIZE_MB))
                        idx = self.speed_test_widget.combo_dl_size.findData(dl)
                        if idx >= 0:
                            self.speed_test_widget.combo_dl_size.setCurrentIndex(idx)
                    if hasattr(self.speed_test_widget, "combo_ul_size"):
                        ul = int(st.get("ul_size_mb", DEFAULT_UL_SIZE_MB))
                        idx = self.speed_test_widget.combo_ul_size.findData(ul)
                        if idx >= 0:
                            self.speed_test_widget.combo_ul_size.setCurrentIndex(idx)
                    if hasattr(self.speed_test_widget, "spin_dl_connect"):
                        self.speed_test_widget.spin_dl_connect.setValue(int(st.get("dl_connect_timeout", int(DEFAULT_DL_CONNECT_TO))))
                    if hasattr(self.speed_test_widget, "spin_dl_read"):
                        self.speed_test_widget.spin_dl_read.setValue(int(st.get("dl_read_timeout", int(DEFAULT_DL_READ_TO))))
                    if hasattr(self.speed_test_widget, "spin_ul_connect"):
                        self.speed_test_widget.spin_ul_connect.setValue(int(st.get("ul_connect_timeout", int(DEFAULT_UL_CONNECT_TO))))
                    if hasattr(self.speed_test_widget, "spin_ul_read"):
                        self.speed_test_widget.spin_ul_read.setValue(int(st.get("ul_read_timeout", int(DEFAULT_UL_READ_TO))))
                    if hasattr(self.speed_test_widget, "combo_test_mode"):
                        tm = str(st.get("test_mode", "ping_only"))
                        idx = self.speed_test_widget.combo_test_mode.findData(tm)
                        if idx >= 0:
                            self.speed_test_widget.combo_test_mode.setCurrentIndex(idx)
                    if hasattr(self.speed_test_widget, "edit_ping_url"):
                        self.speed_test_widget.edit_ping_url.setText(str(st.get("ping_url", LATENCY_URL)))
                    if hasattr(self.speed_test_widget, "edit_download_url"):
                        self.speed_test_widget.edit_download_url.setText(str(st.get("download_url", CACHEFLY_TEMPLATE)))
                    if hasattr(self.speed_test_widget, "edit_upload_url"):
                        self.speed_test_widget.edit_upload_url.setText(str(st.get("upload_url", HTTPBIN_UPLOAD_URL)))
                    if hasattr(self.speed_test_widget, "chk_dl_time_limit"):
                        self.speed_test_widget.chk_dl_time_limit.setChecked(bool(st.get("dl_time_limit_enabled", True)))
                    if hasattr(self.speed_test_widget, "spin_dl_time_seconds"):
                        self.speed_test_widget.spin_dl_time_seconds.setValue(int(st.get("dl_time_limit_seconds", 5)))
                except Exception:
                    pass

                # restore global json text
                gtxt = st.get("global_json_text") or ""
                if isinstance(gtxt, str) and gtxt.strip():
                    self.speed_test_widget.set_global_config_text(gtxt, "saved-global.json")

                # restore provider json texts + labels
                labels = st.get("provider_json_labels", {})
                if isinstance(labels, dict):
                    self._speedtest_provider_json_labels = dict(labels)

                prov_txts = st.get("provider_json_texts", {})
                if isinstance(prov_txts, dict):
                    for prov, txt in prov_txts.items():
                        if isinstance(txt, str) and txt.strip():
                            label = str(self._speedtest_provider_json_labels.get(prov) or "saved.json")
                            self.speed_test_widget.set_provider_config_text(str(prov), txt, label)

                self._rebuild_speedtest_provider_combo()
                self._on_speedtest_provider_changed()
                self._on_speedtest_json_mode_changed()
            except Exception:
                pass

        # refresh summaries after restoring checks
        try:
            self.refresh_ranges_table()
            self.refresh_ranges_summary()
        except Exception:
            pass

    
    def _rebuild_speedtest_provider_combo(self):
        self.speedtest_provider_combo.clear()
        for prov in sorted(self.providers.keys()):
            icon = icon_for_provider(self.providers, prov)
            label = (self._speedtest_provider_json_labels.get(prov) or "").strip()
            display = prov if not label else f"{prov}  [{label}]"
            self.speedtest_provider_combo.addItem(icon, display)
            # store the real provider key for later retrieval
            idx = self.speedtest_provider_combo.count() - 1
            self.speedtest_provider_combo.setItemData(idx, prov, Qt.ItemDataRole.UserRole)


    def _on_speedtest_provider_changed(self):
        # update the small label that shows which provider JSON is loaded
        prov_key = None
        try:
            prov_key = self.speedtest_provider_combo.currentData(Qt.ItemDataRole.UserRole)
        except Exception:
            prov_key = None
        prov = (prov_key or self.speedtest_provider_combo.currentText().strip())
        if "  [" in prov:
            prov = prov.split("  [", 1)[0].strip()
        if not prov:
            self.speedtest_provider_cfg_label.setText("Provider config: ---")
            return
        label = (self._speedtest_provider_json_labels.get(prov) or "").strip()
        if label:
            self.speedtest_provider_cfg_label.setText(f"Provider config: {prov} → {label}")
        else:
            self.speedtest_provider_cfg_label.setText(f"Provider config: {prov} → (not loaded)")

    def _on_speedtest_json_mode_changed(self):
        # global checkbox overrides per-provider checkbox
        use_global = bool(self.speedtest_use_global_json.isChecked())
        use_per_provider = bool(self.speedtest_use_per_provider.isChecked())

        # enable/disable per-provider controls for clarity
        self.speedtest_provider_combo.setEnabled(use_per_provider)
        self.speedtest_btn_load_provider_json.setEnabled(use_per_provider)
        self.speedtest_provider_cfg_label.setEnabled(use_per_provider)

        # tell embedded widget what to do
        try:
            self.speed_test_widget.set_use_per_provider_json(use_per_provider)
        except Exception:
            pass

    def on_scan_mode_changed(self):
        is_shuffle = (self.scan_mode.currentText() == "Shuffle (unique)")
        # In Shuffle mode, these options do not apply
        for opt in (
            self.opt_switch_found5,
            self.opt_switch_3min,
            self.opt_switch_10,
            self.opt_switch_30,
            self.opt_switch_50,
            self.opt_focus_productive,
            self.opt_move_on_success,
        ):
            opt.setEnabled(not is_shuffle)
            if is_shuffle:
                opt.setChecked(False)

    def _parse_int_or_none(self, s: str) -> Optional[int]:
        s = (s or "").strip()
        if not s:
            return None
        try:
            v = int(s)
            return v if v > 0 else None
        except Exception:
            return None

    def set_scanning_range(self, scanning: bool):
        self.btn_start_range.setEnabled(not scanning)
        self.btn_stop_range.setEnabled(scanning)
        self.scan_mode.setEnabled(not scanning)
        self.max_latency_range.setEnabled(not scanning)
        self.max_found_range.setEnabled(not scanning)
        self.regex_range.setEnabled(not scanning)
        self.btn_update.setEnabled(not scanning)
        self.btn_reload.setEnabled(not scanning)

        # auto-switch options
        for opt in (
            self.opt_switch_found5,
            self.opt_switch_3min,
            self.opt_switch_10,
            self.opt_switch_30,
            self.opt_switch_50,
            self.opt_focus_productive,
            self.opt_move_on_success,
            self.opt_send_to_ip_tab,
        ):
            opt.setEnabled(not scanning)

        self.on_scan_mode_changed()

    def start_range_scan(self):
        ranges = self.selected_ranges_for_scan()
        if not ranges:
            QMessageBox.warning(self, "No ranges selected", "Please check at least one range in the Ranges tab.")
            self.tabs.setCurrentIndex(0)
            return

        # validate regex
        ip_regex = self.regex_range.text().strip()
        if ip_regex:
            try:
                re.compile(ip_regex)
            except re.error as e:
                QMessageBox.warning(self, "Regex error", f"Invalid regex:\n{e}")
                return

        max_latency = self._parse_int_or_none(self.max_latency_range.currentText())
        if max_latency is None:
            QMessageBox.warning(self, "Input error", "Max latency must be a number.")
            return

        max_found = self._parse_int_or_none(self.max_found_range.text())

        percent = 10 if self.opt_switch_10.isChecked() else (30 if self.opt_switch_30.isChecked() else (50 if self.opt_switch_50.isChecked() else None))
        minutes = 3 if self.opt_switch_3min.isChecked() else None
        found_lim = 5 if self.opt_switch_found5.isChecked() else None

        mode_txt = self.scan_mode.currentText()
        scan_mode = "sequential" if mode_txt == "Sequential" else ("random" if mode_txt == "Random" else "shuffle")

        focus = self.opt_focus_productive.isChecked()
        move_on_first_success = self.opt_move_on_success.isChecked()

        # reset results
        self.range_valid_ips.clear()
        self.range_found_counts.clear()
        self.range_found_total_label.setText("Found: 0 (total)")
        self.range_found_by_provider_label.setText("By provider: -")
        self.range_res_model.set_rows([])
        self.btn_export_range_csv.setEnabled(False)
        self.btn_export_range_json.setEnabled(False)
        self.btn_save_range_success.setEnabled(False)
        self.range_test_no_label.setText("Test: 0")
        self.range_current_ip_label.setText("0.0.0.0")
        self.range_try_char_label.setText("Try: •")
        self.range_latency_label.setText("Latency: 0 ms")
        self.range_current_ip_label.setStyleSheet("")
        self.lbl_scan_range_status.setText("Scanning...")

        self.range_worker = RangeScannerWorker(
            ranges=ranges,
            scan_mode=scan_mode,
            max_latency=max_latency,
            max_found=max_found,
            ip_regex=ip_regex,
            switch_after_minutes=minutes,
            switch_after_percent=percent,
            switch_after_found=found_lim,
            focus_productive=focus,
            move_on_first_success=move_on_first_success,
        )
        self.range_worker.progress.connect(self.on_range_progress)
        self.range_worker.found.connect(self.on_range_found)
        self.range_worker.status.connect(self.lbl_scan_range_status.setText)
        self.range_worker.errored.connect(self.on_range_error)
        self.range_worker.finished_ok.connect(self.on_range_finished)

        self.set_scanning_range(True)
        self.range_worker.start()

    def stop_range_scan(self):
        if self.range_worker is not None:
            self.range_worker.stop()
        self.btn_stop_range.setEnabled(False)
        self.lbl_scan_range_status.setText("Stopping...")

    def on_range_progress(self, test_no: int, ip: str, try_char: str, current_latency: int, color: str):
        self.range_test_no_label.setText(f"Test: {test_no}")
        self.range_current_ip_label.setText(ip)
        self.range_try_char_label.setText(f"Try: {try_char or '•'}")
        self.range_latency_label.setText(f"Latency: {current_latency} ms")

        if color == "red":
            self.range_current_ip_label.setStyleSheet("color: rgb(255, 107, 107); font-weight: 600;")
        else:
            self.range_current_ip_label.setStyleSheet("color: rgb(81, 207, 102); font-weight: 600;")

    def on_range_found(self, provider: str, ip: str, latency: int):
        self.range_valid_ips.append(ValidIP(latency=latency, ip=ip, provider=provider))
        self.range_valid_ips.sort()

        self.range_found_counts[provider] = self.range_found_counts.get(provider, 0) + 1
        total_found = sum(self.range_found_counts.values())
        self.range_found_total_label.setText(f"Found: {total_found} (total)")
        parts = [f"{k}:{self.range_found_counts[k]}" for k in sorted(self.range_found_counts.keys())]
        self.range_found_by_provider_label.setText("By provider: " + (" | ".join(parts) if parts else "-"))

        max_lat = self._parse_int_or_none(self.max_latency_range.currentText()) or 1000
        try:
            self.range_res_model.set_providers(self.providers)
            self.range_res_model.set_max_latency(max_lat)
            self.range_res_model.set_rows(list(self.range_valid_ips))
        except Exception:
            pass

        self.btn_export_range_csv.setEnabled(True)
        self.btn_export_range_json.setEnabled(True)
        self.btn_save_range_success.setEnabled(True)

        # Send to Scan IP list automatically (unique)
        if self.opt_send_to_ip_tab.isChecked():
            self.add_ip_to_list(ip, provider)
            self.refresh_ip_table()

        # Send to Scan IP list automatically (unique)
        if self.opt_send_to_ip_tab.isChecked():
            self.add_ip_to_list(ip, provider)
            self.refresh_ip_table()

    def on_range_error(self, msg: str):
        QMessageBox.critical(self, "Range scan error", msg)

    def on_range_finished(self):
        self.set_scanning_range(False)
        self.btn_stop_range.setEnabled(False)
        self.range_try_char_label.setText("Try: •")
        if self.lbl_scan_range_status.text().strip().lower() == "scanning...":
            self.lbl_scan_range_status.setText("Finished.")

    def on_range_result_cell_clicked(self, row: int, col: int):
        if col == 1:
            try:
                ip = self.range_res_model.data(self.range_res_model.index(row, 1), Qt.ItemDataRole.DisplayRole)
                if ip:
                    QApplication.clipboard().setText(str(ip))
                    self.statusBar().showMessage("Copied to clipboard", 1500)
            except Exception:
                pass

    def open_scan_range_settings(self) -> None:
        try:
            if hasattr(self, "scan_range_settings_dialog") and self.scan_range_settings_dialog is not None:
                self.scan_range_settings_dialog.exec()
        except Exception:
            pass

    def open_tools_cidr_dialog(self) -> None:
        try:
            if hasattr(self, "tools_cidr_dialog") and self.tools_cidr_dialog is not None:
                self.tools_cidr_dialog.exec()
        except Exception:
            pass

    def open_tools_ipcfg_dialog(self) -> None:
        try:
            if hasattr(self, "tools_ipcfg_dialog") and self.tools_ipcfg_dialog is not None:
                self.tools_ipcfg_dialog.exec()
        except Exception:
            pass

    def _range_table_context_menu(self, pos: QPoint):
        index = self.range_res_table.indexAt(pos)
        if not index.isValid():
            return
        row = index.row()
        menu = QMenu(self)
        act_copy = QAction("Copy IP", self)
        act_copy.triggered.connect(lambda: self._copy_range_ip_from_row(row))
        menu.addAction(act_copy)
        menu.exec(self.range_res_table.viewport().mapToGlobal(pos))

    def _copy_range_ip_from_row(self, row: int):
        try:
            ip = self.range_res_model.data(self.range_res_model.index(row, 1), Qt.ItemDataRole.DisplayRole)
            if ip:
                QApplication.clipboard().setText(str(ip))
                self.statusBar().showMessage("Copied to clipboard", 1500)
        except Exception:
            pass

    def _ranges_table_context_menu(self, pos: QPoint):
        index = self.ranges_table.indexAt(pos)
        if not index.isValid():
            return
        row = index.row()
        menu = QMenu(self)
        act_edit = QAction("Edit Provider / CIDR", self)
        act_edit.triggered.connect(lambda: self._edit_ranges_row(row))
        menu.addAction(act_edit)
        act_delete = QAction("Delete Range", self)
        act_delete.triggered.connect(lambda: self._delete_ranges_row(row))
        menu.addAction(act_delete)
        menu.exec(self.ranges_table.viewport().mapToGlobal(pos))

    def _edit_ranges_row(self, row: int) -> None:
        try:
            if row < 0:
                return
            prov = self.ranges_model.data(self.ranges_model.index(row, 1), Qt.ItemDataRole.DisplayRole) or ""
            cidr = self.ranges_model.data(self.ranges_model.index(row, 2), Qt.ItemDataRole.DisplayRole) or ""
            checked = self.ranges_model.data(self.ranges_model.index(row, 0), Qt.ItemDataRole.CheckStateRole) == Qt.CheckState.Checked

            dlg = QDialog(self)
            dlg.setWindowTitle("Edit Range")
            dlg.setModal(True)
            layout = QVBoxLayout(dlg)

            form = QGridLayout()
            form.setHorizontalSpacing(8)
            form.setVerticalSpacing(6)

            provider_combo = QComboBox()
            provider_combo.setEditable(True)
            for p in sorted(self.providers.keys()):
                provider_combo.addItem(icon_for_provider(self.providers, p), p)
            provider_combo.setCurrentText(str(prov))

            cidr_edit = QLineEdit(str(cidr))

            form.addWidget(QLabel("Provider:"), 0, 0)
            form.addWidget(provider_combo, 0, 1)
            form.addWidget(QLabel("IPv4 CIDR:"), 1, 0)
            form.addWidget(cidr_edit, 1, 1)
            layout.addLayout(form)

            btns = QHBoxLayout()
            btn_ok = QPushButton("Save")
            btn_cancel = QPushButton("Cancel")
            btns.addStretch(1)
            btns.addWidget(btn_cancel)
            btns.addWidget(btn_ok)
            layout.addLayout(btns)

            btn_cancel.clicked.connect(dlg.reject)

            def _apply():
                new_provider = provider_combo.currentText().strip()
                new_cidr = cidr_edit.text().strip()
                if not new_provider:
                    QMessageBox.warning(self, "Invalid provider", "Please enter a provider name.")
                    return
                if not is_valid_ipv4_cidr(new_cidr):
                    QMessageBox.warning(self, "Invalid CIDR", "Please enter a valid IPv4 CIDR.")
                    return

                if new_provider not in self.providers:
                    self.providers[new_provider] = {"source": "", "icon": "", "ipv4": []}

                # remove old
                if prov in self.providers:
                    old_list = [x for x in (self.providers[prov].get("ipv4", []) or []) if x != str(cidr)]
                    self.providers[prov]["ipv4"] = old_list

                # add new
                cur = set(self.providers[new_provider].get("ipv4", []) or [])
                cur.add(new_cidr)
                self.providers[new_provider]["ipv4"] = sorted(cur)

                # update selection state
                old_key = f"{prov}|{cidr}"
                if old_key in self.range_checks:
                    del self.range_checks[old_key]
                self.range_checks[f"{new_provider}|{new_cidr}"] = bool(checked)

                save_ip_json(self.providers)
                self._after_providers_changed()
                dlg.accept()

            btn_ok.clicked.connect(_apply)
            dlg.exec()
        except Exception:
            pass

    def _delete_ranges_row(self, row: int) -> None:
        try:
            if row < 0:
                return
            prov = self.ranges_model.data(self.ranges_model.index(row, 1), Qt.ItemDataRole.DisplayRole) or ""
            cidr = self.ranges_model.data(self.ranges_model.index(row, 2), Qt.ItemDataRole.DisplayRole) or ""
            res = QMessageBox.question(self, "Delete Range", f"Remove {prov} {cidr}?")
            if res != QMessageBox.StandardButton.Yes:
                return
            if prov in self.providers:
                self.providers[prov]["ipv4"] = [x for x in (self.providers[prov].get("ipv4", []) or []) if x != str(cidr)]
            key = f"{prov}|{cidr}"
            if key in self.range_checks:
                del self.range_checks[key]
            save_ip_json(self.providers)
            self._after_providers_changed()
        except Exception:
            pass

    def export_range_results(self, fmt: str):
        if not self.range_valid_ips:
            return
        default_name = f"range_working_ips.{fmt}"
        path, _ = QFileDialog.getSaveFileName(self, "Save results", default_name, "All Files (*)")
        if not path:
            return
        try:
            if fmt == "csv":
                lines = ["provider,ip,latency_ms"]
                for v in self.range_valid_ips:
                    lines.append(f"{v.provider},{v.ip},{v.latency}")
                Path(path).write_text("\n".join(lines), encoding="utf-8")
            else:
                data = [{"provider": v.provider, "ip": v.ip, "latency_ms": v.latency} for v in self.range_valid_ips]
                Path(path).write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
            QMessageBox.information(self, "Saved", "File saved successfully.")
        except Exception as e:
            QMessageBox.critical(self, "Save error", str(e))

    # ---------------- Scan IP ----------------

    def add_ip_to_list(self, ip: str, provider: Optional[str] = None):
        ip = (ip or "").strip()
        if not is_valid_ipv4(ip):
            return
        if provider is None or not provider.strip():
            provider = self.detect_provider_for_ip(ip)
        # unique (O(1) with a persistent set)
        if not hasattr(self, "ip_set"):
            self.ip_set = set(row.ip for row in self.ip_list)
        if ip in self.ip_set:
            return
        self.ip_list.append(IPRow(ip=ip, provider=provider))
        self.ip_set.add(ip)

    def clear_ip_list(self):
        self.ip_list.clear()
        self.ip_results.clear()
        if hasattr(self, "ip_set"):
            self.ip_set.clear()
        self.refresh_ip_table()
        self.lbl_scan_ip_status.setText("List cleared.")
        self.ip_done_label.setText("Done: 0 / 0")
        self.btn_export_ip_csv.setEnabled(False)
        self.btn_export_ip_json.setEnabled(False)
        self.btn_save_success_txt.setEnabled(False)
        self.btn_save_success_txt.setEnabled(False)

    # ---------------------- Large-job helpers (no UI freeze) ----------------------

    def _start_progress(self, title: str, label: str, maximum: int = 0) -> QProgressDialog:
        dlg = QProgressDialog(label, "Cancel", 0, maximum, self)
        dlg.setWindowTitle(title)
        dlg.setWindowModality(Qt.WindowModality.WindowModal)
        dlg.setMinimumDuration(0)
        dlg.setValue(0)
        dlg.setAutoClose(True)
        dlg.setAutoReset(True)
        return dlg

    def _run_in_thread(self, title: str, label: str, fn, on_done, *args, maximum: int = 0, **kwargs):
        """Run fn(worker, *args, **kwargs) in a QThread and call on_done(result) in UI thread."""
        dlg = self._start_progress(title, label, maximum=maximum)
        th = QThread(self)
        worker = _ResultWorker(fn, *args, **kwargs)
        worker.moveToThread(th)

        def _cancel():
            worker.request_cancel()

        dlg.canceled.connect(_cancel)
        th.started.connect(worker.run)

        def _cleanup():
            try:
                th.quit()
            except Exception:
                pass
            try:
                th.wait(1000)
            except Exception:
                pass
            worker.deleteLater()
            th.deleteLater()

        worker.progress.connect(lambda done, total: (dlg.setMaximum(total or 0), dlg.setValue(done)))
        worker.error.connect(lambda msg: (dlg.cancel(), QMessageBox.warning(self, "Error", msg), _cleanup()))
        worker.cancelled.connect(lambda: (_cleanup(),))
        worker.finished.connect(lambda res: (dlg.setValue(dlg.maximum()), on_done(res), _cleanup()))

        th.start()

    def _populate_qtablewidget_chunked(
        self,
        table,
        rows: List[Tuple],
        row_builder,
        title: str,
        label: str,
        chunk: int = 500,
    ) -> None:
        """(Legacy) Populate table in chunks. (Kept for backward compatibility; not used with QAbstractTableModel.)"""
        table.setSortingEnabled(False)
        table.setUpdatesEnabled(False)
        table.clearContents()
        table.setRowCount(len(rows))

        dlg = self._start_progress(title, label, maximum=len(rows))

        state = {"i": 0}

        def step():
            i = state["i"]
            if dlg.wasCanceled():
                table.setUpdatesEnabled(True)
                table.setSortingEnabled(True)
                return
            end = min(i + chunk, len(rows))
            for r in range(i, end):
                row_builder(r, rows[r])
            state["i"] = end
            dlg.setValue(end)
            if end >= len(rows):
                table.setUpdatesEnabled(True)
                table.setSortingEnabled(True)
                return
    


    def load_txt_ips(self):
        path, _ = QFileDialog.getOpenFileName(self, "Open TXT", "", "Text Files (*.txt);;All Files (*)")
        if not path:
            return

        def _work(worker: _ResultWorker, file_path: str):
            text = Path(file_path).read_text(encoding="utf-8", errors="ignore")
            ips = extract_ipv4s(text)
            # keep order, de-dup
            seen = set()
            out = []
            total = len(ips)
            for idx, ip in enumerate(ips, 1):
                if worker.is_cancelled():
                    return []
                if ip in seen:
                    continue
                seen.add(ip)
                out.append(ip)
                if idx % 2000 == 0:
                    worker.progress.emit(idx, total)
            worker.progress.emit(total, total)
            return out

        def _done(ips: List[str]):
            if not ips:
                return
            # add to internal list without refreshing UI each time
            added = 0
            for ip in ips:
                before = len(self.ip_list)
                self.add_ip_to_list(ip, None)
                if len(self.ip_list) > before:
                    added += 1

            # refresh table in a non-blocking way
            self.refresh_ip_table()
            self.lbl_scan_ip_status.setText(f"Loaded {len(ips)} IP(s), added {added} new.")
            self.ip_done_label.setText(f"Done: 0 / {len(self.ip_list)}")

        self._run_in_thread("Loading", "Reading TXT and extracting IPs…", _work, _done, path)


    def refresh_ip_table(self):
        view_list = self._sorted_ip_list_view()
        max_lat = self._parse_int_or_none(self.max_latency_ip.currentText()) or 1000
        try:
            self.ip_res_model.set_providers(self.providers)
            self.ip_res_model.set_ip_results_ref(self.ip_results)
            self.ip_res_model.set_max_latency(max_lat)
            self.ip_res_model.set_rows(list(view_list))
        except Exception:
            pass

    def set_scanning_ip(self, scanning: bool):
        self.btn_start_ip.setEnabled(not scanning)
        self.btn_stop_ip.setEnabled(scanning)
        self.btn_load_txt.setEnabled(not scanning)
        self.btn_load_from_range.setEnabled(not scanning)
        self.btn_clear_ip_list.setEnabled(not scanning)
        self.btn_remove_fail.setEnabled(not scanning)
        self.max_latency_ip.setEnabled(not scanning)
        self.btn_save_success_txt.setEnabled((not scanning) and any(v[0] for v in self.ip_results.values()))

    def start_ip_scan(self):
        if not self.ip_list:
            QMessageBox.warning(self, "No IPs", "Please load a TXT file or send IPs from 'Scan Range' first.")
            return

        max_latency = self._parse_int_or_none(self.max_latency_ip.currentText())
        if max_latency is None:
            QMessageBox.warning(self, "Input error", "Max latency must be a number.")
            return

        # reset results (keep list)
        self.ip_results.clear()
        self.refresh_ip_table()
        self.ip_test_no_label.setText("Test: 0")
        self.ip_current_ip_label.setText("0.0.0.0")
        self.ip_try_char_label.setText("Try: •")
        self.ip_latency_label.setText("Latency: 0 ms")
        self.ip_current_ip_label.setStyleSheet("")
        self.lbl_scan_ip_status.setText("Scanning...")
        self.btn_export_ip_csv.setEnabled(False)
        self.btn_export_ip_json.setEnabled(False)
        self.btn_save_success_txt.setEnabled(False)
        self.btn_save_success_txt.setEnabled(False)

        pairs = [(r.provider, r.ip) for r in self.ip_list]

        self.ip_worker = IPScannerWorker(pairs, max_latency=max_latency)
        self.ip_worker.progress.connect(self.on_ip_progress)
        self.ip_worker.result.connect(self.on_ip_result)
        self.ip_worker.status.connect(self.lbl_scan_ip_status.setText)
        self.ip_worker.errored.connect(self.on_ip_error)
        self.ip_worker.finished_ok.connect(self.on_ip_finished)

        self.set_scanning_ip(True)
        self.ip_worker.start()

    def stop_ip_scan(self):
        if self.ip_worker is not None:
            self.ip_worker.stop()
        self.btn_stop_ip.setEnabled(False)
        self.lbl_scan_ip_status.setText("Stopping...")

    def on_ip_progress(self, test_no: int, ip: str, try_char: str, current_latency: int, color: str):
        self.ip_test_no_label.setText(f"Test: {test_no}")
        self.ip_current_ip_label.setText(ip)
        self.ip_try_char_label.setText(f"Try: {try_char or '•'}")
        self.ip_latency_label.setText(f"Latency: {current_latency} ms")

        if color == "red":
            self.ip_current_ip_label.setStyleSheet("color: rgb(255, 107, 107); font-weight: 600;")
        else:
            self.ip_current_ip_label.setStyleSheet("color: rgb(81, 207, 102); font-weight: 600;")

    def on_ip_result(self, provider: str, ip: str, success: bool, latency: int):
        lat_store = latency if success else 0
        self.ip_results[ip] = (success, lat_store, provider)
        # enable export once we have at least one result
        self.btn_export_ip_csv.setEnabled(True)
        self.btn_export_ip_json.setEnabled(True)
        self.btn_save_success_txt.setEnabled(any(v[0] for v in self.ip_results.values()))
        self.refresh_ip_table()

    def on_ip_error(self, msg: str):
        QMessageBox.critical(self, "IP scan error", msg)

    def on_ip_finished(self):
        self.set_scanning_ip(False)
        self.btn_stop_ip.setEnabled(False)
        self.ip_try_char_label.setText("Try: •")
        if self.lbl_scan_ip_status.text().strip().lower() == "scanning...":
            self.lbl_scan_ip_status.setText("Finished.")
        self.refresh_ip_table()

    def on_ip_result_cell_clicked(self, row: int, col: int):
        if col == 1:
            try:
                ip = self.ip_res_model.data(self.ip_res_model.index(row, 1), Qt.ItemDataRole.DisplayRole)
                if ip:
                    QApplication.clipboard().setText(str(ip))
                    self.statusBar().showMessage("Copied to clipboard", 1500)
            except Exception:
                pass

    def _ip_table_context_menu(self, pos: QPoint):
        index = self.ip_res_table.indexAt(pos)
        if not index.isValid():
            return
        row = index.row()
        menu = QMenu(self)
        act_copy = QAction("Copy IP", self)
        act_copy.triggered.connect(lambda: self._copy_ip_from_row(row))
        menu.addAction(act_copy)
        menu.exec(self.ip_res_table.viewport().mapToGlobal(pos))

    def _copy_ip_from_row(self, row: int):
        try:
            ip = self.ip_res_model.data(self.ip_res_model.index(row, 1), Qt.ItemDataRole.DisplayRole)
            if ip:
                QApplication.clipboard().setText(str(ip))
                self.statusBar().showMessage("Copied to clipboard", 1500)
        except Exception:
            pass

    def export_ip_results(self, fmt: str):
        if not self.ip_list:
            return
        default_name = f"ip_scan_results.{fmt}"
        path, _ = QFileDialog.getSaveFileName(self, "Save results", default_name, "All Files (*)")
        if not path:
            return
        try:
            rows = []
            for r in self.ip_list:
                success, latency, prov = self.ip_results.get(r.ip, (False, 0, r.provider))
                status = "SUCCESS" if (r.ip in self.ip_results and success) else ("FAIL" if r.ip in self.ip_results else "PENDING")
                rows.append({"provider": r.provider, "ip": r.ip, "status": status, "latency_ms": latency if r.ip in self.ip_results else None})

            if fmt == "csv":
                lines = ["provider,ip,status,latency_ms"]
                for it in rows:
                    lat = "" if it["latency_ms"] is None else str(it["latency_ms"])
                    lines.append(f"{it['provider']},{it['ip']},{it['status']},{lat}")
                Path(path).write_text("\n".join(lines), encoding="utf-8")
            else:
                Path(path).write_text(json.dumps(rows, ensure_ascii=False, indent=2), encoding="utf-8")

            QMessageBox.information(self, "Saved", "File saved successfully.")
        except Exception as e:
            QMessageBox.critical(self, "Save error", str(e))


    def load_ips_from_scan_range(self):
        """Load working IPs from the 'Scan Range' results into the Scan IP list (unique)."""
        if not self.range_valid_ips:
            QMessageBox.information(self, "Nothing to load", "No working IPs found in 'Scan Range' yet.")
            return
        added = 0
        for v in self.range_valid_ips:
            before = len(self.ip_list)
            self.add_ip_to_list(v.ip, v.provider)
            if len(self.ip_list) > before:
                added += 1
        self.refresh_ip_table()
        self.tabs.setCurrentIndex(2)  # Scan IP tab
        self.lbl_scan_ip_status.setText(f"Loaded {added} new IP(s) from 'Scan Range'.")
        self.ip_done_label.setText(f"Done: 0 / {len(self.ip_list)}")

    def save_success_ips_txt(self):
        """Save only SUCCESS IPs as plain TXT (one IP per line)."""
        success_ips: List[str] = []
        for r in self.ip_list:
            if r.ip in self.ip_results:
                ok, latency, prov = self.ip_results[r.ip]
                if ok:
                    success_ips.append(r.ip)

        if not success_ips:
            QMessageBox.information(self, "No Successful IPs", "There are no successful IPs available to save.")
            return

        path, _ = QFileDialog.getSaveFileName(
            self, "Save SUCCESS IPs", "success_ips.txt", "Text Files (*.txt);;All Files (*)"
        )
        if not path:
            return
        try:
            Path(path).write_text("\n".join(success_ips), encoding="utf-8")
            QMessageBox.information(self, "Saved", "SUCCESS IPs saved successfully.")
        except Exception as e:
            QMessageBox.critical(self, "Save error", str(e))

    # ---------------- Scan IP helpers ----------------

    def _sorted_ip_list_view(self) -> List["IPRow"]:
        """
        When sorting is enabled:
          - SUCCESS first (lowest latency first)
          - then PENDING
          - then FAIL
        """
        if not hasattr(self, "chk_sort_latency") or not self.chk_sort_latency.isChecked():
            return list(self.ip_list)

        success_rows: List[Tuple[int, "IPRow"]] = []
        pending_rows: List["IPRow"] = []
        fail_rows: List["IPRow"] = []
        for r in self.ip_list:
            if r.ip not in self.ip_results:
                pending_rows.append(r)
                continue
            ok, lat, prov = self.ip_results.get(r.ip, (False, 0, r.provider))
            if ok:
                success_rows.append((lat, r))
            else:
                fail_rows.append(r)
        success_rows.sort(key=lambda t: t[0])
        return [r for _, r in success_rows] + pending_rows + fail_rows

    def remove_fail_ips(self):
        """Remove Failed IPs rows from Scan IP list."""
        before = len(self.ip_list)
        kept: List["IPRow"] = []
        for r in self.ip_list:
            if r.ip in self.ip_results:
                ok, lat, prov = self.ip_results[r.ip]
                if not ok:
                    continue
            kept.append(r)
        self.ip_list = kept
        alive = {r.ip for r in self.ip_list}
        self.ip_results = {k: v for k, v in self.ip_results.items() if k in alive}
        self.refresh_ip_table()
        self.lbl_scan_ip_status.setText(f"Removed {before - len(self.ip_list)} failed IP(s).")

    def _success_ips_grouped_ip(self) -> Dict[str, List[str]]:
        grouped: Dict[str, List[str]] = {}
        for r in self.ip_list:
            if r.ip in self.ip_results:
                ok, lat, prov = self.ip_results[r.ip]
                if ok:
                    grouped.setdefault(r.provider, []).append(r.ip)
        return grouped

    def show_save_success_menu_ip(self):
        grouped = self._success_ips_grouped_ip()
        total = sum(len(v) for v in grouped.values())
        if total == 0:
            QMessageBox.information(self, "No Successful IPs", "There are no successful IPs available to save.")
            return

        from PyQt6.QtWidgets import QMenu
        menu = QMenu(self)

        act_all = menu.addAction("Save All Successful IPs")
        act_all.triggered.connect(self.save_all_success_ip)

        menu.addSeparator()
        for prov in sorted(grouped.keys()):
            act = menu.addAction(f"Save All Successful IPs ({prov})")
            act.triggered.connect(lambda _=False, p=prov: self.save_success_ip_by_provider(p))

        menu.exec(self.btn_save_success_txt.mapToGlobal(self.btn_save_success_txt.rect().bottomLeft()))

    def _save_txt_list(self, ips: List[str], default_name: str):
        path, _ = QFileDialog.getSaveFileName(self, "Save IPs", default_name, "Text Files (*.txt);;All Files (*)")
        if not path:
            return
        try:
            Path(path).write_text("\n".join(ips), encoding="utf-8")
            QMessageBox.information(self, "Saved", "File saved successfully.")
        except Exception as e:
            QMessageBox.critical(self, "Save error", str(e))

    def save_all_success_ip(self):
        grouped = self._success_ips_grouped_ip()
        ips: List[str] = []
        for prov in sorted(grouped.keys()):
            ips.extend(grouped[prov])
        self._save_txt_list(ips, "success_ips_all.txt")

    def save_success_ip_by_provider(self, provider: str):
        grouped = self._success_ips_grouped_ip()
        ips = grouped.get(provider, [])
        if not ips:
            QMessageBox.information(self, "No Successful IPs", f"There are no SUCCESS IPs for {provider}.")
            return
        safe = re.sub(r"[^a-zA-Z0-9_-]+", "_", provider)
        self._save_txt_list(ips, f"success_ips_{safe}.txt")

    # ---------------- Scan Range success export ----------------

    def _success_ips_grouped_range(self) -> Dict[str, List[str]]:
        grouped: Dict[str, List[str]] = {}
        for v in self.range_valid_ips:
            grouped.setdefault(v.provider, []).append(v.ip)
        return grouped

    def show_save_success_menu_range(self):
        grouped = self._success_ips_grouped_range()
        total = sum(len(v) for v in grouped.values())
        if total == 0:
            QMessageBox.information(self, "No Successful IPs", "There are no successful IPs available to save.")
            return

        from PyQt6.QtWidgets import QMenu
        menu = QMenu(self)

        act_all = menu.addAction("Save All Successful IPs")
        act_all.triggered.connect(self.save_all_success_range)

        menu.addSeparator()
        for prov in sorted(grouped.keys()):
            act = menu.addAction(f"Save All Successful IPs ({prov})")
            act.triggered.connect(lambda _=False, p=prov: self.save_success_range_by_provider(p))

        menu.exec(self.btn_save_range_success.mapToGlobal(self.btn_save_range_success.rect().bottomLeft()))

    def save_all_success_range(self):
        grouped = self._success_ips_grouped_range()
        ips: List[str] = []
        for prov in sorted(grouped.keys()):
            ips.extend(grouped[prov])
        self._save_txt_list(ips, "range_success_ips_all.txt")

    def save_success_range_by_provider(self, provider: str):
        grouped = self._success_ips_grouped_range()
        ips = grouped.get(provider, [])
        if not ips:
            QMessageBox.information(self, "No Successful IPs", f"There are no SUCCESS IPs for {provider}.")
            return
        safe = re.sub(r"[^a-zA-Z0-9_-]+", "_", provider)
        self._save_txt_list(ips, f"range_success_ips_{safe}.txt")

    # ---------------- Tools tab ----------------


    def tools_convert_cidr(self):
        cidr = (self.tools_cidr.text() or "").strip()
        if not is_valid_ipv4_cidr(cidr):
            QMessageBox.warning(self, "Invalid CIDR", "Please enter a valid IPv4 CIDR (example: 103.244.50.0/24).")
            return

        # Safety: enormous CIDRs are not practical to materialize.
        try:
            net = ipaddress.IPv4Network(cidr, strict=False)
            total = net.num_addresses
        except Exception as e:
            QMessageBox.warning(self, "Convert CIDR failed", str(e))
            return

        MAX_IPS = 500_000  # responsive + realistic
        if total > MAX_IPS:
            QMessageBox.warning(
                self,
                "CIDR too large",
                f"This CIDR expands to {total:,} IPs which is too large to load into the UI.\n"
                f"Please use a smaller range (≤ {MAX_IPS:,} IPs).",
            )
            return

        def _work(worker: _ResultWorker, cidr_text: str):
            netw = ipaddress.IPv4Network(cidr_text, strict=False)
            out = []
            total_local = netw.num_addresses
            for idx, ip in enumerate(netw, 1):
                if worker.is_cancelled():
                    return []
                out.append(str(ip))
                if idx % 5000 == 0:
                    worker.progress.emit(idx, total_local)
            worker.progress.emit(total_local, total_local)
            return out

        def _done(ips: List[str]):
            if not ips:
                return
            self._tools_ips = ips

            try:
                self.tools_model.set_ips(ips)
            except Exception:
                pass

            self.tools_info.setText(f"Convert CIDRed {cidr} → {len(ips)} IPv4 addresses.")
            self.btn_tools_save.setEnabled(True)
            self.btn_tools_move.setEnabled(True)
            self.btn_tools_move_speed.setEnabled(True)
            try:
                self.btn_tools_clear.setEnabled(True)
            except Exception:
                pass

        self._run_in_thread("Loading", f"Expanding CIDR {cidr}…", _work, _done, cidr, maximum=0)

    def tools_clear_list(self) -> None:
        """Clear Tools tab converted IP list."""
        try:
            self.tools_model.set_rows([])
        except Exception:
            try:
                self.tools_model = ToolsIPModel([])
                self.tools_table.setModel(self.tools_model)
            except Exception:
                pass

        self.btn_tools_save.setEnabled(False)
        self.btn_tools_move.setEnabled(False)
        self.btn_tools_move_speed.setEnabled(False)
        try:
            self.btn_tools_clear.setEnabled(False)
        except Exception:
            pass

    def tools_save_txt(self):
        ips = getattr(self, "_tools_ips", [])
        if not ips:
            return
        self._save_txt_list(ips, "cidr_ips.txt")

    def tools_move_to_scanip(self):
        ips = getattr(self, "_tools_ips", [])
        if not ips:
            return
        added = 0
        for ip in ips:
            before = len(self.ip_list)
            self.add_ip_to_list(ip, None)
            if len(self.ip_list) > before:
                added += 1
        self.refresh_ip_table()
        self.tabs.setCurrentIndex(2)  # Scan IP
        self.lbl_scan_ip_status.setText(f"Added {added} IP(s) from Tools.")

    def tools_move_to_speedtest(self):
        ips = getattr(self, "_tools_ips", [])
        if not ips:
            return
        items = []
        seen = set()
        for ip in ips:
            if ip in seen:
                continue
            seen.add(ip)
            prov = self.detect_provider_for_ip(ip)
            items.append((prov, ip))
        self.speed_test_widget.load_ip_items(items)
        # switch to Speed Test tab
        try:
            idx = self.tabs.indexOf(self.speed_test_widget.parentWidget())
            if idx >= 0:
                self.tabs.setCurrentIndex(idx)
        except Exception:
            pass

    # ---------------- IP to Config (Tools) ----------------
    def tools_ipcfg_load_from_speedtest(self):
        try:
            items = getattr(self.speed_test_widget, "_batch_ips", [])
            ips = [addr for _prov, addr in (items or []) if addr]
            self.ipcfg_input.setPlainText("\n".join(ips))
            self.ipcfg_loaded_label.setText(f"Loaded: {len(ips)}")
        except Exception:
            pass

    def tools_ipcfg_load_from_scanip(self):
        try:
            ips = [r.ip for r in (self.ip_list or []) if getattr(r, "ip", None)]
            self.ipcfg_input.setPlainText("\n".join(ips))
            self.ipcfg_loaded_label.setText(f"Loaded: {len(ips)}")
        except Exception:
            pass

    def tools_ipcfg_load_from_txt(self):
        file_path, _ = QFileDialog.getOpenFileName(self, "Select IP List (TXT)", "", "Text Files (*.txt);;All Files (*)")
        if not file_path:
            return
        try:
            lines = Path(file_path).read_text(encoding="utf-8").splitlines()
            ips = [ln.strip() for ln in lines if ln.strip()]
            self.ipcfg_input.setPlainText("\n".join(ips))
            self.ipcfg_loaded_label.setText(f"Loaded: {len(ips)}")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Failed to read file:\n{e}")

    def tools_ipcfg_generate(self):
        tmpl = (self.ipcfg_template.text() or "").strip()
        if not tmpl:
            QMessageBox.warning(self, "Template missing", "Please paste a vless/vmess template URL.")
            return
        ips = [ln.strip() for ln in (self.ipcfg_input.toPlainText() or "").splitlines() if ln.strip()]
        if not ips:
            QMessageBox.warning(self, "No IPs", "Please provide at least one IP.")
            return
        out = [self._apply_ip_to_template(tmpl, ip) for ip in ips]
        self.ipcfg_output.setPlainText("\n".join(out))

    def tools_ipcfg_copy(self):
        text = self.ipcfg_output.toPlainText()
        if text.strip():
            QGuiApplication.clipboard().setText(text)

    def tools_ipcfg_save(self):
        text = self.ipcfg_output.toPlainText()
        if not text.strip():
            return
        save_path, _ = QFileDialog.getSaveFileName(self, "Save Configs (TXT)", "configs.txt", "Text Files (*.txt);;All Files (*)")
        if not save_path:
            return
        try:
            Path(save_path).write_text(text, encoding="utf-8")
            QMessageBox.information(self, "Saved", f"Saved configs to:\n{save_path}")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Failed to save file:\n{e}")

    def _apply_ip_to_template(self, tmpl: str, ip: str) -> str:
        if "[ip]" in tmpl:
            return tmpl.replace("[ip]", ip)

        out = tmpl
        # Replace host between '@' and ':' if present
        try:
            at_idx = out.find("@")
            colon_idx = out.find(":", at_idx + 1) if at_idx >= 0 else -1
            if at_idx >= 0 and colon_idx > at_idx:
                out = out[:at_idx + 1] + ip + out[colon_idx:]
        except Exception:
            pass

        # Replace or append in fragment after '#'
        try:
            if "#" in out:
                base, frag = out.split("#", 1)
                if ip not in frag:
                    if "+" in frag:
                        frag = frag.rsplit("+", 1)[0] + "+" + ip
                    else:
                        frag = frag + "+" + ip
                out = base + "#" + frag
        except Exception:
            pass

        return out

    def on_tools_cell_clicked(self, index):
        try:
            row = index.row() if hasattr(index, "row") else int(index)
            ip = self.tools_model.data(self.tools_model.index(row, 0), Qt.ItemDataRole.DisplayRole)
            if ip:
                QApplication.clipboard().setText(str(ip))
                self.statusBar().showMessage("Copied to clipboard", 1500)
        except Exception:
            pass


    # ---------------- Misc ----------------

    def on_ip_result_cell_clicked(self, row: int, col: int):
        if col == 1:
            try:
                ip = self.ip_res_model.data(self.ip_res_model.index(row, 1), Qt.ItemDataRole.DisplayRole)
                if ip:
                    QApplication.clipboard().setText(str(ip))
                    self.statusBar().showMessage("Copied to clipboard", 1500)
            except Exception:
                pass


def main():
    # Windows taskbar icon fix (especially for PyInstaller)
    if sys.platform.startswith('win'):
        try:
            import ctypes
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID('FarhadUK.IPCleanScanner')
        except Exception:
            pass
    app = QApplication(sys.argv)
    icon = load_app_icon()
    if icon is not None and hasattr(icon, 'isNull') and not icon.isNull():
        app.setWindowIcon(icon)

    apply_dark_theme(app)

    win = MainWindow()
    if icon is not None and hasattr(icon, 'isNull') and not icon.isNull():
        win.setWindowIcon(icon)
    win.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
