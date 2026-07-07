import os
import re
import sys
import csv
import time
import threading
import subprocess
from datetime import datetime, timedelta

import requests
from google.cloud import bigquery

from selenium import webdriver
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.support.ui import WebDriverWait

from PySide6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QLabel, QComboBox, QSpinBox, QPushButton, QTextEdit, QMessageBox,
    QCheckBox, QLineEdit
)
from PySide6.QtCore import QTimer, Signal, QObject, Qt
from PySide6.QtGui import QFont, QTextCursor, QIcon, QColor, QPainter, QPalette

# ==========================
# CONFIG — OOT
# ==========================
BASE            = "https://envios.adminml.com"
METRICS_PAGE    = f"{BASE}/logistics/ops-clock/metrics"
API_BASE        = f"{BASE}/logistics/ops-clock/api/metrics"

PROFILE_DIR = os.path.join(
    os.environ.get("LOCALAPPDATA", os.path.expanduser("~")),
    "OOT_chrome_profile"
)
OOT_OUT_DIR  = r"G:\Drives compartilhados\UTR_OTR\Outontime"
OOT_OUT_FILE = "out_on_time.csv"

DEFAULT_SERVICE_CENTER  = "SPA1"
DEFAULT_INTERVALO_SEG   = 60
MIN_INTERVALO_SEG       = 10
MAX_INTERVALO_SEG       = 3600

SERVICE_CENTERS = [
    "SAL1","SAM1","SBA2","SBA3","SBA4","SBA7","SCE1",
    "SDF1","SDF2","SGO1","SGO2","SJP1","SMN1","SMR1",
    "SMR2","SMS1","SMS2","SPA1","SPE1","SPI1","SRD1",
    "SRD2","SRN1","SSE1","STO1","STO2",
]

STATUS_MAP = {
    "ontime":       "NO PRAZO", "on_time":      "NO PRAZO",
    "delayed":      "ATRASADA", "late":          "ATRASADA",
    "pending":      "PENDENTE", "not_dispatched":"PENDENTE",
    "undispatched": "PENDENTE",
}

# CONFIG — ADUANA
ADUANA_OUT_DIR  = r"G:\Drives compartilhados\UTR_OTR\Aduana"
ADUANA_OUT_FILE = "Aduana_audits.csv"
ADUANA_OUT_PATH = os.path.join(ADUANA_OUT_DIR, ADUANA_OUT_FILE)

# Path da API de auditorias — editável na UI caso o endpoint mude
ADUANA_API_PATH_DEFAULT = (
    "/logistics/audit/api/audits/search"
    "?auditType=driver"
    "&auditStatus=finished,in_progress,canceled,pending"
    "&process=ad_hoc,automatic,on_demand"
    "&unitStatus=leftover,audited,damaged,missing"
    "&timezone=America%2FBelem"
)

os.makedirs(OOT_OUT_DIR,    exist_ok=True)
os.makedirs(ADUANA_OUT_DIR, exist_ok=True)

scraping_lock = threading.Lock()
aduana_lock   = threading.Lock()

# ==========================
# PALETA
# ==========================
ML_YELLOW = "#FFE600"
ML_NAVY   = "#1A2355"
ML_GREEN  = "#00A650"
ML_ORANGE = "#E8620A"
ML_BG     = "#EFEFEA"
ML_CARD   = "#FFFFFF"
ML_BORDER = "#D4D4CC"
ML_MUTED  = "#888880"
ML_FIELD  = "#F5F5F0"
ML_LOGBG  = "#FAFAF7"
ML_LOGBDR = "#E0E0D8"

# ==========================
# Helpers — comuns
# ==========================
def now_str() -> str:
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")

# ==========================
# Helpers — OOT
# ==========================
def map_estado(status: str) -> str:
    if not status:
        return ""
    return STATUS_MAP.get(status.lower(), status.upper())

def am_from_today(local_dt: datetime) -> str:
    return f"AM{local_dt.weekday() + 2}"

def build_cycle_id(facility: str, local_dt: datetime) -> str:
    return f"{facility}_{local_dt.strftime('%Y%m%d')}_{am_from_today(local_dt)}_0"

def iso_to_local_str(iso_str: str) -> str:
    if not iso_str:
        return ""
    s = iso_str.strip()
    if s.startswith("0001-01-01") or s.startswith("0000-01-01"):
        return ""
    if s.endswith("Z"):
        s = s[:-1] + "+00:00"
    try:
        dt = datetime.fromisoformat(s)
    except ValueError:
        return iso_str
    if dt.tzinfo is None:
        return dt.strftime("%Y-%m-%d %H:%M:%S")
    return dt.astimezone().strftime("%Y-%m-%d %H:%M:%S")

# ==========================
# Helpers — Aduana
# ==========================

def _parse_dt(s):
    if not s:
        return None
    return datetime.fromisoformat(s.replace("Z", "+00:00"))

def _audit_minutes(a: dict):
    started  = _parse_dt(a.get("started_at"))
    finished = _parse_dt(a.get("finished_at"))
    if not started or not finished:
        return None
    return int((finished - started).total_seconds() // 60)

def _full_name(obj, first_keys, last_keys) -> str:
    if not obj:
        return ""
    first = next((obj.get(k) for k in first_keys if obj.get(k)), "") or ""
    last  = next((obj.get(k) for k in last_keys  if obj.get(k)), "") or ""
    return (first + " " + last).strip()

def _estado_label(status: str) -> str:
    s = (status or "").lower()
    return {"finished": "Concluída", "active": "Em andamento", "canceled": "Cancelada"}.get(s, s)

def _count_units(units):
    units    = units or []
    corretas = sum(1 for u in units if (u.get("status") or "").lower() == "audited")
    faltantes = sum(1 for u in units if (u.get("status") or "").lower() == "missing")
    return corretas, 0, faltantes, 0

def aduana_build_rows(audits: list) -> list:
    rows = []
    for a in audits:
        driver      = a.get("driver")      or {}
        vehicle     = a.get("vehicle")     or {}
        carrier     = a.get("carrier")     or {}
        operator    = a.get("operator")    or {}
        transporter = a.get("transporter") or {}
        corretas, a_mais, faltantes, avariadas = _count_units(a.get("units"))
        rows.append({
            "rota_id":            driver.get("route_id"),
            "motorista":          _full_name(transporter,
                                     ("preferred_first_name", "first_name"),
                                     ("preferred_last_name",  "last_name")),
            "veiculo_placa":      vehicle.get("license_plate"),
            "transportadora":     carrier.get("display_name"),
            "rep_aduana":         _full_name(operator, ("name",), ("last_name",)),
            "tempo_auditoria_min":_audit_minutes(a),
            "corretas":           corretas,
            "a_mais":             a_mais,
            "faltantes":          faltantes,
            "avariadas":          avariadas,
            "estado":             _estado_label(a.get("status")),
            "audit_id":           a.get("id"),
            "facility_id":        a.get("facility_id"),
            "created_at":         _utc_to_belem(a.get("created_at")),
            "started_at":         _utc_to_belem(a.get("started_at")),
            "finished_at":        _utc_to_belem(a.get("finished_at")),
        })
    rows.sort(key=lambda r: r.get("created_at") or "", reverse=True)
    return rows

def _utc_to_belem(s: str) -> str:
    """Converte timestamp UTC (ISO 8601) para horário de Belém (UTC-3)."""
    if not s:
        return ""
    try:
        dt = datetime.fromisoformat(s.replace("Z", "+00:00"))
        return (dt + timedelta(hours=-3)).replace(tzinfo=None).strftime("%Y-%m-%d %H:%M:%S")
    except Exception:
        return s

def aduana_write_csv(rows: list, path: str):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    cols = [
        "rota_id","motorista","veiculo_placa","transportadora","rep_aduana",
        "tempo_auditoria_min","corretas","a_mais","faltantes","avariadas",
        "estado","audit_id","facility_id","created_at","started_at","finished_at",
    ]
    tmp = path + ".tmp"
    with open(tmp, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.DictWriter(f, fieldnames=cols)
        w.writeheader()
        w.writerows(rows)
    os.replace(tmp, path)

def aduana_run_once(session: requests.Session, aduana_url: str, log_cb) -> int:
    """Chama a API de auditorias reaproveitando a sessão autenticada do OOT.
    Retorna o número de registros exportados."""
    session.headers.update({"referer": f"{BASE}/logistics/audit/driver/monitoring"})
    r = session.get(aduana_url, timeout=30)
    if r.status_code in (401, 403):
        raise RuntimeError("Sessão expirada para Aduana (401/403). Reinicie a coleta.")
    r.raise_for_status()
    rows = aduana_build_rows(r.json())
    aduana_write_csv(rows, ADUANA_OUT_PATH)
    return len(rows)

# ==========================
# Selenium + sessão OOT
# ==========================
_NO_WINDOW = subprocess.CREATE_NO_WINDOW

def _cleanup_chrome_for_profile():
    subprocess.run(
        ["taskkill", "/F", "/IM", "chromedriver.exe"],
        capture_output=True, timeout=5, creationflags=_NO_WINDOW
    )
    try:
        result = subprocess.run(
            ["wmic","process","where","name='chrome.exe'",
             "get","ProcessId,CommandLine","/format:csv"],
            capture_output=True, text=True, timeout=10, creationflags=_NO_WINDOW
        )
        for line in result.stdout.splitlines():
            if PROFILE_DIR.replace("\\","/") in line or PROFILE_DIR in line:
                pid = line.rsplit(",", 1)[-1].strip()
                if pid.isdigit():
                    subprocess.run(
                        ["taskkill", "/F", "/PID", pid],
                        capture_output=True, timeout=5, creationflags=_NO_WINDOW
                    )
    except Exception:
        pass
    for fname in ("SingletonLock","SingletonCookie","SingletonSocket"):
        p = os.path.join(PROFILE_DIR, fname)
        try:
            if os.path.exists(p):
                os.remove(p)
        except Exception:
            pass
    time.sleep(1)

def selenium_get_cookies(log_cb, headless=True):
    _cleanup_chrome_for_profile()
    opts = Options()
    opts.add_argument(rf"--user-data-dir={PROFILE_DIR}")
    opts.add_argument("--no-sandbox")
    opts.add_argument("--disable-dev-shm-usage")
    opts.add_argument("--disable-gpu")
    if headless:
        opts.add_argument("--headless=new")
        opts.add_argument("--window-size=1920,1080")
    else:
        opts.add_argument("--start-maximized")
    svc = Service()
    svc.creationflags = _NO_WINDOW
    driver = webdriver.Chrome(options=opts, service=svc)
    try:
        bv  = driver.capabilities.get("browserVersion")
        cdv = (driver.capabilities.get("chrome", {}) or {}).get("chromedriverVersion")
        log_cb(f"BrowserVersion: {bv} | ChromeDriverVersion: {cdv}")
    except Exception:
        pass
    driver.get(METRICS_PAGE)
    if headless:
        WebDriverWait(driver, 60).until(
            lambda d: "envios.adminml.com" in d.current_url
        )
        if "login.adminml.com" in driver.current_url or "auth" in driver.current_url:
            driver.quit()
            raise RuntimeError("Sessão não autenticada (caiu no login).")
        cookies = driver.get_cookies()
        driver.quit()
        return cookies
    log_cb("Janela visível aberta. Conclua o login se solicitado…")
    try:
        WebDriverWait(driver, 180).until(
            lambda d: "envios.adminml.com/logistics/ops-clock/metrics" in d.current_url
        )
    except Exception:
        cur = driver.current_url
        driver.quit()
        raise RuntimeError(f"Login não concluído a tempo. URL atual: {cur}")
    cookies = driver.get_cookies()
    driver.quit()
    return cookies

def build_session(cookies):
    s = requests.Session()
    s.headers.update({
        "accept":          "application/json, text/plain, */*",
        "referer":         METRICS_PAGE,
        "origin":          BASE,
        "accept-language": "pt-BR,pt;q=0.9",
        "cache-control":   "no-cache",
        "pragma":          "no-cache",
        "user-agent":      "Mozilla/5.0",
    })
    for c in cookies:
        s.cookies.set(c["name"], c["value"], domain=c.get("domain"), path=c.get("path", "/"))
    csrf = s.cookies.get("_csrf")
    if csrf:
        s.headers["x-csrf-token"] = csrf
    return s

def get_json(session, url, params):
    r = session.get(url, params=params, timeout=30)
    if r.status_code >= 400:
        raise RuntimeError(f"HTTP {r.status_code} em {r.url} → {r.text[:400]}")
    return r.json()

def list_waves(session, cycle_id):
    data = get_json(session, f"{API_BASE}/dispatch", {"cycleId": cycle_id})
    wm = data.get("wave_metrics", {}) or {}
    return sorted([int(k) for k in wm.keys()])

def fetch_wave_routes(session, cycle_id, wave_id: int):
    data = get_json(session, f"{API_BASE}/dispatch/wave-routes",
                    {"cycleId": cycle_id, "waveId": wave_id})
    return data.get("routes", [])

# ==========================
# BigQuery
# ==========================
_bq_client = None

def get_bq_client():
    global _bq_client
    if _bq_client is None:
        _bq_client = bigquery.Client()
    return _bq_client

def fetch_mapping_bigquery_for_route_ids(node_id: str, route_ids: list) -> dict:
    route_ids = [str(x).strip() for x in route_ids if str(x).strip()]
    if not route_ids:
        return {}
    client = get_bq_client()
    query = """
    WITH ROUTES AS (
      SELECT CAST(SHP_LG_ROUTE_ID AS STRING) AS ROUTE_ID,
             CAST(SHP_LG_DRIVER_ID AS STRING) AS DRIVER_ID, SHP_LG_INIT_DATE,
             ROW_NUMBER() OVER(PARTITION BY CAST(SHP_LG_ROUTE_ID AS STRING)
                               ORDER BY SHP_LG_INIT_DATE DESC) AS rn
      FROM `meli-bi-data.WHOWNER.LK_SHP_LG_ROUTES`
      WHERE SHP_LG_FACILITY_ID=@node_id AND SHP_LG_TYPE='last_mile'
        AND SHP_LG_ROUTE_ID IS NOT NULL AND SHP_LG_DRIVER_ID IS NOT NULL
        AND CAST(SHP_LG_ROUTE_ID AS STRING) IN UNNEST(@route_ids)
        AND DATE(SHP_LG_INIT_DATE)
            BETWEEN DATE_SUB(CURRENT_DATE("America/Sao_Paulo"),INTERVAL 7 DAY)
                AND CURRENT_DATE("America/Sao_Paulo")
    ),
    YMS AS (
      SELECT CAST((SELECT d.DRIVER_ID FROM UNNEST(t.PURPOSES) p, UNNEST(p.DRIVER) d
                   WHERE p.MILE='last_mile' LIMIT 1) AS STRING) AS DRIVER_ID,
             (SELECT v.VEHICLE_PLATE FROM UNNEST(t.VEHICLES) v LIMIT 1) AS VEHICLE_PLATE,
             t.STARTED_AT,
             CASE CAST(t.CARRIER.CARRIER_ID AS INT64)
               WHEN 59903397   THEN 'RodaCoop'        WHEN 1387994348 THEN 'BRJTransportes'
               WHEN 1070423464 THEN 'COOPMETRO'       WHEN 1726310024 THEN '50 Mais'
               WHEN 1733570264 THEN 'Envios Extra'    WHEN 2063018767 THEN 'PANTERA LOG TRAN'
               WHEN 1670870460 THEN 'JL Castro'       WHEN 17502440   THEN 'DHL'
               WHEN 1542308672 THEN 'Kangu Logistics' WHEN 164929533  THEN 'WLS CARGO'
               ELSE NULL END AS TRANSPORTADORA,
             ROW_NUMBER() OVER(
               PARTITION BY CAST((SELECT d.DRIVER_ID FROM UNNEST(t.PURPOSES) p,
                                  UNNEST(p.DRIVER) d WHERE p.MILE='last_mile' LIMIT 1) AS STRING)
               ORDER BY t.STARTED_AT DESC) AS rn
      FROM `meli-bi-data.WHOWNER.BT_YMS_JOURNEY_PLANNER` t
      WHERE t.NODE_ID=@node_id
        AND DATE(DATETIME_SUB(t.STARTED_AT,INTERVAL 3 HOUR))
            >= DATE_SUB(CURRENT_DATE("America/Sao_Paulo"),INTERVAL 1 DAY)
        AND EXISTS(SELECT 1 FROM UNNEST(t.PURPOSES) p WHERE p.MILE='last_mile')
    )
    SELECT R.ROUTE_ID, Y.TRANSPORTADORA, Y.STARTED_AT, Y.VEHICLE_PLATE
    FROM ROUTES R LEFT JOIN YMS Y ON Y.DRIVER_ID=R.DRIVER_ID AND Y.rn=1
    WHERE R.rn=1
    """
    jc = bigquery.QueryJobConfig(query_parameters=[
        bigquery.ScalarQueryParameter("node_id",   "STRING", node_id),
        bigquery.ArrayQueryParameter("route_ids",  "STRING", route_ids),
    ])
    result = client.query(query, job_config=jc).result()
    mapping = {}
    for row in result:
        rid = (row.get("ROUTE_ID") or "").strip()
        if not rid:
            continue
        sa = row.get("STARTED_AT")
        if sa:
            try:
                sl = sa.astimezone() + timedelta(hours=1)
            except Exception:
                sl = sa + timedelta(hours=1)
            sa_str = sl.strftime("%H:%M:%S")
        else:
            sa_str = ""
        mapping[rid] = {
            "Transportadoras": (row.get("TRANSPORTADORA") or "").strip(),
            "PLACA":            (row.get("VEHICLE_PLATE")  or "").strip(),
            "STARTED_AT":       sa_str,
        }
    return mapping

# ==========================
# Scraping — OOT
# ==========================
def oot_run_once(service_center_id: str, log_cb) -> str:
    cycle_id = build_cycle_id(service_center_id, datetime.now())
    try:
        cookies = selenium_get_cookies(log_cb, headless=True)
    except Exception as e:
        log_cb(f"Headless falhou ({e}). Abrindo visível para relogar…")
        cookies = selenium_get_cookies(log_cb, headless=False)
    session   = build_session(cookies)
    waves     = list_waves(session, cycle_id)
    temp_rows, route_ids = [], set()
    for w in waves:
        for item in fetch_wave_routes(session, cycle_id, w):
            rid = str(item.get("route_id") or "").strip()
            if rid:
                route_ids.add(rid)
            temp_rows.append({
                "cycle_id":               cycle_id,
                "wave_id":                str(item.get("wave_id") or w),
                "rota":                   item.get("route_name", "") or "",
                "Transportadoras":        "",
                "PLACA":                  "",
                "STARTED_AT":             "",
                "estado":                 map_estado(item.get("status")),
                "status_raw":             item.get("status", ""),
                "route_id":               rid,
                "planned_id":             item.get("planned_id", ""),
                "dispatch_time":          iso_to_local_str(item.get("dispatch_time",    "")),
                "transition_time":        iso_to_local_str(item.get("transition_time",  "")),
                "yms_gate_out":           iso_to_local_str(item.get("yms_gate_out",     "")),
                "yms_status":             item.get("yms_status", ""),
                "destination_facility_id":item.get("destination_facility_id", ""),
            })
    log_cb(f"[OOT] BigQuery: consultando {len(route_ids)} route_ids…")
    mapping = fetch_mapping_bigquery_for_route_ids(service_center_id, sorted(route_ids))
    log_cb(f"[OOT] BigQuery: retornou {len(mapping)} route_ids com dados.")
    rows = []
    for r in temp_rows:
        extra = mapping.get(r["route_id"], {})
        r["Transportadoras"] = extra.get("Transportadoras", "")
        r["PLACA"]           = extra.get("PLACA",           "")
        r["STARTED_AT"]      = extra.get("STARTED_AT",      "")
        rows.append(r)
    rows.sort(key=lambda x: (x["wave_id"], x["rota"]))
    out_csv = os.path.join(OOT_OUT_DIR, OOT_OUT_FILE)
    fields  = [
        "cycle_id","wave_id","rota","Transportadoras","PLACA","STARTED_AT",
        "estado","status_raw","route_id","planned_id",
        "dispatch_time","transition_time","yms_gate_out","yms_status",
        "destination_facility_id",
    ]
    tmp = out_csv + ".tmp"
    with open(tmp, "w", newline="", encoding="utf-8-sig") as f:
        w2 = csv.DictWriter(f, fieldnames=fields)
        w2.writeheader()
        w2.writerows(rows)
    os.replace(tmp, out_csv)
    # Retorna também a sessão autenticada para reaproveitamento pela Aduana
    return out_csv, session

# ==========================
# Signals
# ==========================
class UiSignals(QObject):
    log = Signal(str)

# ==========================
# Pulse dot
# ==========================
class PulseDot(QWidget):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setFixedSize(10, 10)
        self._running = False
        self._alpha   = 255
        self._phase   = 0.0
        self._timer   = QTimer(self)
        self._timer.setInterval(50)
        self._timer.timeout.connect(self._tick)

    def set_running(self, v: bool):
        self._running = v
        if v:
            self._timer.start()
        else:
            self._timer.stop()
            self._alpha = 255
            self.update()

    def _tick(self):
        import math
        self._phase += 0.15
        self._alpha  = int(128 + 127 * math.sin(self._phase))
        self.update()

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        color = QColor(0, 166, 80, self._alpha) if self._running else QColor(185, 185, 180, 220)
        p.setBrush(color)
        p.setPen(Qt.NoPen)
        p.drawEllipse(0, 0, 10, 10)
        p.end()

# ==========================
# Main Window
# ==========================
class OutOnTimeInterface(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Out On Time — Mercado Envios")
        self.setFixedSize(680, 860)

        self.signals = UiSignals()
        self.signals.log.connect(self._append_log)

        self.timer = QTimer(self)
        self.timer.timeout.connect(self._tick)

        self._next_run_at: datetime | None = None
        self._countdown_timer = QTimer(self)
        self._countdown_timer.setInterval(1000)
        self._countdown_timer.timeout.connect(self._update_countdown)

        self._running     = False
        self._cycle_count = 0

        # Última sessão autenticada — compartilhada com a coleta Aduana
        self._last_session: requests.Session | None = None

        self._build_ui()
        self._log(f"[OOT]    Destino CSV: {os.path.join(OOT_OUT_DIR, OOT_OUT_FILE)}")
        self._log(f"[ADUANA] Destino CSV: {ADUANA_OUT_PATH}")
        self._log("[OOT]    BigQuery usa ADC (gcloud auth application-default login).")
        self._log("[ADUANA] Autenticação via sessão Selenium do OOT (sem headers manuais).")

    # ──────────────────────────────────────────────
    # QSS helpers
    # ──────────────────────────────────────────────
    def _qss_combo(self) -> str:
        return f"""
            QComboBox {{
                background: {ML_FIELD}; color: {ML_NAVY};
                border: 1px solid {ML_BORDER}; border-radius: 7px;
                padding: 4px 30px 4px 10px;
                font-family: 'Segoe UI'; font-size: 11pt; font-weight: bold;
            }}
            QComboBox:hover {{ border-color: {ML_NAVY}; }}
            QComboBox:focus {{ border-color: {ML_NAVY}; outline: none; }}
            QComboBox::drop-down {{
                subcontrol-origin: padding; subcontrol-position: top right;
                width: 28px; border: none; background: transparent;
            }}
            QComboBox::down-arrow {{ image: none; width: 0; height: 0; }}
            QComboBox QAbstractItemView {{
                background: {ML_CARD}; border: 1px solid {ML_BORDER};
                border-radius: 6px;
                selection-background-color: {ML_YELLOW};
                selection-color: {ML_NAVY};
                padding: 4px; font-size: 10pt; outline: none;
            }}
        """

    def _qss_spinbox(self) -> str:
        return f"""
            QSpinBox {{
                background: {ML_FIELD}; color: {ML_NAVY};
                border: 1px solid {ML_BORDER}; border-radius: 7px;
                padding: 4px 6px 4px 10px;
                font-family: 'Segoe UI'; font-size: 11pt; font-weight: bold;
            }}
            QSpinBox:hover {{ border-color: {ML_NAVY}; }}
            QSpinBox:focus {{ border-color: {ML_NAVY}; outline: none; }}
            QSpinBox::up-button, QSpinBox::down-button {{
                width: 18px; background: {ML_FIELD}; border: none;
            }}
            QSpinBox::up-button   {{ subcontrol-position: top right; }}
            QSpinBox::down-button {{ subcontrol-position: bottom right; }}
            QSpinBox::up-arrow, QSpinBox::down-arrow {{ width: 0; height: 0; }}
        """

    def _qss_btn_navy(self) -> str:
        return f"""
            QPushButton {{
                background: {ML_NAVY}; color: {ML_YELLOW};
                border: none; border-radius: 7px;
                font-family: 'Segoe UI'; font-size: 10pt; font-weight: bold;
                padding: 0 14px;
            }}
            QPushButton:hover   {{ background: #10183D; }}
            QPushButton:pressed {{ background: #080F28; }}
        """

    def _qss_btn_outline(self) -> str:
        return f"""
            QPushButton {{
                background: transparent; color: {ML_NAVY};
                border: 1px solid {ML_BORDER}; border-radius: 7px;
                font-family: 'Segoe UI'; font-size: 9pt; font-weight: bold;
                padding: 0 12px;
            }}
            QPushButton:hover   {{ background: #E8E8E0; }}
            QPushButton:pressed {{ background: #D8D8D0; }}
        """

    def _qss_btn_green(self, enabled: bool) -> str:
        if enabled:
            return f"""
                QPushButton {{
                    background: {ML_GREEN}; color: #FFFFFF;
                    border: none; border-radius: 7px;
                    font-family: 'Segoe UI'; font-size: 11pt; font-weight: bold;
                }}
                QPushButton:hover   {{ background: #008040; }}
                QPushButton:pressed {{ background: #006830; }}
                QPushButton:disabled {{ background: #CCCCCC; color: #999999; }}
            """
        return f"""
            QPushButton {{
                background: #CCCCCC; color: #999999;
                border: none; border-radius: 7px;
                font-family: 'Segoe UI'; font-size: 11pt; font-weight: bold;
            }}
        """

    def _qss_btn_stop(self, enabled: bool) -> str:
        if enabled:
            return f"""
                QPushButton {{
                    background: #FFF0E8; color: {ML_ORANGE};
                    border: 1px solid #F0BEA0; border-radius: 7px;
                    font-family: 'Segoe UI'; font-size: 11pt; font-weight: bold;
                }}
                QPushButton:hover   {{ background: #FFE0CC; }}
                QPushButton:pressed {{ background: #FFD0B0; }}
            """
        return f"""
            QPushButton {{
                background: #EBEBEB; color: #BBBBBB;
                border: 1px solid {ML_BORDER}; border-radius: 7px;
                font-family: 'Segoe UI'; font-size: 11pt; font-weight: bold;
            }}
        """

    # ──────────────────────────────────────────────
    # Card factory
    # ──────────────────────────────────────────────
    def _make_card(self) -> QWidget:
        card = QWidget()
        card.setObjectName("card")
        card.setStyleSheet(f"""
            QWidget#card {{
                background: {ML_CARD};
                border: 1px solid {ML_BORDER};
                border-radius: 10px;
            }}
        """)
        lay = QVBoxLayout(card)
        lay.setContentsMargins(16, 14, 16, 14)
        lay.setSpacing(12)
        return card

    def _section_label(self, text: str) -> QLabel:
        lbl = QLabel(text)
        lbl.setFont(QFont("Segoe UI", 8))
        lbl.setStyleSheet(
            f"color:{ML_MUTED}; background:transparent; border:none; letter-spacing:1px;"
        )
        return lbl

    # ──────────────────────────────────────────────
    # Build UI
    # ──────────────────────────────────────────────
    def _build_ui(self):
        # Ícone
        if getattr(sys, "frozen", False):
            icon_path = os.path.join(sys._MEIPASS, "logo.ico")
        else:
            icon_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logo.ico")
        if os.path.exists(icon_path):
            self.setWindowIcon(QIcon(icon_path))

        central = QWidget()
        self.setCentralWidget(central)
        central.setStyleSheet(f"background: {ML_BG};")

        root = QVBoxLayout(central)
        root.setContentsMargins(0, 0, 0, 0)
        root.setSpacing(0)

        # ── Header ──────────────────────────────────
        header = QWidget()
        header.setFixedHeight(58)
        header.setStyleSheet(f"background: {ML_YELLOW};")
        h_lay = QHBoxLayout(header)
        h_lay.setContentsMargins(16, 0, 16, 0)
        h_lay.setSpacing(10)

        icon_box = QLabel("▶")
        icon_box.setFixedSize(34, 34)
        icon_box.setAlignment(Qt.AlignCenter)
        icon_box.setStyleSheet(f"""
            background: {ML_NAVY}; color: {ML_YELLOW};
            border-radius: 8px; font-size: 14px; font-weight: bold;
            padding-left: 2px;
        """)
        h_lay.addWidget(icon_box)

        title = QLabel("Out On Time — Ops Clock")
        title.setFont(QFont("Segoe UI", 13, QFont.Bold))
        title.setStyleSheet(f"color: {ML_NAVY}; background: transparent;")
        h_lay.addWidget(title)
        h_lay.addStretch()

        sub = QLabel("Mercado Envios")
        sub.setFont(QFont("Segoe UI", 9))
        sub.setStyleSheet(f"color: {ML_NAVY}; background: transparent;")
        h_lay.addWidget(sub)

        self._badge = QLabel(DEFAULT_SERVICE_CENTER)
        self._badge.setFont(QFont("Segoe UI", 11, QFont.Bold))
        self._badge.setStyleSheet(f"color: {ML_NAVY}; background: transparent;")
        h_lay.addWidget(self._badge)

        root.addWidget(header)

        # ── Body ────────────────────────────────────
        body = QWidget()
        body.setStyleSheet(f"background: {ML_BG};")
        bw_lay = QVBoxLayout(body)
        bw_lay.setContentsMargins(14, 14, 14, 8)
        bw_lay.setSpacing(10)

        # ── Card: OOT Config ─────────────────────────
        cfg_card = self._make_card()
        cfg_lay  = cfg_card.layout()

        cfg_lay.addWidget(self._section_label("OOT — CONFIGURAÇÃO"))

        fields_row = QHBoxLayout()
        fields_row.setSpacing(10)
        fields_row.setContentsMargins(0, 0, 0, 0)

        # SC selector
        sc_vbox = QVBoxLayout()
        sc_vbox.setSpacing(4)
        sc_l = QLabel("Service center")
        sc_l.setFont(QFont("Segoe UI", 9))
        sc_l.setStyleSheet(f"color:{ML_MUTED}; background:transparent; border:none;")
        sc_vbox.addWidget(sc_l)
        self.cb_sc = QComboBox()
        self.cb_sc.addItems(SERVICE_CENTERS)
        self.cb_sc.setCurrentText(DEFAULT_SERVICE_CENTER)
        self.cb_sc.setFixedHeight(38)
        self.cb_sc.setFont(QFont("Segoe UI", 11, QFont.Bold))
        self.cb_sc.setStyleSheet(self._qss_combo())
        self.cb_sc.currentTextChanged.connect(self._on_sc_changed)
        sc_vbox.addWidget(self.cb_sc)
        fields_row.addLayout(sc_vbox, 3)

        # Intervalo
        int_vbox = QVBoxLayout()
        int_vbox.setSpacing(4)
        int_l = QLabel("Intervalo (s)")
        int_l.setFont(QFont("Segoe UI", 9))
        int_l.setStyleSheet(f"color:{ML_MUTED}; background:transparent; border:none;")
        int_vbox.addWidget(int_l)
        self.spin_int = QSpinBox()
        self.spin_int.setRange(MIN_INTERVALO_SEG, MAX_INTERVALO_SEG)
        self.spin_int.setValue(DEFAULT_INTERVALO_SEG)
        self.spin_int.setFixedHeight(38)
        self.spin_int.setFont(QFont("Segoe UI", 11, QFont.Bold))
        self.spin_int.setStyleSheet(self._qss_spinbox())
        int_vbox.addWidget(self.spin_int)
        fields_row.addLayout(int_vbox, 2)

        # Botão Aplicar
        apply_vbox = QVBoxLayout()
        apply_vbox.setSpacing(4)
        apply_vbox.setAlignment(Qt.AlignBottom)
        self.btn_apply = QPushButton("Aplicar")
        self.btn_apply.setFixedHeight(38)
        self.btn_apply.setFont(QFont("Segoe UI", 10, QFont.Bold))
        self.btn_apply.setStyleSheet(self._qss_btn_navy())
        self.btn_apply.clicked.connect(self._on_aplicar)
        apply_vbox.addWidget(self.btn_apply)
        fields_row.addLayout(apply_vbox, 2)

        cfg_lay.addLayout(fields_row)
        bw_lay.addWidget(cfg_card)

        # ── Card: Aduana ─────────────────────────────
        aduana_card = self._make_card()
        aduana_lay  = aduana_card.layout()
        aduana_lay.setSpacing(8)

        # Linha 1: checkbox + status
        aduana_hdr = QHBoxLayout()
        aduana_hdr.setContentsMargins(0, 0, 0, 0)
        aduana_hdr.setSpacing(12)

        self.chk_aduana = QCheckBox("ADUANA — ATIVAR COLETA AUTOMÁTICA")
        self.chk_aduana.setFont(QFont("Segoe UI", 8, QFont.Bold))
        self.chk_aduana.setStyleSheet(f"""
            QCheckBox {{
                color: {ML_MUTED}; background: transparent;
                border: none; letter-spacing: 1px;
                font-family: 'Segoe UI'; font-size: 8pt;
            }}
            QCheckBox::indicator {{
                width: 16px; height: 16px;
                border: 1px solid {ML_BORDER};
                border-radius: 4px; background: {ML_FIELD};
            }}
            QCheckBox::indicator:checked {{
                background: {ML_NAVY}; border-color: {ML_NAVY};
            }}
        """)
        aduana_hdr.addWidget(self.chk_aduana)
        aduana_hdr.addStretch()

        self.lbl_aduana_status = QLabel("Usa sessão do OOT")
        self.lbl_aduana_status.setFont(QFont("Segoe UI", 8))
        self.lbl_aduana_status.setStyleSheet(
            f"color:{ML_MUTED}; background:transparent; border:none;"
        )
        aduana_hdr.addWidget(self.lbl_aduana_status)
        aduana_lay.addLayout(aduana_hdr)

        # Linha 2: campo de path + botão Testar
        path_row = QHBoxLayout()
        path_row.setContentsMargins(0, 0, 0, 0)
        path_row.setSpacing(8)

        path_lbl = QLabel("Path da API:")
        path_lbl.setFont(QFont("Segoe UI", 8))
        path_lbl.setStyleSheet(f"color:{ML_MUTED}; background:transparent; border:none;")
        path_row.addWidget(path_lbl)

        self.txt_aduana_path = QLineEdit(ADUANA_API_PATH_DEFAULT)
        self.txt_aduana_path.setFixedHeight(30)
        self.txt_aduana_path.setFont(QFont("Consolas", 8))
        self.txt_aduana_path.setStyleSheet(f"""
            QLineEdit {{
                background: {ML_FIELD}; color: {ML_NAVY};
                border: 1px solid {ML_BORDER}; border-radius: 6px;
                padding: 0 8px;
                font-family: 'Consolas'; font-size: 8pt;
            }}
            QLineEdit:focus {{ border-color: {ML_NAVY}; }}
        """)
        path_row.addWidget(self.txt_aduana_path, 1)

        self.btn_aduana_test = QPushButton("Testar agora")
        self.btn_aduana_test.setFixedHeight(30)
        self.btn_aduana_test.setFont(QFont("Segoe UI", 9, QFont.Bold))
        self.btn_aduana_test.setStyleSheet(self._qss_btn_outline())
        self.btn_aduana_test.clicked.connect(self._on_aduana_test)
        path_row.addWidget(self.btn_aduana_test)

        aduana_lay.addLayout(path_row)
        bw_lay.addWidget(aduana_card)

        # ── Card: Controle ───────────────────────────
        ctrl_card = self._make_card()
        ctrl_lay  = ctrl_card.layout()
        ctrl_lay.setSpacing(10)

        btns_row = QHBoxLayout()
        btns_row.setSpacing(10)

        self.btn_start = QPushButton("▶  Iniciar coleta")
        self.btn_start.setFixedHeight(44)
        self.btn_start.setFont(QFont("Segoe UI", 11, QFont.Bold))
        self.btn_start.setStyleSheet(self._qss_btn_green(True))
        self.btn_start.clicked.connect(self.start)
        btns_row.addWidget(self.btn_start, 1)

        self.btn_stop = QPushButton("◼  Finalizar")
        self.btn_stop.setFixedHeight(44)
        self.btn_stop.setEnabled(False)
        self.btn_stop.setFont(QFont("Segoe UI", 11, QFont.Bold))
        self.btn_stop.setStyleSheet(self._qss_btn_stop(False))
        self.btn_stop.clicked.connect(self.stop)
        btns_row.addWidget(self.btn_stop, 1)

        ctrl_lay.addLayout(btns_row)

        # Status bar
        status_bar = QWidget()
        status_bar.setFixedHeight(38)
        status_bar.setStyleSheet(f"""
            QWidget {{
                background: #F0F0EB;
                border: 1px solid {ML_BORDER};
                border-radius: 8px;
            }}
        """)
        sb_lay = QHBoxLayout(status_bar)
        sb_lay.setContentsMargins(12, 0, 12, 0)
        sb_lay.setSpacing(8)

        self.pulse_dot = PulseDot()
        sb_lay.addWidget(self.pulse_dot)

        self.lbl_status = QLabel("Aguardando inicialização")
        self.lbl_status.setFont(QFont("Segoe UI", 9))
        self.lbl_status.setStyleSheet(f"color:{ML_MUTED}; background:transparent; border:none;")
        sb_lay.addWidget(self.lbl_status, 1)

        self.lbl_sc_status = QLabel(DEFAULT_SERVICE_CENTER)
        self.lbl_sc_status.setFont(QFont("Segoe UI", 9, QFont.Bold))
        self.lbl_sc_status.setStyleSheet(f"color:{ML_NAVY}; background:transparent; border:none;")
        sb_lay.addWidget(self.lbl_sc_status)

        ctrl_lay.addWidget(status_bar)
        bw_lay.addWidget(ctrl_card)

        # ── Card: Log ────────────────────────────────
        log_card = self._make_card()
        log_lay  = log_card.layout()

        log_hdr = QHBoxLayout()
        log_hdr.setContentsMargins(0, 0, 0, 0)
        lbl_log = QLabel("LOG DE EVENTOS")
        lbl_log.setFont(QFont("Segoe UI", 8))
        lbl_log.setStyleSheet(
            f"color:{ML_MUTED}; background:transparent; border:none; letter-spacing:1px;"
        )
        log_hdr.addWidget(lbl_log)
        log_hdr.addStretch()

        self.btn_clear_log = QPushButton("Limpar")
        self.btn_clear_log.setFixedSize(64, 26)
        self.btn_clear_log.setFont(QFont("Segoe UI", 8))
        self.btn_clear_log.setStyleSheet(f"""
            QPushButton {{
                background: transparent; color: {ML_MUTED};
                border: 1px solid {ML_BORDER}; border-radius: 6px;
            }}
            QPushButton:hover {{ background: #E8E8E0; }}
        """)
        self.btn_clear_log.clicked.connect(lambda: self.log_area.clear())
        log_hdr.addWidget(self.btn_clear_log)
        log_lay.addLayout(log_hdr)

        self.log_area = QTextEdit()
        self.log_area.setReadOnly(True)
        self.log_area.setFont(QFont("Segoe UI", 9))
        self.log_area.setMinimumHeight(200)
        self.log_area.setStyleSheet(f"""
            QTextEdit {{
                background: {ML_LOGBG}; color: #333330;
                border: 1px solid {ML_LOGBDR}; border-radius: 8px;
                padding: 10px 12px;
                selection-background-color: {ML_YELLOW};
                selection-color: {ML_NAVY};
            }}
            QScrollBar:vertical {{
                background: {ML_BG}; width: 6px;
                border-radius: 3px; margin: 0;
            }}
            QScrollBar::handle:vertical {{
                background: #CBCBC4; border-radius: 3px; min-height: 20px;
            }}
            QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {{ height: 0; }}
        """)
        log_lay.addWidget(self.log_area)
        bw_lay.addWidget(log_card)

        root.addWidget(body, 1)

        # ── Footer ───────────────────────────────────
        footer = QWidget()
        footer.setFixedHeight(28)
        footer.setStyleSheet(f"background:{ML_BG}; border-top: 1px solid {ML_BORDER};")
        f_lay = QHBoxLayout(footer)
        f_lay.setContentsMargins(20, 0, 20, 0)
        f_lbl = QLabel(f"© Mercado Envios — Automação · SPA1 · {datetime.now().year}")
        f_lbl.setFont(QFont("Segoe UI", 8))
        f_lbl.setAlignment(Qt.AlignCenter)
        f_lbl.setStyleSheet("color: #AAAAAA; background: transparent;")
        f_lay.addWidget(f_lbl)
        root.addWidget(footer)

    # ──────────────────────────────────────────────
    # Logging
    # ──────────────────────────────────────────────
    def _append_log(self, msg: str):
        lower = msg.lower()
        # Cores por origem/severidade
        if "[aduana]" in lower:
            ts_c, msg_c = "#7C3AED", "#6D28D9"   # roxo para Aduana
        elif "erro" in lower or "error" in lower or "falhou" in lower:
            ts_c, msg_c = "#B91C1C", "#DC2626"
        elif "csv atualizado" in lower or "retornou" in lower:
            ts_c, msg_c = "#15803D", "#16A34A"
        elif "bigquery" in lower:
            ts_c, msg_c = "#1D4ED8", "#2563EB"
        elif "iniciand" in lower:
            ts_c, msg_c = "#15803D", "#166534"
        elif "finalizado" in lower or "parado" in lower:
            ts_c, msg_c = "#888880", "#666660"
        elif "github" in lower or "desativado" in lower:
            ts_c, msg_c = "#AAAAAA", "#888880"
        else:
            ts_c, msg_c = "#AAAAAA", "#444440"

        m = re.match(r"^(\[.*?\])\s*(.*)", msg, re.DOTALL)
        if m:
            ts   = m.group(1).replace("&","&amp;").replace("<","&lt;").replace(">","&gt;")
            body = m.group(2).replace("&","&amp;").replace("<","&lt;").replace(">","&gt;")
            html = (
                f'<span style="color:{ts_c};font-family:Segoe UI;font-size:9pt">{ts}</span>'
                f'&nbsp;<span style="color:{msg_c};font-family:Segoe UI;font-size:9pt">{body}</span><br>'
            )
        else:
            safe = msg.replace("&","&amp;").replace("<","&lt;").replace(">","&gt;")
            html = f'<span style="color:{msg_c};font-family:Segoe UI;font-size:9pt">{safe}</span><br>'

        self.log_area.moveCursor(QTextCursor.End)
        self.log_area.insertHtml(html)
        self.log_area.moveCursor(QTextCursor.End)

    def _log(self, msg: str):
        self.signals.log.emit(f"[{now_str()}] {msg}")

    # ──────────────────────────────────────────────
    # Callbacks — OOT
    # ──────────────────────────────────────────────
    def _on_sc_changed(self, text: str):
        self._badge.setText(text)
        self.lbl_sc_status.setText(text)

    def _on_aplicar(self):
        if self._running:
            interval = int(self.spin_int.value())
            self.timer.setInterval(interval * 1000)
            self._next_run_at = datetime.now() + timedelta(seconds=interval)
            self._log(f"[OOT] Intervalo atualizado para {interval}s.")

    def _update_countdown(self):
        if self._next_run_at and self._running:
            rem = max(0, int((self._next_run_at - datetime.now()).total_seconds()))
            self.lbl_status.setText(f"Ciclo {self._cycle_count} — próxima coleta em {rem}s")

    # ──────────────────────────────────────────────
    # Callbacks — Aduana
    # ──────────────────────────────────────────────
    def _aduana_url(self) -> str:
        """Monta a URL completa da API Aduana a partir do campo de path."""
        path = self.txt_aduana_path.text().strip()
        if not path.startswith("/"):
            path = "/" + path
        return BASE + path

    def _on_aduana_test(self):
        session = self._last_session
        if session is None:
            QMessageBox.information(
                self, "Aduana — sessão não disponível",
                "Ainda não há sessão autenticada.\n\n"
                "Inicie a coleta OOT primeiro (botão ▶ Iniciar coleta) "
                "e depois clique em Testar agora."
            )
            return
        if not aduana_lock.acquire(blocking=False):
            self._log("[ADUANA] Teste já em andamento.")
            return
        url = self._aduana_url()

        def worker():
            try:
                self._log(f"[ADUANA] Testando → {url}")
                n = aduana_run_once(session, url, self._log)
                self._log(f"[ADUANA] Teste OK — {n} registros → {ADUANA_OUT_PATH}")
            except Exception as e:
                self._log(f"[ADUANA] ERRO no teste: {e}")
            finally:
                aduana_lock.release()

        threading.Thread(target=worker, daemon=True).start()

    # ──────────────────────────────────────────────
    # Control
    # ──────────────────────────────────────────────
    def start(self):
        if self._running:
            return

        self._running = True
        self.btn_start.setEnabled(False)
        self.btn_start.setStyleSheet(self._qss_btn_green(False))
        self.btn_stop.setEnabled(True)
        self.btn_stop.setStyleSheet(self._qss_btn_stop(True))
        self.pulse_dot.set_running(True)
        self.lbl_status.setText("Iniciando coleta…")
        self._run_async_once()
        interval = int(self.spin_int.value())
        self.timer.setInterval(interval * 1000)
        self.timer.start()
        self._next_run_at = datetime.now() + timedelta(seconds=interval)
        self._countdown_timer.start()
        mode = " + Aduana" if self.chk_aduana.isChecked() else ""
        self._log(f"[OOT{mode}] Iniciado. Intervalo: {interval}s · SC: {self.cb_sc.currentText()}")

    def stop(self):
        self.timer.stop()
        self._countdown_timer.stop()
        self._running     = False
        self._next_run_at = None
        self.btn_start.setEnabled(True)
        self.btn_start.setStyleSheet(self._qss_btn_green(True))
        self.btn_stop.setEnabled(False)
        self.btn_stop.setStyleSheet(self._qss_btn_stop(False))
        self.pulse_dot.set_running(False)
        self.lbl_status.setText("Coleta finalizada")
        self._log("[OOT] Finalizado.")

    def _tick(self):
        self._run_async_once()
        self._next_run_at = datetime.now() + timedelta(seconds=self.spin_int.value())

    def _run_async_once(self):
        sc_id          = self.cb_sc.currentText().strip()
        aduana_enabled = self.chk_aduana.isChecked()
        aduana_url     = self._aduana_url() if aduana_enabled else None

        if not scraping_lock.acquire(blocking=False):
            self._log("[OOT] Execução anterior ainda em andamento; ignorando ciclo.")
            return

        def oot_worker():
            session = None
            try:
                self._log(f"[OOT] Iniciando coleta (SC={sc_id})…")
                out, session = oot_run_once(sc_id, self._log)
                self._last_session = session
                self._log(f"[OOT] CSV atualizado: {out}")
                self._cycle_count += 1
            except Exception as e:
                self._log(f"[OOT] ERRO: {e}")
                QTimer.singleShot(0, lambda: QMessageBox.critical(self, "OOT — Erro na coleta", str(e)))
            finally:
                try:
                    scraping_lock.release()
                except Exception:
                    pass

            # ── Aduana (sequencial, reutiliza sessão) ───────────
            if aduana_enabled and session is not None and aduana_url:
                if not aduana_lock.acquire(blocking=False):
                    self._log("[ADUANA] Execução anterior ainda em andamento; ignorando ciclo.")
                    return
                try:
                    self._log(f"[ADUANA] Iniciando coleta…")
                    n = aduana_run_once(session, aduana_url, self._log)
                    self._log(f"[ADUANA] CSV atualizado: {n} registros → {ADUANA_OUT_PATH}")
                except Exception as e:
                    self._log(f"[ADUANA] ERRO: {e}")
                finally:
                    try:
                        aduana_lock.release()
                    except Exception:
                        pass

        threading.Thread(target=oot_worker, daemon=True).start()

# ==========================
# Entry point
# ==========================
if __name__ == "__main__":
    app = QApplication(sys.argv)
    app.setStyle("Fusion")

    pal = QPalette()
    pal.setColor(QPalette.Window,          QColor(ML_BG))
    pal.setColor(QPalette.WindowText,      QColor(ML_NAVY))
    pal.setColor(QPalette.Base,            QColor(ML_CARD))
    pal.setColor(QPalette.AlternateBase,   QColor(ML_FIELD))
    pal.setColor(QPalette.Text,            QColor(ML_NAVY))
    pal.setColor(QPalette.Button,          QColor(ML_CARD))
    pal.setColor(QPalette.ButtonText,      QColor(ML_NAVY))
    pal.setColor(QPalette.Highlight,       QColor(ML_YELLOW))
    pal.setColor(QPalette.HighlightedText, QColor(ML_NAVY))
    app.setPalette(pal)

    win = OutOnTimeInterface()
    win.show()
    sys.exit(app.exec())