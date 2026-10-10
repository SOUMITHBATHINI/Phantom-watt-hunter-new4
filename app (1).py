"""
=============================================================================
Phantom Watt Hunter  -  Facility energy monitoring & suspected-waste finder
-----------------------------------------------------------------------------
Run:      pip install streamlit pandas plotly      (pandas >= 2.2)
          streamlit run app.py
Storage:  SQLite file `phantom_watt_hunter.db` (Python standard library).
Optional: `pip install fastapi uvicorn` + `uvicorn app:api` for a gateway endpoint.

HONESTY RULES BUILT IN
 * Simulated / uploaded / gateway data are always labelled separately.
 * An alert is a SUSPECTED ANOMALY needing on-site verification, never "confirmed waste".
 * A zone-level meter can only point to the zone; a circuit meter to the circuit;
   an appliance is named only when it has its own meter.
 * Missing data is never treated as zero consumption.
=============================================================================
"""

import json
import os
import random
import sqlite3
import tempfile
from datetime import date, datetime, time, timedelta

import pandas as pd
import plotly.express as px
import plotly.graph_objects as go
import streamlit as st

# =============================================================================
# 1. CONSTANTS
# =============================================================================
DB_PATH = os.environ.get("PWH_DB", "phantom_watt_hunter.db")
DAY_NAMES = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]
MODES = ["Scheduled", "Intermittent", "Continuous", "Standby"]
SCHEDULED_MODES = ("Scheduled", "Intermittent")
CATEGORIES = ["Lighting", "HVAC / Air conditioning", "Fans", "Computers / IT", "Plug loads",
              "Motors / Machinery", "Elevators / Escalators", "Medical equipment",
              "Kitchen / Refrigeration", "Other"]
FACILITY_TYPES = ["College", "Airport", "Hospital", "Mall", "Office", "Warehouse",
                  "Railway station", "Other"]
ZONE_KINDS = ["Zone", "Building", "Floor", "Room", "Lab", "Terminal", "Shop", "Outdoor", "Other"]
LEVEL_NAMES = {"A": "Level A - zone meter", "B": "Level B - circuit meter",
               "C": "Level C - appliance meter"}
SOURCE_LABELS = {"simulated": "🧪 Simulated", "uploaded": "📂 Uploaded CSV",
                 "api": "📡 Gateway/API (unverified)"}
SEV_ORDER = {"Critical": 0, "High": 1, "Medium": 2, "Low": 3}
ACTIVE_STATUSES = ("Open", "Acknowledged", "Assigned")
STATUS_FOR_ACTION = {"Acknowledge": "Acknowledged", "Assign": "Assigned", "Resolve": "Resolved",
                     "Dismiss": "Dismissed", "Reopen": "Open"}
RULES = {
    "OUTSIDE_SCHEDULE": "Consumption outside scheduled hours",
    "OVERNIGHT_BASE": "Abnormal overnight base load",
    "ABOVE_EXPECTED": "Consumption above expected range",
    "SPIKE_VS_BASELINE": "Sudden increase vs historical baseline",
    "METER_OFFLINE": "Meter offline",
    "METER_STALE": "Meter reporting stale",
    "DATA_GAP": "Missing data / reporting gap",
}
EXCESS_RULES = ("OUTSIDE_SCHEDULE", "OVERNIGHT_BASE", "ABOVE_EXPECTED", "SPIKE_VS_BASELINE")
DEFAULTS = {"tolerance_pct": 20.0, "floor_kw": 0.15, "spike_pct": 50.0, "min_hist_days": 3,
            "night_start": 22, "night_end": 5, "ref_mode": "clock"}
ALERT_COLS = ["key", "facility", "zone_id", "zone", "meter_pk", "meter", "level", "monitoring",
              "suspected", "rule", "rule_label", "start", "end", "duration_min", "expected_kw",
              "measured_kw", "peak_kw", "schedule", "excess_kwh", "excess_cost_inr", "severity",
              "explanation", "action", "evidence", "evidence_note", "data_source",
              "counted_in_totals"]

SCHEMA = """
CREATE TABLE IF NOT EXISTS facilities(
  id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT NOT NULL UNIQUE, type TEXT DEFAULT 'Other',
  tariff_inr REAL NOT NULL DEFAULT 8.0, sample_key TEXT, active INTEGER NOT NULL DEFAULT 1,
  archived_at TEXT, created_at TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS zones(
  id INTEGER PRIMARY KEY AUTOINCREMENT, facility_id INTEGER NOT NULL REFERENCES facilities(id),
  name TEXT NOT NULL, kind TEXT DEFAULT 'Zone', active INTEGER NOT NULL DEFAULT 1,
  archived_at TEXT, created_at TEXT NOT NULL, UNIQUE(facility_id, name));
CREATE TABLE IF NOT EXISTS circuits(
  id INTEGER PRIMARY KEY AUTOINCREMENT, zone_id INTEGER NOT NULL REFERENCES zones(id),
  name TEXT NOT NULL, category TEXT DEFAULT 'Other', active INTEGER NOT NULL DEFAULT 1,
  archived_at TEXT, created_at TEXT NOT NULL, UNIQUE(zone_id, name));
CREATE TABLE IF NOT EXISTS schedules(
  id INTEGER PRIMARY KEY AUTOINCREMENT, facility_id INTEGER NOT NULL REFERENCES facilities(id),
  name TEXT NOT NULL, days TEXT NOT NULL, start_min INTEGER NOT NULL, end_min INTEGER NOT NULL,
  active INTEGER NOT NULL DEFAULT 1, archived_at TEXT, created_at TEXT NOT NULL,
  UNIQUE(facility_id, name));
CREATE TABLE IF NOT EXISTS holidays(
  id INTEGER PRIMARY KEY AUTOINCREMENT, facility_id INTEGER NOT NULL REFERENCES facilities(id),
  hdate TEXT NOT NULL, name TEXT, UNIQUE(facility_id, hdate));
CREATE TABLE IF NOT EXISTS appliances(
  id INTEGER PRIMARY KEY AUTOINCREMENT, zone_id INTEGER NOT NULL REFERENCES zones(id),
  circuit_id INTEGER REFERENCES circuits(id), schedule_id INTEGER REFERENCES schedules(id),
  name TEXT NOT NULL, category TEXT DEFAULT 'Other', quantity INTEGER NOT NULL,
  rated_w REAL NOT NULL, load_pct REAL NOT NULL DEFAULT 100, mode TEXT NOT NULL,
  active INTEGER NOT NULL DEFAULT 1, archived_at TEXT, created_at TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS meters(
  id INTEGER PRIMARY KEY AUTOINCREMENT, meter_code TEXT NOT NULL UNIQUE, name TEXT,
  facility_id INTEGER NOT NULL REFERENCES facilities(id), zone_id INTEGER NOT NULL REFERENCES zones(id),
  circuit_id INTEGER REFERENCES circuits(id), appliance_id INTEGER REFERENCES appliances(id),
  level TEXT NOT NULL, protocol TEXT DEFAULT 'CSV/API', unit TEXT NOT NULL DEFAULT 'kW',
  timeout_min INTEGER NOT NULL DEFAULT 30, active INTEGER NOT NULL DEFAULT 1,
  archived_at TEXT, created_at TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS readings(
  id INTEGER PRIMARY KEY AUTOINCREMENT, meter_id INTEGER NOT NULL REFERENCES meters(id),
  facility_id INTEGER NOT NULL, zone_id INTEGER NOT NULL, circuit_id INTEGER,
  ts TEXT NOT NULL, active_power_kw REAL NOT NULL, cumulative_energy_kwh REAL,
  data_source TEXT NOT NULL, quality_status TEXT NOT NULL DEFAULT 'ok', UNIQUE(meter_id, ts));
CREATE INDEX IF NOT EXISTS idx_readings_fac_ts ON readings(facility_id, ts);
CREATE TABLE IF NOT EXISTS alert_states(
  key TEXT PRIMARY KEY, status TEXT NOT NULL, assignee TEXT, note TEXT, updated_at TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS alert_history(
  id INTEGER PRIMARY KEY AUTOINCREMENT, key TEXT NOT NULL, ts TEXT NOT NULL,
  from_status TEXT, to_status TEXT, assignee TEXT, note TEXT);
CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY, value TEXT);
"""

# children archived together with a parent (table, foreign key)
CHILDREN = {"facilities": [("zones", "facility_id"), ("schedules", "facility_id"),
                           ("meters", "facility_id")],
            "zones": [("circuits", "zone_id"), ("appliances", "zone_id"), ("meters", "zone_id")],
            "circuits": [("meters", "circuit_id")]}


# =============================================================================
# 2. DATABASE HELPERS
# =============================================================================
def now_str():
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def fts(t):
    """Timestamp -> the text format stored in SQLite (sorts correctly as text)."""
    return pd.Timestamp(t).strftime("%Y-%m-%d %H:%M:%S")


def get_conn(path=None):
    conn = sqlite3.connect(path or DB_PATH, timeout=30)
    conn.execute("PRAGMA foreign_keys=ON")
    try:
        conn.execute("PRAGMA journal_mode=WAL")
    except sqlite3.DatabaseError:
        pass
    conn.executescript(SCHEMA)
    conn.commit()
    return conn


def q(conn, sql, params=()):
    return pd.read_sql_query(sql, conn, params=params)


def _py(v):
    """Convert numpy scalars / NaN to plain Python values SQLite can store."""
    if v is not None and hasattr(v, "item") and not isinstance(v, (str, bytes)):
        v = v.item()
    return None if isinstance(v, float) and v != v else v


def _insert(conn, table, **cols):
    keys, ph = ",".join(cols), ",".join("?" * len(cols))
    cur = conn.execute(f"INSERT INTO {table}({keys},created_at) VALUES({ph},?)",
                       (*[_py(v) for v in cols.values()], now_str()))
    conn.commit()
    return cur.lastrowid


def load_settings(conn):
    cfg = dict(DEFAULTS)
    for k, v in conn.execute("SELECT key, value FROM settings"):
        if k in DEFAULTS:
            t = type(DEFAULTS[k])
            try:
                cfg[k] = t(float(v)) if t in (int, float) else v
            except ValueError:
                pass
    return cfg


def save_settings(conn, cfg):
    for k in DEFAULTS:
        conn.execute("INSERT OR REPLACE INTO settings(key,value) VALUES(?,?)", (k, str(cfg[k])))
    conn.commit()


# =============================================================================
# 3. INVENTORY CRUD (every function returns (ok, message))
# =============================================================================
def _clean(name):
    return str(name or "").strip()


def add_facility(conn, name, ftype, tariff, sample_key=None):
    if not _clean(name):
        return False, "Facility name is required.", None
    if tariff is None or tariff < 0:
        return False, "Tariff must be 0 or more (₹/kWh).", None
    try:
        fid = _insert(conn, "facilities", name=_clean(name), type=ftype, tariff_inr=float(tariff),
                      sample_key=sample_key)
        return True, f"Facility '{_clean(name)}' created.", fid
    except sqlite3.IntegrityError:
        return False, f"A facility named '{_clean(name)}' already exists (maybe archived).", None


def update_facility(conn, fid, name, ftype, tariff):
    if not _clean(name) or tariff < 0:
        return False, "Name is required and tariff must be 0 or more."
    try:
        conn.execute("UPDATE facilities SET name=?, type=?, tariff_inr=? WHERE id=?",
                     (_clean(name), ftype, float(tariff), int(fid)))
        conn.commit()
        return True, "Facility updated."
    except sqlite3.IntegrityError:
        return False, "Another facility already uses that name."


def add_zone(conn, fid, name, kind):
    if not _clean(name):
        return False, "Zone name is required.", None
    try:
        zid = _insert(conn, "zones", facility_id=int(fid), name=_clean(name), kind=kind)
        return True, f"Zone '{_clean(name)}' created.", zid
    except sqlite3.IntegrityError:
        return False, f"Zone '{_clean(name)}' already exists in this facility (maybe archived).", None


def rename_zone(conn, zid, name, kind):
    if not _clean(name):
        return False, "Zone name is required."
    try:
        conn.execute("UPDATE zones SET name=?, kind=? WHERE id=?", (_clean(name), kind, int(zid)))
        conn.commit()
        return True, "Zone updated."
    except sqlite3.IntegrityError:
        return False, "Another zone already uses that name."


def add_circuit(conn, zone_id, name, category):
    if not _clean(name):
        return False, "Circuit name is required.", None
    try:
        cid = _insert(conn, "circuits", zone_id=int(zone_id), name=_clean(name), category=category)
        return True, f"Circuit '{_clean(name)}' created.", cid
    except sqlite3.IntegrityError:
        return False, "That circuit name already exists in this zone (maybe archived).", None


def add_schedule(conn, fid, name, days, start_min, end_min):
    if not _clean(name):
        return False, "Schedule name is required.", None
    if not days:
        return False, "Pick at least one day.", None
    try:
        sid = _insert(conn, "schedules", facility_id=int(fid), name=_clean(name),
                      days=",".join(str(int(d)) for d in sorted(days)),
                      start_min=int(start_min), end_min=int(end_min))
        return True, f"Schedule '{_clean(name)}' created.", sid
    except sqlite3.IntegrityError:
        return False, "A schedule with that name already exists (maybe archived).", None


def add_holiday(conn, fid, hdate, name):
    try:
        conn.execute("INSERT INTO holidays(facility_id,hdate,name) VALUES(?,?,?)",
                     (int(fid), pd.Timestamp(hdate).strftime("%Y-%m-%d"), _clean(name)))
        conn.commit()
        return True, "Holiday added."
    except sqlite3.IntegrityError:
        return False, "That date is already a holiday."


def validate_appliance(name, qty, rated_w, load_pct, mode, schedule_id):
    if not _clean(name):
        return "Appliance name is required."
    if qty is None or int(qty) < 1:
        return "Quantity must be at least 1."
    if rated_w is None or float(rated_w) <= 0:
        return "Rated wattage must be greater than 0."
    if load_pct is None or not (1 <= float(load_pct) <= 100):
        return "Typical load must be between 1 and 100 % of rated power."
    if mode not in MODES:
        return "Unknown operating mode."
    if mode in SCHEDULED_MODES and not schedule_id:
        return f"'{mode}' equipment needs an operating schedule - create one in the Schedules tab first."
    return None


def add_appliance(conn, zone_id, circuit_id, schedule_id, name, category, qty, rated_w, load_pct, mode):
    err = validate_appliance(name, qty, rated_w, load_pct, mode, schedule_id)
    if err:
        return False, err, None
    aid = _insert(conn, "appliances", zone_id=int(zone_id), circuit_id=circuit_id, schedule_id=schedule_id,
                  name=_clean(name), category=category, quantity=int(qty), rated_w=float(rated_w),
                  load_pct=float(load_pct), mode=mode)
    return True, f"Added {int(qty)} x {_clean(name)}.", aid


def update_appliance(conn, aid, zone_id, circuit_id, schedule_id, name, category, qty, rated_w,
                     load_pct, mode):
    err = validate_appliance(name, qty, rated_w, load_pct, mode, schedule_id)
    if err:
        return False, err
    conn.execute("""UPDATE appliances SET zone_id=?, circuit_id=?, schedule_id=?, name=?, category=?,
                    quantity=?, rated_w=?, load_pct=?, mode=? WHERE id=?""",
                 (int(zone_id), _py(circuit_id), _py(schedule_id), _clean(name), category, int(qty),
                  float(rated_w), float(load_pct), mode, int(aid)))
    conn.commit()
    return True, "Appliance updated. Historical readings were not changed."


def add_meter(conn, code, name, fid, zone_id, circuit_id, appliance_id, level, protocol, unit, timeout_min):
    code = _clean(code)
    if not code or " " in code:
        return False, "Meter ID is required and must not contain spaces.", None
    if level not in LEVEL_NAMES:
        return False, "Pick a monitoring level.", None
    circuit_id, appliance_id = _py(circuit_id), _py(appliance_id)
    if level == "B" and not circuit_id:
        return False, "A Level B (circuit) meter must be mapped to a circuit.", None
    if level == "C" and not appliance_id:
        return False, "A Level C (appliance) meter must be mapped to an appliance.", None
    if unit not in ("kW", "W") or int(timeout_min) < 1:
        return False, "Unit must be kW or W and the timeout at least 1 minute.", None
    try:
        mid = _insert(conn, "meters", meter_code=code, name=_clean(name) or code, facility_id=int(fid),
                      zone_id=int(zone_id), circuit_id=_py(circuit_id) if level in "BC" else None,
                      appliance_id=_py(appliance_id) if level == "C" else None, level=level,
                      protocol=protocol, unit=unit, timeout_min=int(timeout_min))
        return True, f"Meter '{code}' registered.", mid
    except sqlite3.IntegrityError:
        return False, f"Meter ID '{code}' already exists (it may be archived).", None


def archive_entity(conn, table, eid, stamp=None):
    """Soft delete (keeps all historical readings). Archives dependent items too."""
    stamp = stamp or now_str()
    conn.execute(f"UPDATE {table} SET active=0, archived_at=? WHERE id=? AND active=1", (stamp, int(eid)))
    if table == "circuits":
        conn.execute("UPDATE appliances SET circuit_id=NULL WHERE circuit_id=?", (int(eid),))
    for child, fk in CHILDREN.get(table, []):
        for (cid,) in conn.execute(f"SELECT id FROM {child} WHERE {fk}=? AND active=1", (int(eid),)).fetchall():
            archive_entity(conn, child, cid, stamp)
    conn.commit()


def restore_entity(conn, table, eid):
    row = conn.execute(f"SELECT archived_at FROM {table} WHERE id=?", (int(eid),)).fetchone()
    if not row or not row[0]:
        return
    stamp = row[0]
    conn.execute(f"UPDATE {table} SET active=1, archived_at=NULL WHERE id=?", (int(eid),))
    for child, fk in CHILDREN.get(table, []):
        for (cid,) in conn.execute(f"SELECT id FROM {child} WHERE {fk}=? AND archived_at=?",
                                   (int(eid), stamp)).fetchall():
            restore_entity(conn, child, cid)
    conn.commit()


def archive_schedule(conn, sid):
    used = conn.execute("SELECT COUNT(*) FROM appliances WHERE schedule_id=? AND active=1", (int(sid),)).fetchone()[0]
    if used:
        return False, f"{used} active appliance(s) still use this schedule. Change them first."
    archive_entity(conn, "schedules", sid)
    return True, "Schedule archived."


# =============================================================================
# 4. SCHEDULES & EXPECTED POWER
# =============================================================================
def hhmm_to_min(s):
    h, m = str(s).split(":")
    return int(h) * 60 + int(m)


def min_to_hhmm(m):
    return f"{int(m) // 60:02d}:{int(m) % 60:02d}"


def sched_text(days, s, e):
    days = sorted(days)
    if days == list(range(7)):
        d = "Daily"
    elif days == [0, 1, 2, 3, 4]:
        d = "Mon-Fri"
    elif days == [0, 1, 2, 3, 4, 5]:
        d = "Mon-Sat"
    else:
        d = ",".join(DAY_NAMES[i] for i in days)
    return f"{d} {min_to_hhmm(s)}-{min_to_hhmm(e)}" if s != e else f"{d} all day"


def schedule_hours(s, e):
    return 24.0 if s == e else ((e - s) % 1440) / 60.0


def schedule_mask(ts, days, s, e, holidays):
    """True where `ts` falls inside the schedule (supports overnight windows and holidays)."""
    m = ts.dt.hour * 60 + ts.dt.minute
    day0 = ts.dt.normalize()
    if s == e:
        inwin, wdate = pd.Series(True, index=ts.index), day0
    elif s < e:
        inwin, wdate = (m >= s) & (m < e), day0
    else:  # overnight, e.g. 18:00-06:00: the after-midnight part belongs to the previous day
        inwin = (m >= s) | (m < e)
        wdate = day0 - pd.to_timedelta((m < e).astype(int), unit="D")
    ok = inwin & wdate.dt.weekday.isin(list(days))
    if holidays:
        ok = ok & ~wdate.dt.date.isin(holidays)
    return ok


def load_context(conn, fid):
    fid = int(fid)
    zones = q(conn, "SELECT * FROM zones WHERE facility_id=? AND active=1 ORDER BY name", (fid,))
    circuits = q(conn, """SELECT c.*, z.name AS zone_name FROM circuits c JOIN zones z ON z.id=c.zone_id
                          WHERE z.facility_id=? AND c.active=1 AND z.active=1 ORDER BY z.name, c.name""", (fid,))
    apps = q(conn, """SELECT a.*, z.name AS zone_name, c.name AS circuit_name, s.name AS schedule_name
                      FROM appliances a JOIN zones z ON z.id=a.zone_id
                      LEFT JOIN circuits c ON c.id=a.circuit_id LEFT JOIN schedules s ON s.id=a.schedule_id
                      WHERE z.facility_id=? AND a.active=1 AND z.active=1 ORDER BY z.name, a.name""", (fid,))
    apps["connected_kw"] = apps["quantity"] * apps["rated_w"] / 1000.0
    apps["expected_kw"] = apps["connected_kw"] * apps["load_pct"] / 100.0
    meters = q(conn, "SELECT * FROM meters WHERE facility_id=? AND active=1 ORDER BY meter_code", (fid,))
    sch = q(conn, "SELECT * FROM schedules WHERE facility_id=? AND active=1 ORDER BY name", (fid,))
    scheds = {}
    for _, r in sch.iterrows():
        days = [int(x) for x in str(r["days"]).split(",") if x != ""]
        scheds[int(r["id"])] = {"name": r["name"], "days": days, "s": int(r["start_min"]),
                                "e": int(r["end_min"]), "text": sched_text(days, int(r["start_min"]), int(r["end_min"]))}
    hol = {pd.Timestamp(d).date() for d in q(conn, "SELECT hdate FROM holidays WHERE facility_id=?", (fid,))["hdate"]}
    return {"zones": zones, "circuits": circuits, "apps": apps, "meters": meters, "scheds": scheds, "holidays": hol}


def scope_appliances(meter, apps):
    """Appliances a meter is responsible for, by monitoring level."""
    if meter["level"] == "A":
        return apps[apps["zone_id"] == meter["zone_id"]]
    if meter["level"] == "B":
        return apps[apps["circuit_id"] == meter["circuit_id"]]
    return apps[apps["id"] == meter["appliance_id"]]


def expected_profile(ts, scope, scheds, holidays):
    """Expected kW at each timestamp for a set of appliances.
    always_kw = Continuous/Standby gear; sched_kw = Scheduled/Intermittent gear that is 'on' now."""
    ts = pd.Series(pd.to_datetime(ts)).reset_index(drop=True)
    always = float(scope.loc[scope["mode"].isin(["Continuous", "Standby"]), "expected_kw"].sum())
    sched_kw = pd.Series(0.0, index=ts.index)
    for _, a in scope[scope["mode"].isin(SCHEDULED_MODES)].iterrows():
        sid = a["schedule_id"]
        if pd.isna(sid) or int(sid) not in scheds:
            mask = pd.Series(True, index=ts.index)  # no schedule known -> never alert on it
        else:
            sc = scheds[int(sid)]
            mask = schedule_mask(ts, sc["days"], sc["s"], sc["e"], holidays)
        sched_kw += mask.astype(float) * float(a["expected_kw"])
    return pd.DataFrame({"always_kw": always, "sched_kw": sched_kw, "total_kw": always + sched_kw})


def scope_schedule_text(scope, scheds):
    parts = []
    for sid in scope.loc[scope["mode"].isin(SCHEDULED_MODES), "schedule_id"].dropna().unique():
        if int(sid) in scheds:
            parts.append(f"{scheds[int(sid)]['name']} ({scheds[int(sid)]['text']})")
    if (scope["mode"].isin(["Continuous", "Standby"])).any():
        parts.append("Continuous/standby equipment (24x7)")
    return "; ".join(parts) if parts else "No equipment registered for this meter"


# =============================================================================
# 5. READING INGESTION (CSV / JSON / API share this one validated path)
# =============================================================================
def parse_timestamps(col):
    """Parse timestamps. A single UTC offset is ignored (wall-clock time kept); mixed offsets are
    converted to this computer's local time."""
    try:
        s = pd.to_datetime(col, errors="coerce", format="mixed")
    except (ValueError, TypeError):
        s = pd.to_datetime(col, errors="coerce", utc=True, format="mixed")
        return s.dt.tz_convert(datetime.now().astimezone().tzinfo).dt.tz_localize(None)
    if getattr(s.dt, "tz", None) is not None:
        s = s.dt.tz_localize(None)
    return s


def ingest_readings(conn, records, source="uploaded", now=None):
    """Validate and store readings. Returns a result dict; never raises on bad rows."""
    now = pd.Timestamp(now) if now is not None else pd.Timestamp.now()
    df = records.copy() if isinstance(records, pd.DataFrame) else pd.DataFrame(records)
    res = {"received": int(len(df)), "inserted": 0, "duplicates": 0, "suspect": 0, "rejected": {}}
    if df.empty:
        return res
    df.columns = [str(c).strip().lower() for c in df.columns]
    for need in ("timestamp", "meter_id"):
        if need not in df.columns:
            raise ValueError(f"Missing required column: {need}")
    if not any(c in df.columns for c in ("active_power_kw", "active_power_w", "active_power")):
        raise ValueError("Missing power column: use active_power_kw (or active_power_w / active_power).")

    meters = q(conn, """SELECT m.id AS meter_pk, m.meter_code, m.facility_id, m.zone_id, m.circuit_id, m.unit,
        CASE m.level
          WHEN 'A' THEN (SELECT COALESCE(SUM(quantity*rated_w),0)/1000.0 FROM appliances WHERE zone_id=m.zone_id AND active=1)
          WHEN 'B' THEN (SELECT COALESCE(SUM(quantity*rated_w),0)/1000.0 FROM appliances WHERE circuit_id=m.circuit_id AND active=1)
          ELSE (SELECT COALESCE(SUM(quantity*rated_w),0)/1000.0 FROM appliances WHERE id=m.appliance_id AND active=1) END AS rated_kw
        FROM meters m WHERE m.active=1""")
    df["meter_code"] = df["meter_id"].astype(str).str.strip()
    # mapping comes from the meter registry, so ignore any ids/flags supplied in the file
    ignore = ["meter_id", "facility_id", "zone_id", "circuit_id", "unit", "rated_kw", "meter_pk", "level"]
    df = df.drop(columns=[c for c in ignore if c in df.columns]).merge(meters, how="left", on="meter_code")
    df["ts"] = parse_timestamps(df["timestamp"])
    if "active_power_kw" in df.columns:
        kw = pd.to_numeric(df["active_power_kw"], errors="coerce")
    elif "active_power_w" in df.columns:
        kw = pd.to_numeric(df["active_power_w"], errors="coerce") / 1000.0
    else:
        raw = pd.to_numeric(df["active_power"], errors="coerce")
        kw = raw.where(df["unit"] != "W", raw / 1000.0)
    df["kw"] = kw
    cum = pd.to_numeric(df["cumulative_energy_kwh"], errors="coerce") if "cumulative_energy_kwh" in df.columns \
        else pd.Series(float("nan"), index=df.index)

    alive = pd.Series(True, index=df.index)

    def drop(mask, reason):
        hit = mask & alive
        if hit.any():
            res["rejected"][reason] = res["rejected"].get(reason, 0) + int(hit.sum())
            alive.loc[hit] = False

    drop(df["meter_pk"].isna(), "unknown or archived meter_id")
    drop(df["ts"].isna(), "invalid or missing timestamp")
    drop(df["kw"].isna() | df["kw"].isin([float("inf"), float("-inf")]), "missing or non-numeric power")
    drop(df["kw"] < 0, "negative power")
    drop(df["ts"] > now + pd.Timedelta(days=1), "timestamp more than 1 day in the future")
    dup = df.duplicated(["meter_pk", "ts"], keep="last") & alive
    res["duplicates"] += int(dup.sum())
    alive &= ~dup
    good = df[alive]
    suspect = (good["rated_kw"] > 0) & (good["kw"] > 3 * good["rated_kw"].clip(lower=0.5))
    res["suspect"] = int(suspect.sum())

    rows = []
    for i, r in good.iterrows():
        c = cum.loc[i]
        rows.append((int(r["meter_pk"]), int(r["facility_id"]), int(r["zone_id"]),
                     None if pd.isna(r["circuit_id"]) else int(r["circuit_id"]), fts(r["ts"]),
                     float(r["kw"]), None if pd.isna(c) else float(c), source,
                     "suspect" if suspect.loc[i] else "ok"))
    before = conn.total_changes
    conn.executemany("""INSERT OR IGNORE INTO readings(meter_id,facility_id,zone_id,circuit_id,ts,
        active_power_kw,cumulative_energy_kwh,data_source,quality_status) VALUES(?,?,?,?,?,?,?,?,?)""", rows)
    conn.commit()
    res["inserted"] = conn.total_changes - before
    res["duplicates"] += len(rows) - res["inserted"]
    return res


# =============================================================================
# 6. ANALYSIS ENGINE
# =============================================================================
def build_frame(raw, scope, scheds, holidays, cfg):
    """Per-reading analysis for ONE meter. Returns (frame, nominal_interval)."""
    d = raw[raw["quality_status"] == "ok"].sort_values("ts").reset_index(drop=True)
    if d.empty:
        return pd.DataFrame(), pd.Timedelta(minutes=15)
    d = d.copy()
    d["M"] = d["active_power_kw"].astype(float)
    diffs = d["ts"].diff().dropna()
    nominal = diffs.median() if len(diffs) else pd.Timedelta(minutes=15)
    if pd.isna(nominal) or nominal <= pd.Timedelta(0):
        nominal = pd.Timedelta(minutes=15)
    gap = d["ts"].shift(-1) - d["ts"]
    d["dt_h"] = gap.clip(upper=nominal * 1.5).fillna(nominal).dt.total_seconds() / 3600.0

    prof = expected_profile(d["ts"], scope, scheds, holidays)
    d["E"], d["sched_kw"] = prof["total_kw"].values, prof["sched_kw"].values
    d["limit"] = d["E"] + (d["E"] * cfg["tolerance_pct"] / 100.0).clip(lower=cfg["floor_kw"])
    d["ref"], d["rule"] = d["E"], ""

    has_sched = bool(scope["mode"].isin(SCHEDULED_MODES).any())
    over = d["M"] > d["limit"]
    hour = d["ts"].dt.hour
    ns, ne = int(cfg["night_start"]), int(cfg["night_end"])
    night = ((hour >= ns) | (hour < ne)) if ns > ne else ((hour >= ns) & (hour < ne))
    outside = over & (d["sched_kw"] == 0) & has_sched
    d.loc[over, "rule"] = "ABOVE_EXPECTED"
    d.loc[outside & night, "rule"] = "OVERNIGHT_BASE"
    d.loc[outside & ~night, "rule"] = "OUTSIDE_SCHEDULE"

    # history-based rule: same hour & day-type (weekday/weekend) on other days
    d["date"], d["hour"], d["wk"] = d["ts"].dt.normalize(), hour, d["ts"].dt.weekday < 5
    grp = d.groupby(["wk", "hour"])
    base, ndays = grp["M"].transform("median"), grp["date"].transform("nunique")
    spike = ((ndays >= cfg["min_hist_days"]) & (d["M"] > base * (1 + cfg["spike_pct"] / 100.0))
             & ((d["M"] - base) >= cfg["floor_kw"]) & (d["rule"] == "")
             & (d["E"] <= base * (1 + cfg["tolerance_pct"] / 100.0) + cfg["floor_kw"]))
    d.loc[spike, "rule"] = "SPIKE_VS_BASELINE"
    d.loc[spike, "ref"] = base[spike]

    d["flag"] = d["rule"] != ""
    d["excess_kw"] = (d["M"] - d["ref"]).clip(lower=0).where(d["flag"], 0.0)
    d["M_kwh"], d["E_kwh"], d["excess_kwh"] = d["M"] * d["dt_h"], d["E"] * d["dt_h"], d["excess_kw"] * d["dt_h"]
    d["idle_kwh"] = d["M_kwh"].where((d["sched_kw"] == 0) & has_sched, 0.0)
    return d, nominal


def extract_events(p, nominal):
    """Merge consecutive flagged readings (same rule, no data gap) into events."""
    if p.empty or not p["flag"].any():
        return []
    brk = p["ts"].diff() > nominal * 1.5
    fam = p["rule"].replace("OVERNIGHT_BASE", "OUTSIDE_SCHEDULE")  # one incident, even across 22:00
    p = p.assign(gid=((fam != fam.shift()) | brk).cumsum())
    events = []
    for _, g in p[p["flag"]].groupby("gid"):
        dur_h = float(g["dt_h"].sum())
        rule = g["rule"].iloc[0]
        if rule in ("OUTSIDE_SCHEDULE", "OVERNIGHT_BASE"):
            rule = "OVERNIGHT_BASE" if (g["rule"] == "OVERNIGHT_BASE").mean() >= 0.5 else "OUTSIDE_SCHEDULE"
        events.append({
            "rule": rule, "start": g["ts"].min(),
            "end": g["ts"].max() + pd.Timedelta(hours=float(g["dt_h"].iloc[-1])),
            "n": len(g), "dur_h": dur_h, "avg_m": float(g["M"].mean()), "peak": float(g["M"].max()),
            "avg_e": float(g["E"].mean()), "avg_ref": float(g["ref"].mean()),
            "avg_limit": float(g["limit"].mean()), "excess_kwh": float(g["excess_kwh"].sum()),
            "supported": len(g) >= 2 and dur_h >= 0.5,
            "sources": sorted(set(g["data_source"]))})
    return events


def meter_health(last_ts, now, timeout_min):
    if last_ts is None or pd.isna(last_ts):
        return "No data", None
    age = (pd.Timestamp(now) - pd.Timestamp(last_ts)).total_seconds() / 60.0
    if age <= timeout_min:
        return "Online", age
    return ("Stale" if age <= timeout_min * 3 else "Offline"), age


def severity_for(excess_kwh, supported, avg_excess_kw):
    if supported:
        return "Critical" if excess_kwh >= 25 else "High" if excess_kwh >= 8 else "Medium" if excess_kwh >= 2 else "Low"
    return "Medium" if avg_excess_kw >= 1.0 else "Low"


def evidence_level(level, n, supported):
    score = {"A": 2, "B": 3, "C": 4}[level] - (0 if n >= 3 else 1) - (0 if supported else 1)
    return {1: "Low", 2: "Moderate", 3: "Good", 4: "Strong"}[max(1, min(4, score))]


def describe_target(m, zone, circuit, app, scope):
    names = ", ".join(f"{int(a.quantity)} x {a['name']}" for _, a in scope.iterrows()) or "no equipment registered"
    if m["level"] == "A":
        return f"Zone '{zone}' (zone-level meter - cannot tell which circuit or appliance is responsible)"
    if m["level"] == "B":
        return f"Circuit '{circuit}' in zone '{zone}' - equipment on this circuit: {names}. Individual appliance is NOT measured"
    return f"Appliance '{app}' in zone '{zone}' (dedicated appliance meter)"


def recommend_action(rule, level):
    if rule in ("METER_OFFLINE", "METER_STALE"):
        return ("Check meter power, RS-485/Modbus wiring, gateway and network. Until it reports again, "
                "its consumption is UNKNOWN (not zero).")
    if rule == "DATA_GAP":
        return "Review gateway/logger logs for this period. Totals exclude the missing time; nothing is assumed."
    base = {"OUTSIDE_SCHEDULE": "Look for equipment left on after hours, or update the schedule if the use is legitimate.",
            "OVERNIGHT_BASE": "Inspect the area overnight/early morning for equipment left running (AC, heaters, machinery).",
            "ABOVE_EXPECTED": "Check for faults, extra equipment not in the inventory, or an outdated inventory/load factor.",
            "SPIKE_VS_BASELINE": "Compare with a normal day; look for new loads, faults or changed settings."}[rule]
    scope = {"A": " Zone-level meter only: check the whole zone, then add circuit sub-meters to narrow it down.",
             "B": " Inspect the equipment on this circuit; add appliance-level meters to confirm which unit.",
             "C": " Inspect this appliance directly."}[level]
    return base + scope + " This is a suspected anomaly - verify on site before treating it as waste."


def explain_event(ev, cfg, sched):
    tol = f"tolerance {cfg['tolerance_pct']:.0f}% / minimum margin {cfg['floor_kw']:.2f} kW"
    if ev["rule"] in ("OUTSIDE_SCHEDULE", "OVERNIGHT_BASE"):
        return (f"Measured {ev['avg_m']:.2f} kW (peak {ev['peak']:.2f}) while no scheduled equipment in scope is "
                f"expected to be on [{sched}]. Expected {ev['avg_e']:.2f} kW (continuous loads only); allowed "
                f"limit {ev['avg_limit']:.2f} kW ({tol}).")
    if ev["rule"] == "ABOVE_EXPECTED":
        over = (ev["avg_m"] / ev["avg_e"] - 1) * 100 if ev["avg_e"] > 0 else float("nan")
        return (f"Measured {ev['avg_m']:.2f} kW vs expected {ev['avg_e']:.2f} kW (limit {ev['avg_limit']:.2f} kW, "
                f"{tol}); about {over:+.0f}% over expected.")
    return (f"Measured {ev['avg_m']:.2f} kW vs a typical {ev['avg_ref']:.2f} kW at this hour on other days of the "
            f"same type (weekday/weekend); the configured schedule does not explain the rise.")


def make_alert(ev, m, facility, zone, circuit, app, scope, scheds, tariff, cfg):
    sched = scope_schedule_text(scope, scheds)
    supported = ev["supported"]
    excess = ev["excess_kwh"] if supported else float("nan")
    avg_excess = ev["excess_kwh"] / ev["dur_h"] if ev["dur_h"] > 0 else 0.0
    ev_note = (f"Excess estimated from {ev['n']} readings over {ev['dur_h']:.2f} h: sum of (measured - expected) x time."
               if supported else "Excess NOT estimated: fewer than 2 readings or under 30 minutes of evidence.")
    return {
        "key": f"{m['meter_code']}|{ev['rule']}|{ev['start']:%Y%m%d%H%M}", "facility": facility,
        "zone_id": int(m["zone_id"]), "zone": zone, "meter_pk": int(m["id"]), "meter": m["meter_code"],
        "level": m["level"], "monitoring": LEVEL_NAMES[m["level"]],
        "suspected": describe_target(m, zone, circuit, app, scope), "rule": ev["rule"],
        "rule_label": RULES[ev["rule"]], "start": ev["start"], "end": ev["end"],
        "duration_min": round(ev["dur_h"] * 60), "expected_kw": round(ev["avg_ref"], 3),
        "measured_kw": round(ev["avg_m"], 3), "peak_kw": round(ev["peak"], 3), "schedule": sched,
        "excess_kwh": round(excess, 3) if supported else float("nan"),
        "excess_cost_inr": round(excess * tariff, 2) if supported else float("nan"),
        "severity": severity_for(ev["excess_kwh"], supported, avg_excess),
        "explanation": explain_event(ev, cfg, sched), "action": recommend_action(ev["rule"], m["level"]),
        "evidence": evidence_level(m["level"], ev["n"], supported), "evidence_note": ev_note,
        "data_source": ", ".join(SOURCE_LABELS.get(s, s) for s in ev["sources"]), "counted_in_totals": False}


def health_alert(m, facility, zone, circuit, app, scope, scheds, kind, when, detail, sev, src):
    return {
        "key": f"{m['meter_code']}|{kind}|{pd.Timestamp(when):%Y%m%d%H%M}", "facility": facility,
        "zone_id": int(m["zone_id"]), "zone": zone, "meter_pk": int(m["id"]), "meter": m["meter_code"],
        "level": m["level"], "monitoring": LEVEL_NAMES[m["level"]],
        "suspected": describe_target(m, zone, circuit, app, scope), "rule": kind, "rule_label": RULES[kind],
        "start": pd.Timestamp(when), "end": pd.Timestamp(when), "duration_min": 0,
        "expected_kw": float("nan"), "measured_kw": float("nan"), "peak_kw": float("nan"),
        "schedule": scope_schedule_text(scope, scheds), "excess_kwh": float("nan"),
        "excess_cost_inr": float("nan"), "severity": sev, "explanation": detail,
        "action": recommend_action(kind, m["level"]), "evidence": "High (direct observation of missing data)",
        "evidence_note": "Missing data is never counted as zero consumption.", "data_source": src,
        "counted_in_totals": False}


def analyze_facility(conn, fid, start, end, tariff, cfg, sources, ref_now):
    """The whole engine: readings -> per-meter frames -> events/alerts -> zone & facility totals."""
    start, end, ref_now = pd.Timestamp(start), pd.Timestamp(end), pd.Timestamp(ref_now)
    ctx = load_context(conn, fid)
    meters, apps, zones, scheds, hol = ctx["meters"], ctx["apps"], ctx["zones"], ctx["scheds"], ctx["holidays"]
    fac_name = q(conn, "SELECT name FROM facilities WHERE id=?", (int(fid),))["name"].iloc[0]
    zname = dict(zip(zones["id"], zones["name"]))
    cname = dict(zip(ctx["circuits"]["id"], ctx["circuits"]["name"]))
    aname = dict(zip(apps["id"], apps["name"]))
    srcs = list(sources) or ["__none__"]
    ph = ",".join("?" * len(srcs))
    eff_end = min(end, max(ref_now, start + pd.Timedelta(minutes=1)))
    period_h = max((eff_end - start).total_seconds() / 3600.0, 1e-6)
    ext_start = min(start, end - pd.Timedelta(days=14))
    raw = q(conn, f"""SELECT meter_id, ts, active_power_kw, data_source, quality_status FROM readings
                      WHERE facility_id=? AND ts>=? AND ts<? AND data_source IN ({ph})""",
            (int(fid), fts(ext_start), fts(end), *srcs))
    raw["ts"] = pd.to_datetime(raw["ts"])
    last = q(conn, f"""SELECT meter_id, MAX(ts) AS last_ts, GROUP_CONCAT(DISTINCT data_source) AS sources
                       FROM readings WHERE facility_id=? AND quality_status='ok' AND data_source IN ({ph})
                       GROUP BY meter_id""", (int(fid), *srcs))
    last["last_ts"] = pd.to_datetime(last["last_ts"])
    last = last.set_index("meter_id")

    periods, info, alert_rows = {}, {}, []
    for _, m in meters.iterrows():
        mid = int(m["id"])
        scope = scope_appliances(m, apps)
        zone = zname.get(m["zone_id"], "?")
        circuit = cname.get(m["circuit_id"]) if pd.notna(m["circuit_id"]) else None
        app = aname.get(m["appliance_id"]) if pd.notna(m["appliance_id"]) else None
        mraw = raw[raw["meter_id"] == mid]
        frame, nominal = build_frame(mraw, scope, scheds, hol, cfg)
        p = frame[(frame["ts"] >= start) & (frame["ts"] < end)] if not frame.empty else frame
        periods[mid] = p
        last_ts = last["last_ts"].get(mid) if mid in last.index else None
        health, age = meter_health(last_ts, ref_now, int(m["timeout_min"]))
        src_txt = ", ".join(SOURCE_LABELS.get(s, s) for s in str(last["sources"].get(mid, "")).split(",") if s)
        has = not p.empty
        info[mid] = {
            "meter_pk": mid, "Meter ID": m["meter_code"], "Name": m["name"], "Level": m["level"],
            "Zone": zone, "zone_id": int(m["zone_id"]),
            "Maps to": app if m["level"] == "C" else (circuit if m["level"] == "B" else "(whole zone)"),
            "Health": health, "Last reading": last_ts, "Age (min)": None if age is None else round(age),
            "Timeout (min)": int(m["timeout_min"]), "Data sources": src_txt or "-",
            "Readings in period": int(len(p)), "Suspect readings (excluded)": int((mraw["quality_status"] == "suspect").sum()),
            "Coverage %": round(min(100.0, p["dt_h"].sum() / period_h * 100.0), 1) if has else 0.0,
            "Measured kWh": float(p["M_kwh"].sum()) if has else 0.0,
            "Expected kWh": float(p["E_kwh"].sum()) if has else 0.0,
            "Off-schedule kWh": float(p["idle_kwh"].sum()) if has else 0.0, "has_data": has, "is_primary": False}
        for ev in extract_events(p, nominal):
            alert_rows.append(make_alert(ev, m, fac_name, zone, circuit, app, scope, scheds, tariff, cfg))
        if has:  # reporting gaps inside the period, clustered (gaps < 2 h apart = one alert)
            gaps = p["ts"].diff()
            clusters = []
            for i in gaps.index[gaps > pd.Timedelta(minutes=int(m["timeout_min"]))]:
                prev, nxt, gh = p["ts"].shift().loc[i], p["ts"].loc[i], gaps.loc[i].total_seconds() / 3600
                if clusters and (prev - clusters[-1]["last_next"]) < pd.Timedelta(hours=2):
                    clusters[-1].update(last_next=nxt, n=clusters[-1]["n"] + 1, hours=clusters[-1]["hours"] + gh)
                else:
                    clusters.append({"first_prev": prev, "last_next": nxt, "n": 1, "hours": gh})
            for cl in clusters:
                alert_rows.append(health_alert(
                    m, fac_name, zone, circuit, app, scope, scheds, "DATA_GAP", cl["first_prev"],
                    f"{cl['n']} reporting gap(s) totalling about {cl['hours']:.1f} h between "
                    f"{cl['first_prev']:%d %b %H:%M} and {cl['last_next']:%d %b %H:%M} "
                    f"(timeout {int(m['timeout_min'])} min). Missing time is excluded, not treated as zero.",
                    "Medium" if cl["hours"] >= 6 else "Low", src_txt))
        if health in ("Stale", "Offline"):
            detail = (f"Last reading {last_ts:%d %b %H:%M}, {age / 60:.1f} h before the reference time "
                      f"(timeout {int(m['timeout_min'])} min).")
            alert_rows.append(health_alert(
                m, fac_name, zone, circuit, app, scope, scheds,
                "METER_OFFLINE" if health == "Offline" else "METER_STALE", last_ts, detail,
                ("High" if age > 1440 else "Medium") if health == "Offline" else "Low", src_txt))

    # primary measurement source per zone (prevents double counting A + B + C of the same energy)
    for z in zones["id"]:
        for lvl in "ABC":
            cand = [i for i in info.values() if i["zone_id"] == int(z) and i["Level"] == lvl and i["has_data"]]
            if cand:
                for i in cand:
                    i["is_primary"] = True
                break

    alerts = pd.DataFrame(alert_rows, columns=ALERT_COLS)
    if not alerts.empty:
        prim = {k: v["is_primary"] for k, v in info.items()}
        alerts["counted_in_totals"] = alerts.apply(
            lambda r: bool(prim.get(r["meter_pk"], False) and r["rule"] in EXCESS_RULES
                           and pd.notna(r["excess_kwh"])), axis=1)
    states = q(conn, "SELECT key, status, assignee, note, updated_at FROM alert_states")
    alerts = alerts.merge(states, how="left", on="key")
    alerts["status"] = alerts["status"].fillna("Open")
    alerts["assignee"] = alerts["assignee"].fillna("")
    alerts["note"] = alerts["note"].fillna("")
    alerts["sev_rank"] = alerts["severity"].map(SEV_ORDER)
    alerts = alerts.sort_values(["sev_rank", "start"], ascending=[True, False]).drop(columns="sev_rank").reset_index(drop=True)
    valid_excess = alerts["counted_in_totals"] & (alerts["status"] != "Dismissed")

    meter_df = pd.DataFrame(list(info.values()))
    zrows = []
    for _, z in zones.iterrows():
        zid = int(z["id"])
        prim = meter_df[(meter_df["zone_id"] == zid) & (meter_df["is_primary"])] if not meter_df.empty else meter_df
        zl = apps[apps["zone_id"] == zid]
        meas, exp = (prim["Measured kWh"].sum(), prim["Expected kWh"].sum()) if len(prim) else (float("nan"),) * 2
        zx = alerts[valid_excess & (alerts["zone_id"] == zid)]
        zrows.append({
            "Zone": z["name"], "zone_id": zid, "Connected load (kW)": round(zl["connected_kw"].sum(), 3),
            "Monitoring": LEVEL_NAMES[prim["Level"].iloc[0]] if len(prim) else "No meter data",
            "Measured kWh": meas, "Expected kWh": exp, "Difference kWh": meas - exp if len(prim) else float("nan"),
            "Deviation %": (meas - exp) / exp * 100 if len(prim) and exp > 0 else float("nan"),
            "Est. excess kWh": float(zx["excess_kwh"].sum()) if len(prim) else float("nan"),
            "Est. excess ₹": float(zx["excess_cost_inr"].sum()) if len(prim) else float("nan"),
            "Measured cost ₹": meas * tariff if len(prim) else float("nan"),
            "Off-schedule kWh": prim["Off-schedule kWh"].sum() if len(prim) else float("nan"),
            "Coverage %": prim["Coverage %"].mean() if len(prim) else 0.0})
    zone_df = pd.DataFrame(zrows)
    mon = zone_df[zone_df["Monitoring"] != "No meter data"] if not zone_df.empty else zone_df
    health_counts = meter_df["Health"].value_counts().to_dict() if not meter_df.empty else {}
    totals = {
        "measured_kwh": float(mon["Measured kWh"].sum()) if len(mon) else 0.0,
        "expected_kwh": float(mon["Expected kWh"].sum()) if len(mon) else 0.0,
        "excess_kwh": float(alerts.loc[valid_excess, "excess_kwh"].sum()),
        "excess_cost": float(alerts.loc[valid_excess, "excess_cost_inr"].sum()),
        "active_alerts": int(alerts["status"].isin(ACTIVE_STATUSES).sum()),
        "online": int(health_counts.get("Online", 0)), "stale": int(health_counts.get("Stale", 0)),
        "offline": int(health_counts.get("Offline", 0)) + int(health_counts.get("No data", 0)),
        "meters": int(len(meter_df)),
        "valid_pct": float(meter_df["has_data"].mean() * 100) if len(meter_df) else 0.0}
    totals["measured_cost"] = totals["measured_kwh"] * tariff
    in_period = raw[(raw["ts"] >= start) & (raw["ts"] < end)]
    return {"meters": meter_df, "zones": zone_df, "alerts": alerts, "periods": periods, "totals": totals,
            "tariff": tariff, "start": start, "end": end, "eff_end": eff_end, "facility": fac_name,
            "src_counts": in_period["data_source"].value_counts().to_dict(), "apps": apps}


def trend_tables(an, freq):
    """Facility & zone trend tables. Bins where a primary meter is silent are dropped (no fake dips)."""
    rows = []
    for mid, p in an["periods"].items():
        row = an["meters"][an["meters"]["meter_pk"] == mid].iloc[0]
        if p.empty or not row["is_primary"]:
            continue
        s = p.set_index("ts")[["M", "E"]].resample(freq).mean().dropna(subset=["M"])
        s["zone"], s["meter"] = row["Zone"], mid
        rows.append(s.reset_index())
    if not rows:
        return pd.DataFrame(), pd.DataFrame()
    long = pd.concat(rows)
    need = long.groupby("zone")["meter"].nunique()
    zone = long.groupby(["zone", "ts"]).agg(M=("M", "sum"), E=("E", "sum"), n=("meter", "nunique")).reset_index()
    zone = zone[zone["n"] == zone["zone"].map(need)]
    fac = zone.groupby("ts").agg(M=("M", "sum"), E=("E", "sum"), nz=("zone", "nunique")).reset_index()
    return fac[fac["nz"] == zone["zone"].nunique()], zone


# =============================================================================
# 7. ALERT WORKFLOW & REPORTS
# =============================================================================
def set_alert_status(conn, key, new_status, assignee="", note=""):
    if new_status not in ("Open", "Acknowledged", "Assigned", "Resolved", "Dismissed"):
        return False, "Unknown status."
    if new_status == "Assigned" and not _clean(assignee):
        return False, "Enter who the alert is assigned to."
    row = conn.execute("SELECT status, assignee FROM alert_states WHERE key=?", (key,)).fetchone()
    old = row[0] if row else "Open"
    keep_assignee = _clean(assignee) or (row[1] if row and row[1] else "")
    conn.execute("INSERT OR REPLACE INTO alert_states(key,status,assignee,note,updated_at) VALUES(?,?,?,?,?)",
                 (key, new_status, keep_assignee, _clean(note), now_str()))
    conn.execute("INSERT INTO alert_history(key,ts,from_status,to_status,assignee,note) VALUES(?,?,?,?,?,?)",
                 (key, now_str(), old, new_status, keep_assignee, _clean(note)))
    conn.commit()
    return True, f"Alert marked {new_status}."


def build_audit_report(an):
    """One row per alert, built from the same alerts table the dashboard uses."""
    a = an["alerts"]
    if a.empty:
        return pd.DataFrame()
    assume = (f"Tariff Rs {an['tariff']:.2f}/kWh. Excess = sum of (measured - expected/baseline) x time over flagged "
              "readings; only shown with >=2 readings and >=30 min evidence. Missing data excluded, not zero.")
    out = pd.DataFrame({
        "Zone": a["zone"], "Suspected circuit / appliance group": a["suspected"], "Monitoring level": a["monitoring"],
        "Meter": a["meter"], "Rule": a["rule_label"], "Start": a["start"].dt.strftime("%Y-%m-%d %H:%M"),
        "Duration (min)": a["duration_min"], "Expected power (kW)": a["expected_kw"],
        "Measured power avg (kW)": a["measured_kw"], "Peak (kW)": a["peak_kw"],
        "Est. excess energy (kWh)": a["excess_kwh"], "Est. excess cost (₹)": a["excess_cost_inr"],
        "Counted in totals": a["counted_in_totals"] & (a["status"] != "Dismissed"),
        "Severity": a["severity"], "Status": a["status"], "Explanation": a["explanation"],
        "Recommended action": a["action"], "Evidence level": a["evidence"],
        "Evidence & assumptions": a["evidence_note"] + " " + assume, "Data source": a["data_source"],
        "Label": "Suspected anomaly - requires verification, not confirmed waste"})
    return out


def build_summary_markdown(an, period_label):
    t, z, a = an["totals"], an["zones"], an["alerts"]
    L = [f"# Phantom Watt Hunter - Facility summary: {an['facility']}", "",
         f"**Period:** {period_label} ({an['start']:%Y-%m-%d %H:%M} to {an['end']:%Y-%m-%d %H:%M})  ",
         f"**Tariff:** Rs {an['tariff']:.2f}/kWh  ", f"**Data sources in view:** "
         + (", ".join(f"{SOURCE_LABELS.get(k, k)} ({v} readings)" for k, v in an["src_counts"].items()) or "none"), "",
         "> Alerts are *suspected anomalies requiring verification*, not confirmed waste. "
         "Estimated excess cost is not guaranteed savings.", "", "## Totals", "",
         f"- Measured energy: **{t['measured_kwh']:.1f} kWh** (Rs {t['measured_cost']:.0f})",
         f"- Expected energy (same time intervals): **{t['expected_kwh']:.1f} kWh**",
         f"- Estimated excess: **{t['excess_kwh']:.1f} kWh** = **Rs {t['excess_cost']:.0f}**",
         f"- Active alerts: **{t['active_alerts']}**; meters online/stale/offline: "
         f"{t['online']}/{t['stale']}/{t['offline']}", "", "## Zones", "",
         "| Zone | Monitoring | Measured kWh | Expected kWh | Deviation % | Est. excess Rs |", "|---|---|---|---|---|---|"]
    for _, r in z.iterrows():
        f = lambda v, d=1: "n/a" if pd.isna(v) else f"{v:.{d}f}"
        L.append(f"| {r['Zone']} | {r['Monitoring']} | {f(r['Measured kWh'])} | {f(r['Expected kWh'])} | "
                 f"{f(r['Deviation %'], 0)} | {f(r['Est. excess ₹'], 0)} |")
    L += ["", "## Top alerts", ""]
    for _, r in a[a["status"].isin(ACTIVE_STATUSES)].head(8).iterrows():
        L.append(f"- **[{r['severity']}] {r['zone']}** - {r['rule_label']} at {r['start']:%d %b %H:%M} "
                 f"({r['monitoring']}). {r['action']}")
    if a.empty:
        L.append("- No alerts for this period.")
    L += ["", "## Assumptions & limits", "",
          "- Expected power = quantity x rated W x typical load %, only while the equipment's schedule is active.",
          "- Where a zone has several meter levels, only one level is used for totals to avoid double counting.",
          "- Missing readings are excluded from energy totals and never treated as zero.",
          "- Simulated data is for demonstration only and is not real consumption."]
    return "\n".join(L)


# =============================================================================
# 8. SIMULATION (sample facilities; all readings labelled 'simulated')
# =============================================================================
ALLD, MS, MF = [0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4]


def AP(name, cat, qty, w, mode="Scheduled", sched=None, lf=100):
    return dict(name=name, category=cat, quantity=qty, rated_w=w, mode=mode, schedule=sched, load_pct=lf)


HV, LT, IT, FAN, MOT, MED, KIT, ESC = ("HVAC / Air conditioning", "Lighting", "Computers / IT", "Fans",
                                       "Motors / Machinery", "Medical equipment", "Kitchen / Refrigeration",
                                       "Elevators / Escalators")
SAMPLES = {
    "College Campus": dict(prefix="COL", type="College", tariff=8.0, schedules={
        "College hours": (MS, "08:30", "17:00"), "Library hours": (MS, "08:00", "20:00"),
        "Evening floodlights": (ALLD, "18:00", "21:00"), "Auditorium events": (MF, "10:00", "15:00")},
        zones=[
            dict(name="Library", kind="Building", meters="AB", circuits={
                "Lighting & fans": (LT, [AP("LED lights", LT, 20, 20, "Scheduled", "Library hours"),
                                         AP("Ceiling fans", FAN, 10, 60, "Scheduled", "Library hours", 80)]),
                "AC circuit": (HV, [AP("Air conditioner", HV, 2, 1500, "Scheduled", "Library hours", 80)])}),
            dict(name="Playground", kind="Outdoor", meters="B", circuits={
                "Floodlights": (LT, [AP("Floodlight", LT, 4, 500, "Scheduled", "Evening floodlights")])}),
            dict(name="Auditorium", kind="Building", meters="B", circuits={
                "Stage lights": (LT, [AP("Stage light", LT, 30, 100, "Intermittent", "Auditorium events", 60)]),
                "AC circuit": (HV, [AP("Air conditioner", HV, 4, 2000, "Scheduled", "Auditorium events", 75)])}),
            dict(name="Computer Lab", kind="Lab", meters="A", circuits={
                "Workstations": (IT, [AP("Desktop computer", IT, 40, 150, "Scheduled", "College hours", 70),
                                      AP("Network rack", IT, 1, 200, "Continuous", None, 100)])})],
        anomalies=[dict(kind="extra", zone="Playground", circuit="Floodlights", day=1, hour=14, hours=2.5, kw=2.0),
                   dict(kind="extra", zone="Library", circuit="AC circuit", day=1, hour=22, hours=7, kw=1.45),
                   dict(kind="extra", zone="Computer Lab", circuit=None, day=2, hour=19, hours=12, kw=1.3),
                   dict(kind="offline", zone="Auditorium", circuit="Stage lights", hours=6),
                   dict(kind="drop", zone="Computer Lab", circuit=None, day=3, hour=1, hours=6, frac=0.7)]),
    "Airport Terminal": dict(prefix="AIR", type="Airport", tariff=9.5, schedules={
        "Airside operations": (ALLD, "04:00", "23:00"), "Retail hours": (ALLD, "06:00", "23:00")}, zones=[
            dict(name="Check-in Hall", kind="Terminal", meters="A", circuits={
                "Lighting": (LT, [AP("Hall lights", LT, 100, 40, "Continuous")]),
                "HVAC": (HV, [AP("Central AC", HV, 6, 3000, "Continuous", None, 70)])}),
            dict(name="Baggage Handling", kind="Zone", meters="B", circuits={
                "Belts": (MOT, [AP("Conveyor belt", MOT, 12, 1500, "Scheduled", "Airside operations", 60)])}),
            dict(name="Retail Concourse", kind="Shop", meters="A", circuits={
                "Lights & AC": (LT, [AP("Shop lights", LT, 60, 40, "Scheduled", "Retail hours"),
                                     AP("Shop AC", HV, 4, 2500, "Scheduled", "Retail hours", 75)])})],
        anomalies=[dict(kind="extra", zone="Baggage Handling", circuit="Belts", day=1, hour=0, hours=4, kw=6.0),
                   dict(kind="offline", zone="Retail Concourse", circuit=None, hours=4)]),
    "Shopping Mall": dict(prefix="MAL", type="Mall", tariff=10.0, schedules={
        "Mall hours": (ALLD, "10:00", "22:00"), "Night lighting": (ALLD, "18:00", "06:00")}, zones=[
            dict(name="Food Court", kind="Zone", meters="B", circuits={
                "Kitchens": (KIT, [AP("Kitchen equipment", KIT, 10, 2000, "Scheduled", "Mall hours", 50)]),
                "AC": (HV, [AP("Food court AC", HV, 6, 2000, "Scheduled", "Mall hours", 75)])}),
            dict(name="Common Areas", kind="Zone", meters="A", circuits={
                "Lights & escalators": (LT, [AP("Corridor lights", LT, 200, 30, "Scheduled", "Mall hours"),
                                             AP("Escalator", ESC, 8, 3000, "Scheduled", "Mall hours", 40)])}),
            dict(name="Parking", kind="Outdoor", meters="B", circuits={
                "Floodlights": (LT, [AP("Parking floodlight", LT, 40, 150, "Scheduled", "Night lighting")])})],
        anomalies=[dict(kind="extra", zone="Common Areas", circuit=None, day=1, hour=23, hours=5, kw=4.0),
                   dict(kind="extra", zone="Parking", circuit="Floodlights", day=1, hour=12, hours=3, kw=3.5),
                   dict(kind="offline", zone="Food Court", circuit="AC", hours=5)]),
    "Hospital": dict(prefix="HOS", type="Other", tariff=9.0, schedules={"OPD hours": (MS, "08:00", "20:00")}, zones=[
        dict(name="ICU", kind="Zone", meters="A", circuits={
            "Critical care": (MED, [AP("Ventilators & monitors", MED, 20, 300, "Continuous", None, 80),
                                    AP("ICU AC", HV, 4, 2000, "Continuous", None, 70)])}),
        dict(name="OPD", kind="Building", meters="B", circuits={
            "Lighting": (LT, [AP("OPD lights", LT, 80, 30, "Scheduled", "OPD hours")]),
            "AC": (HV, [AP("OPD AC", HV, 6, 2000, "Scheduled", "OPD hours", 75)])}),
        dict(name="Pharmacy Cold Store", kind="Room", meters="A", circuits={
            "Refrigeration": (KIT, [AP("Medicine refrigerator", KIT, 4, 400, "Continuous", None, 70)])})],
        anomalies=[dict(kind="extra", zone="OPD", circuit="AC", day=1, hour=21, hours=6, kw=6.0),
                   dict(kind="drop", zone="Pharmacy Cold Store", circuit=None, day=2, hour=2, hours=8, frac=0.6)]),
    "Office Building": dict(prefix="OFF", type="Office", tariff=9.0, schedules={
        "Office hours": (MF, "09:00", "18:00")}, zones=[
            dict(name="Floor 1", kind="Floor", meters="A", circuits={
                "Lights, AC & PCs": (LT, [AP("Lights", LT, 100, 18, "Scheduled", "Office hours"),
                                          AP("Split AC", HV, 8, 1800, "Scheduled", "Office hours", 75),
                                          AP("Computers", IT, 60, 100, "Scheduled", "Office hours", 70)])}),
            dict(name="Floor 2", kind="Floor", meters="B", circuits={
                "Lighting": (LT, [AP("Lights", LT, 100, 18, "Scheduled", "Office hours")]),
                "AC": (HV, [AP("Split AC", HV, 8, 1800, "Scheduled", "Office hours", 75)])}),
            dict(name="Server Room", kind="Room", meters="A", circuits={
                "Servers & cooling": (IT, [AP("Server", IT, 6, 800, "Continuous", None, 75),
                                           AP("Precision AC", HV, 2, 1500, "Continuous", None, 80)])})],
        anomalies=[dict(kind="extra", zone="Floor 2", circuit="AC", day=1, hour=20, hours=10, kw=5.0),
                   dict(kind="offline", zone="Floor 2", circuit="Lighting", hours=3)])}


def generate_sim_readings(conn, fid, seed=None, now=None):
    """Create 7 days of 15-minute SIMULATED readings for a sample facility's meters."""
    row = conn.execute("SELECT sample_key FROM facilities WHERE id=?", (int(fid),)).fetchone()
    if not row or row[0] not in SAMPLES:
        return False, "Only sample facilities can be simulated."
    tpl = SAMPLES[row[0]]
    rng = random.Random(seed if seed is not None else random.randint(1, 10 ** 6))
    now = pd.Timestamp(now) if now is not None else pd.Timestamp.now()
    end = now.floor("15min")
    ts = pd.date_range(end - pd.Timedelta(days=7), end, freq="15min")
    ctx = load_context(conn, fid)
    zname, cname = dict(zip(ctx["zones"]["id"], ctx["zones"]["name"])), dict(zip(ctx["circuits"]["id"], ctx["circuits"]["name"]))
    conn.execute("DELETE FROM readings WHERE data_source='simulated' AND facility_id=?", (int(fid),))
    midnight = end.normalize()
    rows = []
    for _, m in ctx["meters"].iterrows():
        scope = scope_appliances(m, ctx["apps"])
        E = expected_profile(pd.Series(ts), scope, ctx["scheds"], ctx["holidays"])["total_kw"].values
        zone = zname[m["zone_id"]]
        circ = cname.get(m["circuit_id"]) if pd.notna(m["circuit_id"]) else None
        day_scale = {d: rng.uniform(0.95, 1.02) for d in pd.date_range(midnight - pd.Timedelta(days=8), midnight)}
        power = [max(0.0, E[i] * day_scale[t.normalize()] * rng.gauss(1, 0.025) + rng.uniform(0.01, 0.05))
                 for i, t in enumerate(ts)]
        keep = [True] * len(ts)
        for an_ in tpl["anomalies"]:
            if an_["zone"] != zone:
                continue
            exact = (an_.get("circuit") == circ) if m["level"] != "A" else (an_.get("circuit") is None)
            if an_["kind"] == "offline" and exact:
                cut = end - pd.Timedelta(hours=an_["hours"])
                keep = [k and t <= cut for k, t in zip(keep, ts)]
                continue
            w0 = midnight - pd.Timedelta(days=an_["day"]) + pd.Timedelta(hours=an_["hour"]) if "day" in an_ else None
            if w0 is None:
                continue
            w1 = w0 + pd.Timedelta(hours=an_["hours"])
            if an_["kind"] == "extra" and (m["level"] == "A" or exact):
                power = [p + an_["kw"] * rng.gauss(1, 0.03) if w0 <= t < w1 else p for p, t in zip(power, ts)]
            if an_["kind"] == "drop" and exact:
                keep = [k and not (w0 <= t < w1 and rng.random() < an_["frac"]) for k, t in zip(keep, ts)]
        cum = 1000.0
        for i, t in enumerate(ts):
            cum += power[i] * 0.25
            if keep[i]:
                rows.append((int(m["id"]), int(fid), int(m["zone_id"]),
                             None if pd.isna(m["circuit_id"]) else int(m["circuit_id"]), fts(t),
                             round(power[i], 3), round(cum, 2), "simulated", "ok"))
    conn.executemany("""INSERT OR IGNORE INTO readings(meter_id,facility_id,zone_id,circuit_id,ts,active_power_kw,
        cumulative_energy_kwh,data_source,quality_status) VALUES(?,?,?,?,?,?,?,?,?)""", rows)
    conn.commit()
    return True, f"Generated {len(rows):,} SIMULATED readings (7 days, 15-minute interval)."


def load_sample(conn, key, now=None, seed=None):
    """Create a sample facility (inventory + meters) and simulated readings."""
    tpl = SAMPLES[key]
    ok, msg, fid = add_facility(conn, f"Sample {key}", tpl["type"], tpl["tariff"], sample_key=key)
    if not ok:
        return False, msg + " Use 'Regenerate simulated readings' instead."
    sid = {}
    for name, (days, s, e) in tpl["schedules"].items():
        sid[name] = add_schedule(conn, fid, name, days, hhmm_to_min(s), hhmm_to_min(e))[2]
    n = 0
    for z in tpl["zones"]:
        zid = add_zone(conn, fid, z["name"], z["kind"])[2]
        cids = {}
        for cname_, (cat, apps_) in z["circuits"].items():
            cid = add_circuit(conn, zid, cname_, cat)[2]
            cids[cname_] = cid
            for a in apps_:
                aid = add_appliance(conn, zid, cid, sid.get(a["schedule"]), a["name"], a["category"], a["quantity"],
                                    a["rated_w"], a["load_pct"], a["mode"])[2]
        slug = "".join(ch for ch in z["name"].upper() if ch.isalnum())[:5]
        if "A" in z["meters"]:
            n += 1
            add_meter(conn, f"{tpl['prefix']}-{slug}-Z", f"{z['name']} (zone meter)", fid, zid, None, None, "A",
                      "Modbus RTU (simulated)", "kW", 30)
        if "B" in z["meters"]:
            for cname_, cid in cids.items():
                cs = "".join(ch for ch in cname_.upper() if ch.isalnum())[:5]
                add_meter(conn, f"{tpl['prefix']}-{slug}-{cs}", f"{z['name']} - {cname_}", fid, zid, cid, None, "B",
                          "Modbus RTU (simulated)", "kW", 30)
    ok, msg = generate_sim_readings(conn, fid, seed=seed, now=now)
    return True, f"Sample facility created. {msg}"


# =============================================================================
# 9. SELF-TESTS (acceptance tests 1-10; run from the 'About & Self-test' page)
# =============================================================================
def run_self_tests():
    """Runs the acceptance scenarios on temporary databases. Returns [(name, passed, detail)]."""
    results = []
    NOW = pd.Timestamp("2026-03-11 20:00")  # a Wednesday
    cfg = dict(DEFAULTS)
    tmpdir = tempfile.mkdtemp()

    def record(name, cond, detail=""):
        results.append((name, bool(cond), detail))

    def fixture(path=":memory:"):
        c = get_conn(path)
        return c, add_facility(c, "Test Facility", "Other", 8.0)[2]

    def put(c, code, pairs, source="simulated"):
        recs = [{"timestamp": t, "meter_id": code, "active_power_kw": v} for t, v in pairs]
        return ingest_readings(c, recs, source=source, now=NOW)

    def day_series(day, fn, step=15):
        idx = pd.date_range(pd.Timestamp(day), periods=24 * 60 // step, freq=f"{step}min")
        return [(t, fn(t)) for t in idx]

    def run(c, fid, a=None, b=None, tariff=8.0, ref=None):
        a, b = a or pd.Timestamp("2026-03-11"), b or pd.Timestamp("2026-03-12")
        return analyze_facility(c, fid, a, b, tariff, cfg, list(SOURCE_LABELS), ref or NOW)

    # --- Test 1: connected load
    c, f = fixture()
    zid = add_zone(c, f, "Playground", "Outdoor")[2]
    cid = add_circuit(c, zid, "Floodlights", "Lighting")[2]
    sid = add_schedule(c, f, "Evening", ALLD, 18 * 60, 21 * 60)[2]
    add_appliance(c, zid, cid, sid, "Floodlight", "Lighting", 4, 500, 100, "Scheduled")
    kw = load_context(c, f)["apps"]["connected_kw"].sum()
    record("T1 Playground 4 x 500 W = 2 kW connected load", abs(kw - 2.0) < 1e-9, f"{kw} kW")

    # --- Test 2: 2.05 kW at 2 PM outside 6-9 PM schedule
    add_meter(c, "PLAY-1", "Playground lights", f, zid, cid, None, "B", "test", "kW", 30)
    put(c, "PLAY-1", day_series("2026-03-11", lambda t: 2.05 if (t.hour == 14 and t.minute == 0)
                                else (1.98 if 18 <= t.hour < 21 else 0.03)))
    an = run(c, f, ref=pd.Timestamp("2026-03-11 23:59"))
    al = an["alerts"][an["alerts"]["rule"].isin(EXCESS_RULES)]
    record("T2 2.05 kW at 14:00 flagged as outside schedule on the playground circuit",
           len(al) == 1 and al["rule"].iloc[0] == "OUTSIDE_SCHEDULE" and al["zone"].iloc[0] == "Playground"
           and al["level"].iloc[0] == "B", f"{len(al)} alert(s); {al['suspected'].iloc[0] if len(al) else ''}")
    record("T2b normal 1.98 kW during 18:00-21:00 raises no alert", not (al["start"].dt.hour >= 18).any())

    # --- Test 3: library AC circuit overnight, no appliance claimed
    c3, f3 = fixture()
    z3 = add_zone(c3, f3, "Library", "Building")[2]
    ci3 = add_circuit(c3, z3, "AC circuit", "HVAC / Air conditioning")[2]
    s3 = add_schedule(c3, f3, "Library hours", MS, 8 * 60, 20 * 60)[2]
    add_appliance(c3, z3, ci3, s3, "Air conditioner", HV, 2, 1500, 100, "Scheduled")
    add_meter(c3, "LIB-AC", "Library AC", f3, z3, ci3, None, "B", "test", "kW", 30)
    put(c3, "LIB-AC", day_series("2026-03-11", lambda t: 1.52 if t.hour < 4 else (2.9 if 8 <= t.hour < 20 else 0.02)))
    an3 = run(c3, f3, ref=pd.Timestamp("2026-03-11 23:59"))
    a3 = an3["alerts"][an3["alerts"]["rule"].isin(EXCESS_RULES)]
    record("T3 1.52 kW overnight flags the AC circuit (not a specific unit)",
           len(a3) == 1 and a3["rule"].iloc[0] == "OVERNIGHT_BASE" and "NOT measured" in a3["suspected"].iloc[0]
           and a3["level"].iloc[0] == "B", a3["suspected"].iloc[0] if len(a3) else "no alert")

    # --- Test 4: auditorium normal during event
    c4, f4 = fixture()
    z4 = add_zone(c4, f4, "Auditorium", "Building")[2]
    ci4 = add_circuit(c4, z4, "Stage lights", "Lighting")[2]
    s4 = add_schedule(c4, f4, "Event", ALLD, 10 * 60, 15 * 60)[2]
    add_appliance(c4, z4, ci4, s4, "Stage light", LT, 30, 100, 60, "Intermittent")  # expected 1.8 kW
    add_meter(c4, "AUD-1", "Stage lights", f4, z4, ci4, None, "B", "test", "kW", 30)
    put(c4, "AUD-1", day_series("2026-03-11", lambda t: 1.8 * (1.06 if t.minute == 0 else 0.94) if 10 <= t.hour < 15 else 0.03))
    an4 = run(c4, f4, ref=pd.Timestamp("2026-03-11 23:59"))
    record("T4 normal auditorium readings during the event raise no waste alert",
           an4["alerts"][an4["alerts"]["rule"].isin(EXCESS_RULES)].empty, f"{len(an4['alerts'])} alerts")

    # --- Test 5: stale/offline meter, missing data != zero
    c5, f5 = fixture()
    z5 = add_zone(c5, f5, "Lab", "Lab")[2]
    add_appliance(c5, z5, None, None, "Server", IT, 1, 1000, 100, "Continuous")
    add_meter(c5, "LAB-1", "Lab meter", f5, z5, None, None, "A", "test", "kW", 30)
    put(c5, "LAB-1", [(t, 1.0) for t in pd.date_range("2026-03-11 10:00", "2026-03-11 14:00", freq="15min")])
    an5 = run(c5, f5, ref=NOW)  # 6 h after last reading
    m5 = an5["meters"].iloc[0]
    record("T5 meter 6 h silent is Offline; energy counts only received data (not zero-filled)",
           m5["Health"] == "Offline" and abs(m5["Measured kWh"] - 1.0 * 17 * 0.25) < 1e-6
           and (an5["alerts"]["rule"] == "METER_OFFLINE").any(), f"health={m5['Health']}, kWh={m5['Measured kWh']:.2f}")

    # --- Test 6: tariff & time range
    r8, r10 = run(c, f, tariff=8.0), run(c, f, tariff=10.0)
    half = run(c, f, a=pd.Timestamp("2026-03-11 00:00"), b=pd.Timestamp("2026-03-11 12:00"))
    record("T6 tariff change rescales cost; shorter range reduces energy",
           abs(r10["totals"]["measured_cost"] / r8["totals"]["measured_cost"] - 1.25) < 1e-9
           and half["totals"]["measured_kwh"] < r8["totals"]["measured_kwh"])

    # --- Test 7: audit report == alerts == dashboard totals
    rep = build_audit_report(an)
    ok7 = (abs(rep.loc[rep["Counted in totals"], "Est. excess energy (kWh)"].sum() - an["totals"]["excess_kwh"]) < 1e-6
           and abs(rep.loc[rep["Counted in totals"], "Est. excess cost (₹)"].sum() - an["totals"]["excess_cost"]) < 1e-6)
    record("T7 audit report values match alerts and dashboard totals", ok7 and len(rep) == len(an["alerts"]))

    # --- Test 8: persistence across reconnect
    path = os.path.join(tmpdir, "persist.db")
    c8, f8 = fixture(path)
    z8 = add_zone(c8, f8, "Persist zone", "Zone")[2]
    add_appliance(c8, z8, None, None, "Lamp", LT, 3, 10, 100, "Continuous")
    add_meter(c8, "P-1", "P", f8, z8, None, None, "A", "test", "kW", 30)
    put(c8, "P-1", [(NOW - pd.Timedelta(minutes=15 * i), 0.03) for i in range(4)])
    c8.close()
    c8b = get_conn(path)
    cnt = (c8b.execute("SELECT COUNT(*) FROM facilities").fetchone()[0], c8b.execute("SELECT COUNT(*) FROM zones").fetchone()[0],
           c8b.execute("SELECT COUNT(*) FROM appliances").fetchone()[0], c8b.execute("SELECT COUNT(*) FROM readings").fetchone()[0])
    record("T8 facilities, zones, inventory and readings persist after reconnect", cnt == (1, 1, 1, 4), str(cnt))
    ok_arch = archive_entity(c8b, "appliances", 1) is None and c8b.execute("SELECT COUNT(*) FROM readings").fetchone()[0] == 4
    record("T8b archiving equipment keeps historical readings", ok_arch)

    # --- Test 9: zone with A + B meters not double counted; readings go to the right zone
    c9, f9 = fixture()
    zA = add_zone(c9, f9, "Zone One", "Zone")[2]
    zB = add_zone(c9, f9, "Zone Two", "Zone")[2]
    c1_ = add_circuit(c9, zA, "Lights", "Lighting")[2]
    c2_ = add_circuit(c9, zA, "AC", HV)[2]
    for zid_, cid_, nm, w in ((zA, c1_, "Light", 500), (zA, c2_, "AC", 1000), (zB, None, "Fan", 800)):
        add_appliance(c9, zid_, cid_, None, nm, "Other", 1, w, 100, "Continuous")
    add_meter(c9, "ZONE1-A", "whole zone one", f9, zA, None, None, "A", "t", "kW", 30)
    add_meter(c9, "ZONE1-B1", "lights", f9, zA, c1_, None, "B", "t", "kW", 30)
    add_meter(c9, "ZONE1-B2", "ac", f9, zA, c2_, None, "B", "t", "kW", 30)
    add_meter(c9, "ZONE2-A", "zone two", f9, zB, None, None, "A", "t", "kW", 30)
    grid = pd.date_range("2026-03-11 00:00", "2026-03-11 05:45", freq="15min")
    put(c9, "ZONE1-A", [(t, 1.5) for t in grid]); put(c9, "ZONE1-B1", [(t, 0.5) for t in grid])
    put(c9, "ZONE1-B2", [(t, 1.0) for t in grid]); put(c9, "ZONE2-A", [(t, 0.8) for t in grid])
    an9 = run(c9, f9, a=pd.Timestamp("2026-03-11 00:00"), b=pd.Timestamp("2026-03-11 06:00"), ref=pd.Timestamp("2026-03-11 06:00"))
    expect = (1.5 + 0.8) * 6.0
    zr = c9.execute("SELECT z.name, COUNT(*) FROM readings r JOIN zones z ON z.id=r.zone_id GROUP BY z.name").fetchall()
    record("T9 facility total uses ONE level per zone (no double counting); readings map to correct zones",
           abs(an9["totals"]["measured_kwh"] - expect) < 1e-6 and dict(zr) == {"Zone One": 72, "Zone Two": 24},
           f"measured={an9['totals']['measured_kwh']:.2f} expected={expect:.2f}")

    # --- Test 10: data-source labelling
    record("T10 alerts and readings carry visible data-source labels",
           (an["alerts"]["data_source"].str.contains("Simulated")).all() and "simulated" in SOURCE_LABELS)

    # --- Extra: invalid input handling
    cx, fx = fixture()
    zx = add_zone(cx, fx, "Z", "Zone")[2]
    add_meter(cx, "X-1", "x", fx, zx, None, None, "A", "t", "kW", 30)
    res = ingest_readings(cx, [
        {"timestamp": "2026-03-11 10:00", "meter_id": "X-1", "active_power_kw": 1.0},
        {"timestamp": "2026-03-11 10:00", "meter_id": "X-1", "active_power_kw": 1.0},
        {"timestamp": "bad", "meter_id": "X-1", "active_power_kw": 1.0},
        {"timestamp": "2026-03-11 10:15", "meter_id": "X-1", "active_power_kw": -4},
        {"timestamp": "2026-03-11 10:30", "meter_id": "NOPE", "active_power_kw": 1.0},
        {"timestamp": "2026-03-11 10:45", "meter_id": "X-1", "active_power_kw": "abc"}], now=NOW)
    record("T11 invalid rows (bad time, negative, unknown meter, non-numeric, duplicate) are rejected safely",
           res["inserted"] == 1 and res["duplicates"] == 1 and sum(res["rejected"].values()) == 4, str(res))
    ok_dup, msg_dup, _ = add_meter(cx, "X-1", "again", fx, zx, None, None, "A", "t", "kW", 30)
    record("T12 duplicate meter ID is refused with a clear message", not ok_dup, msg_dup)
    return results


# =============================================================================
# 10. OPTIONAL GATEWAY API (only if fastapi is installed): uvicorn app:api
# =============================================================================
try:
    from fastapi import FastAPI, Header, HTTPException

    api = FastAPI(title="Phantom Watt Hunter ingestion API")

    @api.post("/readings")
    def post_readings(payload: dict, x_api_key: str = Header(default="")):
        """Body: {"readings": [{"timestamp","meter_id","active_power_kw","cumulative_energy_kwh"?}, ...]}.
        Requires env var PWH_API_KEY and header X-API-Key (secure by default)."""
        key = os.environ.get("PWH_API_KEY", "")
        if not key or x_api_key != key:
            raise HTTPException(status_code=401, detail="Missing or invalid API key (set PWH_API_KEY).")
        rows = payload.get("readings")
        if not isinstance(rows, list) or not rows:
            raise HTTPException(status_code=422, detail="'readings' must be a non-empty list.")
        conn = get_conn()
        try:
            return ingest_readings(conn, rows, source="api")
        except ValueError as err:
            raise HTTPException(status_code=422, detail=str(err))
        finally:
            conn.close()
except ImportError:  # fastapi is optional
    api = None


# =============================================================================
# 11. STREAMLIT UI
# =============================================================================
CSS = """<style>
div[data-testid="stMetric"]{background:#f8fafc;border:1px solid #e2e8f0;padding:12px 16px;border-radius:10px;
  box-shadow:0 1px 3px rgba(0,0,0,.06)}
div[data-testid="stMetric"] [data-testid="stMetricLabel"],
div[data-testid="stMetric"] [data-testid="stMetricValue"]{color:#0f172a!important}
.banner{padding:10px 14px;border-radius:6px;margin:6px 0 12px;font-size:.93rem;border-left:5px solid}
.b-sim{background:#eff6ff;border-color:#3b82f6;color:#1e3a8a}
.b-up{background:#fefce8;border-color:#eab308;color:#713f12}
.b-api{background:#f0fdf4;border-color:#22c55e;color:#14532d}
</style>"""
PAGES = ["📊 Dashboard", "🚨 Alerts", "📑 Reports & Export", "🏗️ Inventory", "📟 Meters & Data", "🧪 About & Self-test"]
TIME_RANGES = ["Latest reading (last 30 min)", "Last hour", "Today", "Yesterday", "Last 7 days", "Custom range"]


def flash(msg, kind="success"):
    st.session_state.setdefault("_flash", []).append((kind, msg))


def show_flash():
    for kind, msg in st.session_state.pop("_flash", []):
        getattr(st, kind)(msg)


def show(fig, height=380):
    fig.update_layout(height=height, margin={"l": 10, "r": 10, "t": 40, "b": 10}, template="plotly_white",
                      legend={"orientation": "h", "y": -0.2})
    st.plotly_chart(fig)


def fmt(v, d=1, suffix=""):
    return "n/a" if v is None or pd.isna(v) else f"{v:,.{d}f}{suffix}"


def resolve_range(choice, ref_now, custom):
    ref_now = pd.Timestamp(ref_now)
    today = ref_now.normalize()
    if choice == TIME_RANGES[0]:
        return ref_now - pd.Timedelta(minutes=30), ref_now + pd.Timedelta(minutes=1)
    if choice == "Last hour":
        return ref_now - pd.Timedelta(hours=1), ref_now + pd.Timedelta(minutes=1)
    if choice == "Today":
        return today, today + pd.Timedelta(days=1)
    if choice == "Yesterday":
        return today - pd.Timedelta(days=1), today
    if choice == "Last 7 days":
        return today - pd.Timedelta(days=6), today + pd.Timedelta(days=1)
    d0, d1 = custom
    return pd.Timestamp(d0), pd.Timestamp(d1) + pd.Timedelta(days=1)


def paginate(df, key):
    c1, c2 = st.columns(2)
    size = c1.selectbox("Rows per page", [10, 25, 50, 100], key=f"{key}_size")
    pages = max(1, -(-len(df) // size))
    page = c2.number_input(f"Page (1-{pages})", min_value=1, max_value=pages, value=1, key=f"{key}_page")
    return df.iloc[(int(page) - 1) * size: int(page) * size]


def archived_choice(conn, label, table, where, params, key):
    df = q(conn, f"SELECT id, name, archived_at FROM {table} WHERE active=0 AND {where}", params)
    if df.empty:
        return
    pick = st.selectbox(label, df["id"], format_func=lambda i: f"{df.loc[df['id'] == i, 'name'].iloc[0]} (archived {df.loc[df['id'] == i, 'archived_at'].iloc[0]})", key=key)
    if st.button("Restore", key=key + "_btn"):
        restore_entity(conn, table, pick)
        flash("Restored (with items archived at the same time).")
        st.rerun()


# ---------------------------------------------------------------- Dashboard
def page_dashboard(an, period_label, cfg):
    t = an["totals"]
    st.subheader(f"{an['facility']} - {period_label}")
    counts = an["src_counts"]
    if counts:
        txt = " · ".join(f"{SOURCE_LABELS.get(k, k)}: {v:,} readings" for k, v in counts.items())
        css = "b-sim" if "simulated" in counts else ("b-up" if "uploaded" in counts else "b-api")
        note = " <b>Includes SIMULATED data - not real consumption.</b>" if "simulated" in counts else ""
        st.markdown(f'<div class="banner {css}">Data in view: {txt}.{note} Alerts are <b>suspected anomalies</b>, '
                    f'not confirmed waste.</div>', unsafe_allow_html=True)
    else:
        st.info("No readings in this period/source selection. Import a CSV, load a sample facility, or change the "
                "time range / reference-time option in the sidebar.")
    c = st.columns(4)
    c[0].metric("Measured energy", f"{t['measured_kwh']:,.1f} kWh", help=f"≈ ₹ {t['measured_cost']:,.0f} at the selected tariff")
    c[1].metric("Expected energy", f"{t['expected_kwh']:,.1f} kWh", help="From inventory × schedules, same time intervals as measured.")
    c[2].metric("Est. excess energy", f"{t['excess_kwh']:,.1f} kWh", help="Only well-supported alerts on primary meters; dismissed alerts excluded.")
    c[3].metric("Est. excess cost", f"₹ {t['excess_cost']:,.0f}", help="Estimate, not guaranteed savings.")
    c = st.columns(3)
    c[0].metric("Active alerts", t["active_alerts"])
    c[1].metric("Meters online / stale / offline", f"{t['online']} / {t['stale']} / {t['offline']}")
    c[2].metric("Meters with valid data", f"{t['valid_pct']:.0f}%", help="Share of registered meters that sent valid readings in the period.")
    if t["meters"] == 0:
        st.warning("No meters are registered for this facility yet - add one in 'Meters & Data'.")
        return

    tabs = st.tabs(["Expected vs actual", "Trends", "Zones & circuits", "Cost", "Deviations & off-hours", "Alerts & meter health"])
    z, mdf, alerts = an["zones"], an["meters"], an["alerts"]
    zm = z[z["Monitoring"] != "No meter data"]
    with tabs[0]:
        if zm.empty:
            st.info("No zone has measurement data in this period.")
        else:
            long = zm.melt(id_vars="Zone", value_vars=["Expected kWh", "Measured kWh"], var_name="Type", value_name="kWh")
            show(px.bar(long, x="Zone", y="kWh", color="Type", barmode="group", title="Expected vs measured energy (kWh)"))
        st.dataframe(z.drop(columns=["zone_id"]).round(2), hide_index=True)
        st.caption("Expected and measured are compared over the SAME covered intervals. Unmetered zones show n/a.")
    with tabs[1]:
        hours = (an["eff_end"] - an["start"]).total_seconds() / 3600
        freq = "15min" if hours <= 30 else ("1h" if hours <= 80 else "3h")
        fac, zone_t = trend_tables(an, freq)
        if fac.empty:
            st.info("Not enough complete data for a trend chart (bins where any primary meter is silent are omitted).")
        else:
            f = go.Figure()
            f.add_trace(go.Scatter(x=fac["ts"], y=fac["M"], name="Measured kW", mode="lines"))
            f.add_trace(go.Scatter(x=fac["ts"], y=fac["E"], name="Expected kW", mode="lines", line={"dash": "dash"}))
            f.update_layout(title="Facility power: measured vs expected (kW)", yaxis_title="kW")
            show(f)
            show(px.line(zone_t, x="ts", y="M", color="zone", labels={"M": "Measured kW", "ts": "Time"}, title="Measured power by zone (kW)"))
    with tabs[2]:
        l, r = st.columns(2)
        with l:
            if not zm.empty:
                show(px.pie(zm, names="Zone", values="Measured kWh", hole=0.4, title="Energy share by zone"))
        with r:
            md = mdf[mdf["has_data"]]
            if not md.empty:
                md = md.assign(Label=md["Zone"] + " / " + md["Maps to"].astype(str), Role=md["is_primary"].map({True: "Used in totals", False: "Cross-check only"}))
                show(px.bar(md, x="Label", y="Measured kWh", color="Role", title="Energy by meter / circuit (kWh)"))
        st.dataframe(mdf[["Meter ID", "Zone", "Level", "Maps to", "Measured kWh", "Expected kWh", "is_primary"]].round(2).rename(columns={"is_primary": "Used in totals"}), hide_index=True)
        st.caption("When a zone has several meter levels, only one level feeds the totals so energy is never double counted.")
    with tabs[3]:
        if not zm.empty:
            cost = zm.melt(id_vars="Zone", value_vars=["Measured cost ₹", "Est. excess ₹"], var_name="Type", value_name="₹")
            show(px.bar(cost, x="Zone", y="₹", color="Type", barmode="group", title=f"Cost by zone (₹ at {an['tariff']:.2f}/kWh)"))
    with tabs[4]:
        l, r = st.columns(2)
        with l:
            dev = zm.dropna(subset=["Difference kWh"]).sort_values("Difference kWh", ascending=False)
            if not dev.empty:
                show(px.bar(dev, x="Zone", y="Difference kWh", title="Highest deviations: measured − expected (kWh)"))
        with r:
            if not zm.empty:
                show(px.bar(zm, x="Zone", y="Off-schedule kWh", title="Energy while no scheduled equipment is expected on (kWh)"))
        st.caption("Off-schedule energy includes legitimate always-on loads (e.g. servers, hospital equipment).")
    with tabs[5]:
        l, r = st.columns(2)
        with l:
            if not alerts.empty:
                sev = alerts["severity"].value_counts().reindex(list(SEV_ORDER)).fillna(0).reset_index()
                sev.columns = ["Severity", "Alerts"]
                show(px.bar(sev, x="Severity", y="Alerts", title="Alerts by severity"))
            else:
                st.success("No alerts in this period.")
        with r:
            show(px.bar(mdf, x="Meter ID", y="Coverage %", color="Health", title="Data coverage by meter (%)"))
        st.dataframe(mdf[["Meter ID", "Zone", "Level", "Health", "Last reading", "Age (min)", "Coverage %", "Data sources"]], hide_index=True)


# ------------------------------------------------------------------- Alerts
def page_alerts(conn, an):
    alerts = an["alerts"]
    st.subheader("Alerts - suspected anomalies requiring verification")
    if alerts.empty:
        st.success("No alerts for the selected period and sources.")
        return
    c = st.columns(4)
    sev = c[0].multiselect("Severity", list(SEV_ORDER), default=list(SEV_ORDER))
    zones = c[1].multiselect("Zone", sorted(alerts["zone"].unique()), default=sorted(alerts["zone"].unique()))
    status = c[2].multiselect("Status", ["Open", "Acknowledged", "Assigned", "Resolved", "Dismissed"], default=list(ACTIVE_STATUSES))
    meters = c[3].multiselect("Meter", sorted(alerts["meter"].unique()), default=sorted(alerts["meter"].unique()))
    sort = st.selectbox("Sort by", ["Severity (highest first)", "Newest first", "Highest excess cost"])
    f = alerts[alerts["severity"].isin(sev) & alerts["zone"].isin(zones) & alerts["status"].isin(status) & alerts["meter"].isin(meters)]
    if sort.startswith("Newest"):
        f = f.sort_values("start", ascending=False)
    elif sort.startswith("Highest"):
        f = f.sort_values("excess_cost_inr", ascending=False, na_position="last")
    if f.empty:
        st.info("No alerts match these filters.")
        return
    view = f[["severity", "status", "zone", "rule_label", "monitoring", "meter", "start", "duration_min", "expected_kw",
              "measured_kw", "excess_kwh", "excess_cost_inr", "data_source"]].copy()
    view["start"] = view["start"].dt.strftime("%Y-%m-%d %H:%M")
    st.dataframe(paginate(view, "alerts_tbl"), hide_index=True)
    st.download_button("⬇️ Download filtered alerts (CSV)", f.drop(columns=["key", "meter_pk", "zone_id"]).to_csv(index=False).encode(), "phantom_watt_alerts.csv", "text/csv")

    st.markdown("### Alert details & actions")
    keys = list(f["key"])
    labels = {r["key"]: f"[{r['severity']}] {r['zone']} - {r['rule_label']} - {r['start']:%d %b %H:%M} ({r['status']})" for _, r in f.iterrows()}
    key = st.selectbox("Select an alert", keys, format_func=lambda k: labels[k])
    a = f[f["key"] == key].iloc[0]
    l, r = st.columns([1, 2])
    with l:
        st.markdown(f"**Facility / zone:** {a['facility']} / {a['zone']}  \n**Meter:** {a['meter']}  \n**Monitoring level:** {a['monitoring']}  \n"
                    f"**Detected:** {a['start']:%Y-%m-%d %H:%M} → {a['end']:%H:%M} ({a['duration_min']} min)  \n"
                    f"**Expected / measured:** {fmt(a['expected_kw'], 2)} kW / {fmt(a['measured_kw'], 2)} kW (peak {fmt(a['peak_kw'], 2)})  \n"
                    f"**Est. excess:** {fmt(a['excess_kwh'], 2)} kWh · ₹ {fmt(a['excess_cost_inr'], 0)}  \n"
                    f"**Severity:** {a['severity']} · **Evidence:** {a['evidence']}  \n**Data source:** {a['data_source']}")
    with r:
        st.markdown(f"**Suspected location:** {a['suspected']}  \n**Schedule:** {a['schedule']}  \n**Why it triggered:** {a['explanation']}  \n"
                    f"**Recommended action:** {a['action']}  \n**Evidence note:** {a['evidence_note']}")
        st.caption("Suspected anomaly requiring verification - not proven waste or theft.")
    with st.form("alert_action"):
        c = st.columns(3)
        action = c[0].selectbox("Action", list(STATUS_FOR_ACTION))
        who = c[1].text_input("Assign to (for 'Assign')", value=a["assignee"])
        note = c[2].text_input("Note")
        if st.form_submit_button("Apply"):
            ok, msg = set_alert_status(conn, key, STATUS_FOR_ACTION[action], who, note)
            flash(msg, "success" if ok else "error")
            st.rerun()
    hist = q(conn, "SELECT ts, from_status, to_status, assignee, note FROM alert_history WHERE key=? ORDER BY id DESC", (key,))
    if not hist.empty:
        st.markdown("**History**")
        st.dataframe(hist, hide_index=True)


# ------------------------------------------------------------------ Reports
def page_reports(conn, an, fid, period_label, sources):
    st.subheader("Reports & CSV export")
    st.caption("Every export uses the facility, time range, sources and tariff chosen in the sidebar.")
    rep = build_audit_report(an)
    st.markdown("#### Audit report")
    if rep.empty:
        st.info("No alerts in this period - nothing to audit.")
    else:
        st.dataframe(paginate(rep.drop(columns=["Label"]), "audit_tbl"), hide_index=True)
        st.download_button("⬇️ Audit report (CSV)", rep.to_csv(index=False).encode(), "phantom_watt_audit_report.csv", "text/csv")
    md = build_summary_markdown(an, period_label)
    with st.expander("Facility manager summary (preview)"):
        st.markdown(md)
    c = st.columns(4)
    c[0].download_button("⬇️ Summary report (.md)", md.encode(), "phantom_watt_summary.md", "text/markdown")
    c[1].download_button("⬇️ Alerts (CSV)", an["alerts"].drop(columns=["key", "meter_pk", "zone_id"]).to_csv(index=False).encode(), "phantom_watt_alerts.csv", "text/csv")
    inv = an["apps"][["zone_name", "circuit_name", "name", "category", "quantity", "rated_w", "load_pct", "mode", "schedule_name", "connected_kw", "expected_kw"]]
    c[2].download_button("⬇️ Inventory (CSV)", inv.to_csv(index=False).encode(), "phantom_watt_inventory.csv", "text/csv")
    c[3].download_button("⬇️ Zone summary (CSV)", an["zones"].drop(columns=["zone_id"]).to_csv(index=False).encode(), "phantom_watt_zones.csv", "text/csv")
    if st.checkbox("Prepare readings export for this period"):
        srcs = list(sources) or ["__none__"]
        ph = ",".join("?" * len(srcs))
        rd = q(conn, f"""SELECT r.ts AS timestamp, m.meter_code AS meter_id, r.facility_id, z.name AS zone, c.name AS circuit,
            r.active_power_kw, r.cumulative_energy_kwh, r.data_source, r.quality_status FROM readings r
            JOIN meters m ON m.id=r.meter_id JOIN zones z ON z.id=r.zone_id LEFT JOIN circuits c ON c.id=r.circuit_id
            WHERE r.facility_id=? AND r.ts>=? AND r.ts<? AND r.data_source IN ({ph}) ORDER BY r.ts""",
                (int(fid), fts(an["start"]), fts(an["end"]), *srcs))
        st.download_button(f"⬇️ Readings ({len(rd):,} rows, CSV)", rd.to_csv(index=False).encode(), "phantom_watt_readings.csv", "text/csv")


# ---------------------------------------------------------------- Inventory
def page_inventory(conn, fid, fac_row):
    st.subheader("Inventory management")
    ctx = load_context(conn, fid)
    t_fac, t_zone, t_eq, t_sched, t_arch = st.tabs(["Facility", "Zones & circuits", "Equipment", "Schedules & holidays", "Archive"])

    with t_fac:
        with st.form("edit_facility"):
            c = st.columns(3)
            name = c[0].text_input("Name", value=fac_row["name"])
            ftype = c[1].selectbox("Type", FACILITY_TYPES, index=FACILITY_TYPES.index(fac_row["type"]) if fac_row["type"] in FACILITY_TYPES else len(FACILITY_TYPES) - 1)
            tariff = c[2].number_input("Flat tariff (₹/kWh)", min_value=0.0, value=float(fac_row["tariff_inr"]), step=0.25)
            if st.form_submit_button("Save facility"):
                ok, msg = update_facility(conn, fid, name, ftype, tariff)
                flash(msg, "success" if ok else "error")
                st.rerun()
        with st.form("new_facility", clear_on_submit=True):
            st.markdown("**Create a new facility**")
            c = st.columns(3)
            n = c[0].text_input("Facility name")
            ty = c[1].selectbox("Type", FACILITY_TYPES, key="nf_type")
            tf = c[2].number_input("Flat tariff (₹/kWh)", min_value=0.0, value=8.0, step=0.25, key="nf_tariff")
            if st.form_submit_button("Create facility"):
                ok, msg, _ = add_facility(conn, n, ty, tf)
                flash(msg, "success" if ok else "error")
                st.rerun()
        st.markdown("**Sample facilities** (inventory + meters + clearly labelled SIMULATED readings)")
        c = st.columns([2, 1])
        key = c[0].selectbox("Sample", list(SAMPLES))
        if c[1].button("Load sample facility"):
            ok, msg = load_sample(conn, key)
            flash(msg, "success" if ok else "warning")
            st.rerun()
        if st.button("🗑️ Archive this facility (keeps all history)"):
            archive_entity(conn, "facilities", fid)
            flash("Facility archived. Restore it from the Archive tab.")
            st.rerun()

    with t_zone:
        zones = ctx["zones"]
        with st.form("add_zone", clear_on_submit=True):
            c = st.columns([2, 1])
            zn = c[0].text_input("New zone / floor / building / room name")
            zk = c[1].selectbox("Kind", ZONE_KINDS)
            if st.form_submit_button("Add zone"):
                ok, msg, _ = add_zone(conn, fid, zn, zk)
                flash(msg, "success" if ok else "error")
                st.rerun()
        if zones.empty:
            st.info("No zones yet. Add your first zone above (for example 'Library').")
        else:
            load = ctx["apps"].groupby("zone_id")["connected_kw"].sum()
            tbl = zones[["id", "name", "kind"]].assign(**{"Connected rated load (kW)": zones["id"].map(load).fillna(0).round(3)})
            st.dataframe(tbl.rename(columns={"name": "Zone", "kind": "Kind"}).drop(columns="id"), hide_index=True)
            st.caption("Connected load = Σ quantity × rated W ÷ 1000. It is the nameplate maximum, NOT what the equipment actually uses.")
            c = st.columns(2)
            with c[0].form("add_circuit", clear_on_submit=True):
                zsel = st.selectbox("Zone", zones["id"], format_func=lambda i: zones.loc[zones["id"] == i, "name"].iloc[0], key="circ_zone")
                cn = st.text_input("New circuit name (e.g. 'AC circuit')")
                cc = st.selectbox("Circuit category", CATEGORIES, key="circ_cat")
                if st.form_submit_button("Add circuit"):
                    ok, msg, _ = add_circuit(conn, zsel, cn, cc)
                    flash(msg, "success" if ok else "error")
                    st.rerun()
            with c[1]:
                zsel2 = st.selectbox("Zone to rename / archive", list(zones["id"]), format_func=lambda i: zones.loc[zones["id"] == i, "name"].iloc[0], key="zone_edit")
                zrow = zones[zones["id"] == zsel2].iloc[0]
                with st.form(f"edit_zone_{zsel2}"):
                    nn = st.text_input("New name", value=zrow["name"])
                    nk = st.selectbox("Kind", ZONE_KINDS, index=ZONE_KINDS.index(zrow["kind"]) if zrow["kind"] in ZONE_KINDS else 0, key="zone_kind_edit")
                    b = st.columns(2)
                    if b[0].form_submit_button("Save"):
                        ok, msg = rename_zone(conn, zsel2, nn, nk)
                        flash(msg, "success" if ok else "error")
                        st.rerun()
                    if b[1].form_submit_button("Archive zone"):
                        archive_entity(conn, "zones", zsel2)
                        flash("Zone archived with its equipment and meters. History is kept.")
                        st.rerun()
            if not ctx["circuits"].empty:
                st.dataframe(ctx["circuits"][["zone_name", "name", "category"]].rename(columns={"zone_name": "Zone", "name": "Circuit", "category": "Category"}), hide_index=True)

    with t_eq:
        zones, circuits, scheds, apps = ctx["zones"], ctx["circuits"], ctx["scheds"], ctx["apps"]
        if zones.empty:
            st.info("Create a zone first (Zones & circuits tab).")
        else:
            f = st.columns(4)
            search = f[0].text_input("Search name")
            fz = f[1].multiselect("Zone", list(zones["name"]))
            fc = f[2].multiselect("Category", CATEGORIES)
            fcirc = f[3].multiselect("Circuit", sorted(circuits["name"].unique()))
            v = apps.copy()
            v["Operating h/day"] = v["schedule_id"].map(lambda s: schedule_hours(scheds[int(s)]["s"], scheds[int(s)]["e"]) if pd.notna(s) and int(s) in scheds else 24.0)
            v.loc[v["mode"].isin(["Continuous", "Standby"]), "Operating h/day"] = 24.0
            v["Expected kWh / operating day"] = (v["expected_kw"] * v["Operating h/day"]).round(2)
            if search:
                v = v[v["name"].str.contains(search, case=False, na=False)]
            if fz:
                v = v[v["zone_name"].isin(fz)]
            if fc:
                v = v[v["category"].isin(fc)]
            if fcirc:
                v = v[v["circuit_name"].isin(fcirc)]
            if v.empty:
                st.info("No equipment matches. Add equipment below.")
            else:
                st.dataframe(v[["zone_name", "circuit_name", "name", "category", "quantity", "rated_w", "load_pct", "mode", "schedule_name",
                                "connected_kw", "expected_kw", "Operating h/day", "Expected kWh / operating day"]].rename(columns={
                    "zone_name": "Zone", "circuit_name": "Circuit", "name": "Appliance", "category": "Category", "quantity": "Qty", "rated_w": "Rated W each",
                    "load_pct": "Typical load %", "mode": "Mode", "schedule_name": "Schedule", "connected_kw": "Connected kW", "expected_kw": "Expected kW when on"}).round(3), hide_index=True)
                st.caption("Rated load ≠ expected consumption ≠ measured consumption. Expected kW when on = connected kW × typical load %.")
            zlist, slist, clist = list(zones["id"]), list(scheds), list(circuits["id"])
            zfmt = lambda i: zones.loc[zones["id"] == i, "name"].iloc[0]
            sfmt = lambda i: "(none)" if i is None else scheds[i]["name"] + " - " + scheds[i]["text"]
            cfmt = lambda i: "(none)" if i is None else (circuits.loc[circuits["id"] == i, "zone_name"].iloc[0] + " / " + circuits.loc[circuits["id"] == i, "name"].iloc[0])

            def appliance_form(prefix, row=None):
                c = st.columns(3)
                zi = c[0].selectbox("Zone", zlist, index=zlist.index(int(row["zone_id"])) if row is not None and int(row["zone_id"]) in zlist else 0, format_func=zfmt, key=prefix + "z")
                nm = c[1].text_input("Appliance name", value="" if row is None else row["name"], key=prefix + "n")
                cat = c[2].selectbox("Category", CATEGORIES, index=CATEGORIES.index(row["category"]) if row is not None and row["category"] in CATEGORIES else 0, key=prefix + "c")
                c = st.columns(4)
                qty = c[0].number_input("Quantity", min_value=1, value=1 if row is None else int(row["quantity"]), step=1, key=prefix + "q")
                rw = c[1].number_input("Rated W per unit", min_value=0.0, value=100.0 if row is None else float(row["rated_w"]), step=10.0, key=prefix + "w")
                lp = c[2].number_input("Typical load % when on", min_value=1.0, max_value=100.0, value=100.0 if row is None else float(row["load_pct"]), step=5.0, key=prefix + "l")
                md = c[3].selectbox("Operating mode", MODES, index=0 if row is None else MODES.index(row["mode"]), key=prefix + "m")
                c = st.columns(2)
                copts = [None] + clist
                cur_c = None if row is None or pd.isna(row["circuit_id"]) or int(row["circuit_id"]) not in clist else int(row["circuit_id"])
                ci = c[0].selectbox("Circuit (optional)", copts, index=copts.index(cur_c), format_func=cfmt, key=prefix + "ci")
                sopts = [None] + slist
                cur_s = None if row is None or pd.isna(row["schedule_id"]) or int(row["schedule_id"]) not in slist else int(row["schedule_id"])
                sc = c[1].selectbox("Operating schedule (needed for Scheduled / Intermittent)", sopts, index=sopts.index(cur_s), format_func=sfmt, key=prefix + "s")
                return zi, ci, sc, nm, cat, qty, rw, lp, md

            with st.form("add_appliance", clear_on_submit=True):
                st.markdown("**Add equipment**")
                vals = appliance_form("add_")
                if st.form_submit_button("Add equipment"):
                    ok, msg, _ = add_appliance(conn, vals[0], vals[1], vals[2], *vals[3:])
                    flash(msg, "success" if ok else "error")
                    st.rerun()
            if not apps.empty:
                sel = st.selectbox("Edit or archive existing equipment", list(apps["id"]), format_func=lambda i: f"{apps.loc[apps['id'] == i, 'zone_name'].iloc[0]} - {apps.loc[apps['id'] == i, 'name'].iloc[0]}")
                arow = apps[apps["id"] == sel].iloc[0]
                with st.form(f"edit_appliance_{sel}"):
                    vals = appliance_form(f"edit{sel}_", arow)
                    b = st.columns(2)
                    if b[0].form_submit_button("Save changes"):
                        ok, msg = update_appliance(conn, sel, vals[0], vals[1], vals[2], *vals[3:])
                        flash(msg, "success" if ok else "error")
                        st.rerun()
                    if b[1].form_submit_button("Archive equipment"):
                        archive_entity(conn, "appliances", sel)
                        flash("Equipment archived. Historical readings are kept.")
                        st.rerun()

    with t_sched:
        with st.form("add_schedule", clear_on_submit=True):
            c = st.columns(4)
            sn = c[0].text_input("Schedule name")
            sd = c[1].multiselect("Days", list(range(7)), default=[0, 1, 2, 3, 4], format_func=lambda i: DAY_NAMES[i])
            s0 = c[2].time_input("Start", value=time(9, 0))
            s1 = c[3].time_input("End (earlier than start = overnight)", value=time(18, 0))
            if st.form_submit_button("Add schedule"):
                ok, msg, _ = add_schedule(conn, fid, sn, sd, s0.hour * 60 + s0.minute, s1.hour * 60 + s1.minute)
                flash(msg, "success" if ok else "error")
                st.rerun()
        if ctx["scheds"]:
            st.dataframe(pd.DataFrame([{"Schedule": v["name"], "When": v["text"]} for v in ctx["scheds"].values()]), hide_index=True)
            ds = st.selectbox("Archive a schedule", list(ctx["scheds"]), format_func=lambda i: ctx["scheds"][i]["name"])
            if st.button("Archive schedule"):
                ok, msg = archive_schedule(conn, ds)
                flash(msg, "success" if ok else "error")
                st.rerun()
        st.markdown("**Holidays** (scheduled equipment is expected OFF on these dates)")
        with st.form("add_holiday", clear_on_submit=True):
            c = st.columns(2)
            hd = c[0].date_input("Date", value=date.today())
            hn = c[1].text_input("Name")
            if st.form_submit_button("Add holiday"):
                ok, msg = add_holiday(conn, fid, hd, hn)
                flash(msg, "success" if ok else "error")
                st.rerun()
        hol = q(conn, "SELECT id, hdate, name FROM holidays WHERE facility_id=? ORDER BY hdate", (int(fid),))
        if not hol.empty:
            st.dataframe(hol.drop(columns="id"), hide_index=True)
            hid = st.selectbox("Remove holiday", list(hol["id"]), format_func=lambda i: hol.loc[hol["id"] == i, "hdate"].iloc[0])
            if st.button("Remove holiday"):
                conn.execute("DELETE FROM holidays WHERE id=?", (int(hid),))
                conn.commit()
                st.rerun()

    with t_arch:
        st.caption("Archiving hides items but never deletes readings. Restoring a parent restores items archived with it.")
        archived_choice(conn, "Archived facilities", "facilities", "1=1", (), "arch_f")
        archived_choice(conn, "Archived zones (this facility)", "zones", "facility_id=?", (int(fid),), "arch_z")
        archived_choice(conn, "Archived equipment", "appliances", "zone_id IN (SELECT id FROM zones WHERE facility_id=?)", (int(fid),), "arch_a")
        archived_choice(conn, "Archived meters", "meters", "facility_id=?", (int(fid),), "arch_m")
        archived_choice(conn, "Archived schedules", "schedules", "facility_id=?", (int(fid),), "arch_s")


# ------------------------------------------------------------ Meters & data
SAMPLE_PAYLOAD = {"readings": [{"timestamp": "2026-03-11T14:00:00", "meter_id": "PLAY-1", "active_power_kw": 2.05,
                                "cumulative_energy_kwh": 1523.4}]}


def page_meters(conn, fid, an, fac_row, sources_all):
    st.subheader("Meters & data")
    ctx = load_context(conn, fid)
    t_reg, t_add, t_imp, t_api, t_sim = st.tabs(["Registry & health", "Register meter", "Import CSV", "Gateway / API", "Simulation"])
    with t_reg:
        mdf = an["meters"]
        if mdf.empty:
            st.info("No meters registered for this facility.")
        else:
            st.dataframe(mdf[["Meter ID", "Name", "Level", "Zone", "Maps to", "Health", "Last reading", "Age (min)", "Timeout (min)", "Data sources", "Readings in period", "Suspect readings (excluded)", "Coverage %"]], hide_index=True)
            st.caption("Online: reported within its timeout. Stale: up to 3× timeout. Offline: older. Missing data is never counted as zero.")
            sel = st.selectbox("Archive a meter (history kept)", list(mdf["meter_pk"]), format_func=lambda i: mdf.loc[mdf["meter_pk"] == i, "Meter ID"].iloc[0])
            if st.button("Archive meter"):
                archive_entity(conn, "meters", sel)
                flash("Meter archived.")
                st.rerun()
    with t_add:
        zones, circuits, apps = ctx["zones"], ctx["circuits"], ctx["apps"]
        if zones.empty:
            st.info("Create a zone first.")
        else:
            with st.form("add_meter", clear_on_submit=True):
                c = st.columns(3)
                code = c[0].text_input("Meter ID (unique, no spaces)")
                nm = c[1].text_input("Name")
                lv = c[2].selectbox("Monitoring level", list(LEVEL_NAMES), format_func=lambda k: LEVEL_NAMES[k])
                c = st.columns(3)
                zi = c[0].selectbox("Zone", list(zones["id"]), format_func=lambda i: zones.loc[zones["id"] == i, "name"].iloc[0], key="m_zone")
                copts = [None] + list(circuits["id"])
                ci = c[1].selectbox("Circuit (Level B/C)", copts, format_func=lambda i: "(none)" if i is None else circuits.loc[circuits["id"] == i, "zone_name"].iloc[0] + " / " + circuits.loc[circuits["id"] == i, "name"].iloc[0], key="m_circ")
                aopts = [None] + list(apps["id"])
                ai = c[2].selectbox("Appliance (Level C)", aopts, format_func=lambda i: "(none)" if i is None else apps.loc[apps["id"] == i, "zone_name"].iloc[0] + " / " + apps.loc[apps["id"] == i, "name"].iloc[0], key="m_app")
                c = st.columns(3)
                pr = c[0].selectbox("Protocol", ["CSV/API", "Modbus RTU (RS-485)", "Modbus TCP", "MQTT", "Other"])
                un = c[1].selectbox("Power unit in raw data", ["kW", "W"])
                to = c[2].number_input("Offline timeout (minutes)", min_value=1, value=30)
                if st.form_submit_button("Register meter"):
                    ok, msg, _ = add_meter(conn, code, nm, fid, zi, ci, ai, lv, pr, un, to)
                    flash(msg, "success" if ok else "error")
                    st.rerun()
            st.caption("Level A = whole zone, B = one circuit (pick circuit), C = one appliance (pick appliance).")
    with t_imp:
        st.markdown("CSV columns: `timestamp, meter_id, active_power_kw` (or `active_power_w`), optional `cumulative_energy_kwh`. "
                    "Timestamps are treated as local time (offsets ignored). Rows are stored as **📂 Uploaded CSV**.")
        tmpl = pd.DataFrame({"timestamp": ["2026-03-11 14:00:00"], "meter_id": ["PLAY-1"], "active_power_kw": [2.05], "cumulative_energy_kwh": [1523.4]})
        st.download_button("⬇️ CSV template", tmpl.to_csv(index=False).encode(), "readings_template.csv", "text/csv")
        up = st.file_uploader("Upload readings CSV", type=["csv"], key="read_csv")
        if up is not None and st.button("Import readings"):
            try:
                res = ingest_readings(conn, pd.read_csv(up), source="uploaded")
                st.success(f"Received {res['received']:,} · inserted {res['inserted']:,} · duplicates skipped {res['duplicates']:,} · flagged suspect {res['suspect']:,}")
                if res["rejected"]:
                    st.warning("Rejected rows: " + "; ".join(f"{v} × {k}" for k, v in res["rejected"].items()))
            except (ValueError, pd.errors.ParserError, pd.errors.EmptyDataError) as err:
                st.error(f"Could not import: {err}")
    with t_api:
        st.markdown("**Target architecture:** meters → RS-485/Modbus → gateway/data logger → **API** → database → analytics → dashboard. "
                    "The gateway only *collects* readings; it does not identify appliances. **No physical gateway is connected in this build** - "
                    "the endpoint below and the CSV importer share one validated ingestion function (tested), but real-hardware polling is not implemented.")
        st.code("pip install fastapi uvicorn\nset PWH_API_KEY=choose-a-secret      # Windows (use export on Linux/Mac)\nuvicorn app:api --port 8000\n\n"
                "curl -X POST http://localhost:8000/readings -H \"X-API-Key: choose-a-secret\" -H \"Content-Type: application/json\" -d @payload.json", language="bash")
        st.code(json.dumps(SAMPLE_PAYLOAD, indent=2), language="json")
        st.caption("The API stores rows as '📡 Gateway/API (unverified)'. Streamlit Community Cloud cannot host this endpoint; run it on a server that shares the same database file.")
        txt = st.text_area("Test the ingestion logic here (pasted JSON, stored as 'uploaded')", value=json.dumps(SAMPLE_PAYLOAD, indent=2), height=170)
        if st.button("Ingest pasted JSON"):
            try:
                res = ingest_readings(conn, json.loads(txt)["readings"], source="uploaded")
                st.success(f"Inserted {res['inserted']} · duplicates {res['duplicates']} · rejected {res['rejected'] or 0}")
            except (ValueError, KeyError, TypeError, json.JSONDecodeError) as err:
                st.error(f"Invalid payload: {err}")
    with t_sim:
        st.warning("Simulated readings are synthetic demonstration data - never real consumption.")
        if fac_row["sample_key"] in SAMPLES:
            if st.button("🔄 Regenerate simulated readings (new random variation)"):
                ok, msg = generate_sim_readings(conn, fid)
                flash(msg, "success" if ok else "error")
                st.rerun()
            st.caption("Scenarios: after-hours loads, overnight AC, elevated idle load, a meter going offline, missing readings, and legitimate always-on loads.")
        else:
            st.info("This facility is not a sample facility. Load a sample from Inventory → Facility.")
        if st.button("Delete ALL simulated readings for this facility"):
            conn.execute("DELETE FROM readings WHERE data_source='simulated' AND facility_id=?", (int(fid),))
            conn.commit()
            flash("Simulated readings deleted.")
            st.rerun()


# --------------------------------------------------------- About & self-test
def page_about():
    st.subheader("About, limitations & self-test")
    if st.button("▶ Run acceptance self-tests (uses temporary databases)"):
        res = run_self_tests()
        st.dataframe(pd.DataFrame([{"Test": n, "Result": "✅ PASS" if ok else "❌ FAIL", "Detail": d} for n, ok, d in res]), hide_index=True)
        (st.success if all(ok for _, ok, _ in res) else st.error)(f"{sum(ok for _, ok, _ in res)}/{len(res)} tests passed")
    st.markdown(f"""
**Database:** `{DB_PATH}` (SQLite). Tables: facilities, zones, circuits, schedules, holidays, appliances, meters, readings,
alert_states, alert_history, settings. Alerts are re-computed from readings; only their workflow state is stored.

**Deployment:** Streamlit Community Cloud storage is ephemeral - the SQLite file can reset when the app restarts. For real use,
host it where the file persists (own server/VM/Docker volume) or migrate to PostgreSQL.

**Known limitations**
- Real meter hardware is not connected. Modbus/RS-485 polling is a future gateway module; only CSV/JSON/API ingestion exists.
- Statistical baseline rule only; no machine learning. Flat tariff only. Timestamps are local time.
- Expected power depends on the load % you enter; poor inventory data gives poor expectations.
- Alerts are suspected anomalies - they need on-site verification before anyone calls them waste or theft.
""")


# -------------------------------------------------------------------- main
def main():
    st.set_page_config(page_title="Phantom Watt Hunter", page_icon="⚡", layout="wide")
    st.markdown(CSS, unsafe_allow_html=True)
    conn = get_conn()
    try:
        if conn.execute("SELECT COUNT(*) FROM facilities").fetchone()[0] == 0 and "seeded" not in st.session_state:
            st.session_state["seeded"] = True
            load_sample(conn, "College Campus")
        cfg0 = load_settings(conn)
        st.sidebar.title("⚡ Phantom Watt Hunter")
        page = st.sidebar.radio("Navigate", PAGES)
        facs = q(conn, "SELECT * FROM facilities WHERE active=1 ORDER BY name")
        st.title("⚡ Phantom Watt Hunter")
        show_flash()
        if facs.empty:
            st.info("No facilities yet. Create one below, or load a sample facility.")
            fid, fac_row = None, None
        else:
            fid = st.sidebar.selectbox("Facility", list(facs["id"]), format_func=lambda i: facs.loc[facs["id"] == i, "name"].iloc[0])
            fac_row = facs[facs["id"] == fid].iloc[0]
            fid = int(fid)
        if fid is None:
            page_inventory_empty(conn)
            return
        if page.startswith("🧪"):
            page_about()
            return
        if page.startswith("🏗️"):
            page_inventory(conn, fid, fac_row)
            return

        # ---- global filters
        src_all = q(conn, "SELECT DISTINCT data_source FROM readings WHERE facility_id=?", (fid,))["data_source"].tolist()
        sources = st.sidebar.multiselect("Data sources", list(SOURCE_LABELS), default=[s for s in SOURCE_LABELS if s in src_all] or list(SOURCE_LABELS), format_func=lambda s: SOURCE_LABELS[s])
        ref_mode = st.sidebar.radio("Reference time ('now')", ["Current clock", "Latest data in database"], index=0 if cfg0["ref_mode"] == "clock" else 1,
                                    help="Meter health is judged against this. Use 'Latest data' for old uploaded files.")
        srcs = list(sources) or ["__none__"]
        latest = q(conn, f"SELECT MAX(ts) AS t FROM readings WHERE facility_id=? AND data_source IN ({','.join('?' * len(srcs))})", (fid, *srcs))["t"].iloc[0]
        ref_now = pd.Timestamp(latest) if ref_mode.startswith("Latest") and latest else pd.Timestamp.now()
        choice = st.sidebar.selectbox("Time range", TIME_RANGES, index=4)
        custom = None
        if choice == "Custom range":
            rng = st.sidebar.date_input("Dates", value=(ref_now.date() - timedelta(days=1), ref_now.date()))
            if not isinstance(rng, (tuple, list)) or len(rng) != 2:
                st.info("Pick both a start and an end date in the sidebar.")
                return
            custom = rng
        start, end = resolve_range(choice, ref_now, custom)
        st.sidebar.markdown("**Tariff (flat)**")
        tariff = st.sidebar.number_input("₹ per kWh", min_value=0.0, value=float(fac_row["tariff_inr"]), step=0.25, key=f"tariff_{fid}")
        if tariff != float(fac_row["tariff_inr"]) and st.sidebar.button("Save as facility tariff"):
            conn.execute("UPDATE facilities SET tariff_inr=? WHERE id=?", (float(tariff), fid))
            conn.commit()
            st.rerun()
        with st.sidebar.expander("Detection tolerances"):
            cfg = dict(cfg0)
            cfg["tolerance_pct"] = st.slider("Tolerance above expected (%)", 0, 100, int(cfg0["tolerance_pct"]), 5)
            cfg["floor_kw"] = st.number_input("Minimum margin (kW)", min_value=0.0, value=float(cfg0["floor_kw"]), step=0.05)
            cfg["spike_pct"] = st.slider("Spike vs history (%)", 10, 300, int(cfg0["spike_pct"]), 10)
            cfg["min_hist_days"] = st.number_input("Min. days of history for spike rule", min_value=2, value=int(cfg0["min_hist_days"]))
            cfg["night_start"] = st.number_input("Night starts (hour)", min_value=0, max_value=23, value=int(cfg0["night_start"]))
            cfg["night_end"] = st.number_input("Night ends (hour)", min_value=0, max_value=23, value=int(cfg0["night_end"]))
            cfg["ref_mode"] = "clock" if ref_mode.startswith("Current") else "latest"
            if st.button("Save as defaults"):
                save_settings(conn, cfg)
                flash("Detection settings saved.")
                st.rerun()

        an = analyze_facility(conn, fid, start, end, tariff, cfg, sources, ref_now)
        if page.startswith("📊"):
            page_dashboard(an, choice, cfg)
        elif page.startswith("🚨"):
            page_alerts(conn, an)
        elif page.startswith("📑"):
            page_reports(conn, an, fid, choice, sources)
        else:
            page_meters(conn, fid, an, fac_row, src_all)
    finally:
        conn.close()


def page_inventory_empty(conn):
    with st.form("first_facility"):
        n = st.text_input("Facility name")
        if st.form_submit_button("Create facility"):
            ok, msg, _ = add_facility(conn, n, "Other", 8.0)
            flash(msg, "success" if ok else "error")
            st.rerun()
    key = st.selectbox("Or load a sample (simulated)", list(SAMPLES))
    if st.button("Load sample facility"):
        flash(load_sample(conn, key)[1])
        st.rerun()


if __name__ == "__main__":
    main()
