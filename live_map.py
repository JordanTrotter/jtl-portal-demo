"""Live conditions map for one property. Standard library plus h5py for lightning, serves on localhost.

    python live_map.py --boundary "<boundary.geojson>" --name "<Property Name>"

Pulls public feeds server-side so raw SCFC records never reach the browser.
"""
import argparse
import csv
import io
import json
import math
import re
import secrets
import threading
import time
import urllib.parse
import urllib.request
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

HERE = Path(__file__).parent
# NWS rejects an empty User-Agent but does not need contact info; no email or personal detail goes out with any request
UA = "jt-live-map/0.2"
FIRE_RADIUS_MI = 50  # 25 until 2026-11-12; 50 for the partner demo so a live fire is likelier to show (page text says 50 too)
RECENT_DAYS = 7
STORM_RADIUS_MI = 500
INACTIVE = {"contained", "controlled", "mopped up", "out", "closed"}
FIRESPONSE = {"GA": "georgiafc", "SC": "scfc"}
FIRMS = "https://firms.modaps.eosdis.nasa.gov/data/active_fire/"
FIRMS_FILES = {
    "VIIRS NOAA-20": "noaa-20-viirs-c2/csv/J1_VIIRS_C2_USA_contiguous_and_Hawaii_7d.csv",
    "VIIRS NOAA-21": "noaa-21-viirs-c2/csv/J2_VIIRS_C2_USA_contiguous_and_Hawaii_7d.csv",
    "VIIRS Suomi NPP": "suomi-npp-viirs-c2/csv/SUOMI_VIIRS_C2_USA_contiguous_and_Hawaii_7d.csv",
    "MODIS": "modis-c6.1/csv/MODIS_C6_1_USA_contiguous_and_Hawaii_7d.csv",
}
HEAT_HOURS = 24  # live fires are the last 24 hours; the 7 day files are history for the checks below
HISTORY_HOURS = 24 * 7
PASS_GAP_MIN = 20  # two detections this far apart are separate satellite passes, so a glint or one bad scan cannot confirm
LONG_RUN_DAYS = 3  # heat on this many separate days is a pile, mill or landfill, not a new fire
# US lightning fires: about half reported the same day, 71% within 3 days, 77% within 7 (Schultz et al. 2019, Fire 2:18).
# Past 3 days the gain is small and a big storm leaves strikes near almost any field burn, so the fast-track stops there.
# A later fire is still caught by the 2-pass rule, which only costs the hours until the next pass.
STRIKE_DAYS = 3
HOLDOVER_MI = 1  # GLM is good to a couple of km, so "on the property" means inside or within this of the line
# Primed for a lightning fire: fire danger High or worse and almost no rain over the strike window.
# Ignition odds climb sharply when a storm drops under 2-3 mm (Dowdy, MODSIM 2015), so a soaking storm is not primed.
PRIMED_RATINGS = ("High", "Very High", "Extreme")
PRIMED_RAIN_IN = 0.1
STRIKE_MATCH_MI = 3  # GLM places flashes to within a few miles
STATE = HERE / "state"
# A later clear look that sees nothing retires heat: 2 misses for any spot, then it leaves the map.
# A look = a polar pass with the spot well inside the swath (edge pixels are coarse and miss small fires),
# already in the FIRMS files (they lag the pass by hours), with GOES calling that pixel clear at the time.
# Clouds never count as a miss.
TLE = "https://celestrak.org/NORAD/elements/gp.php?CATNR={}&FORMAT=TLE"  # public orbit data
POLAR = {"Suomi NPP": (37849, 1000), "NOAA-20": (43013, 1000), "NOAA-21": (54234, 1000), "Aqua": (27424, 800), "Terra": (25994, 800)}  # NORAD id, good half swath km
FIRMS_SAT = {"VIIRS NOAA-20": "NOAA-20", "VIIRS NOAA-21": "NOAA-21", "VIIRS Suomi NPP": "Suomi NPP", "A": "Aqua", "T": "Terra"}
GOES_CLEAR, GOES_CLOUD = 100, 200  # FDC mask: 100 processed no fire (clear); 200 and up cloud tests
MISSES_TO_DROP = {False: 2, True: 2}  # keyed by confirmed; Waters 2026-11-12: 2 clear misses for any spot, then off the map
MODIS_MIN_CONFIDENCE = 30  # MODIS gives 0-100; under 30 is FIRMS' "low" class, same cut as VIIRS "low"
GOES_PRODUCT = "ABI-L2-FDCC"  # CONUS fire product, a scan every 5 min, same bucket as GLM
GOES_MINUTES = 30
# fire pixel codes: processed, saturated, cloud contaminated, high probability, and the same four
# temporally filtered (30-33). Medium and low probability (14, 15, 34, 35) are left out as too noisy.
GOES_FIRE = (10, 11, 12, 13, 30, 31, 32, 33)
GOES_SPACING_MI = 3  # GOES pixels run about 2 x 3 km here, so a finer hit within 3 mi is the same fire
# All weather from public domain NOAA and NWS services, no keys.
METAR = "https://aviationweather.gov/api/data/metar"  # airport observations, one call for a box
METAR_MAX_AGE = 5400  # seconds; older airport reports drop out of the wind grid
# NWS precipitation analysis: radar plus gauges, quality checked by the River Forecast Centers, about 4 km.
QPE = "https://mapservices.weather.noaa.gov/raster/rest/services/obs/rfc_qpe/MapServer/identify"
# image layer ids in that service (each group title id + 3)
QPE_LAYERS = {"rain_1h": 8, "rain_3d": 40, "pct_30d": 227}
CPC = "https://mapservices.weather.noaa.gov/vector/rest/services/outlooks/"
USDM = "https://usdmdataservices.unl.edu/api/CountyStatistics/GetDroughtSeverityStatisticsByAreaPercent"
USDM_NAMES = ("Abnormally dry (D0)", "Moderate drought (D1)", "Severe drought (D2)", "Extreme drought (D3)", "Exceptional drought (D4)")
STATE_FIPS = dict(zip("AL AK AZ AR CA CO CT DE DC FL GA HI ID IL IN IA KS KY LA ME MD MA MI MN MS MO MT NE NV NH NJ NM NY NC ND OH OK OR PA RI SC SD TN TX UT VT VA WA WV WI WY".split(),
                      "01 02 04 05 06 08 09 10 11 12 13 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40 41 42 44 45 46 47 48 49 50 51 53 54 55 56".split()))
WIND_N, WIND_STEP = 7, 0.25  # 7 x 7 points, about 17 mi apart, covers about 50 mi each way
AREA_MI = 50  # weather tiles (radar, clouds, Sentinel-2) only load inside this box around the property
TTL = {"nws": 300, "fires": 600, "storms": 900, "burn": 1800, "raws": 600, "lightning": 120, "imagery": 3600, "basemaps": 86400, "fire_class": 3600, "wind": 900, "rain": 900, "climate": 21600}
RAWS = "https://services3.arcgis.com/T4QMspbfLg3qTGWY/arcgis/rest/services/PublicView_RAWS/FeatureServer/1/query"
STAC = "https://planetarycomputer.microsoft.com/api/stac/v1/search"
MOSAIC = "https://planetarycomputer.microsoft.com/api/data/v1/mosaic/register"
IMAGERY_DAYS = 45
# Clouds are judged over the tract itself, from each scene's own classification band (SCL), not the whole 70 mi scene,
# so a pass that is clear over the property is used even when the rest of the scene is cloudy.
STATS = "https://planetarycomputer.microsoft.com/api/data/v1/item/statistics"
CLOUD_CLASSES = {3, 8, 9, 10}  # SCL: cloud shadow, cloud medium and high probability, thin cirrus
TRACT_MAX_CLOUD = 1  # percent of the tract's pixels
SEARCH_MAX_CLOUD = 95  # scene-wide cut only to skip fully overcast passes before checking the tract
BASE_MAX_CLOUD = 5  # the rest of the map: whole scenes this clear, newest first, so the area around the tract is filled
MAX_CHECKS = 20  # scenes checked per pull, newest first; each check is about 1 s
GLM_BUCKET = "https://noaa-goes19.s3.amazonaws.com"
LIGHTNING_MINUTES = 15
STATION_TIE_MI = 5  # within this, a fire weather station beats an airport: it sits in the woods and reports fuel moisture
# Official 7-day outlook from the national Predictive Services (NIFC/GACCs), public, no key. Replaced the FEMS
# station estimate 2026-11-11: that needed fresh RAWS, and the NIFC RAWS feed had gone 23 h stale near the test tract.
FD_CLASS = "https://www.wfas.net/images/firedanger/fd_cls_f.png"  # forecast map; fd_class.png is observed, two days behind
FD_NAMES = ("Very Low", "Low", "Moderate", "High", "Very High", "Extreme")
FD_LEGEND_X = (312, 487, 662, 837, 1012, 1187)
FD_LEGEND_Y = 815
LIGHTNING_WATCH_MI = 10
HEAT_WARNING_MI = 2  # GFC/SCFC wildfires and confirmed non-lightning fires: Warning to here (Waters, 2026-11-11), Watch to 15 mi


def fetch_bytes(url):
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    with urllib.request.urlopen(req, timeout=25) as r:
        return r.read()


def get(url, accept="application/json", raw=False):
    req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept": accept})
    with urllib.request.urlopen(req, timeout=25) as r:
        body = r.read().decode("utf-8", "replace")
    return body if raw else json.loads(body)


# --- geometry -------------------------------------------------------------

def miles(lat1, lon1, lat2, lon2):
    a, b = math.radians(lat1), math.radians(lat2)
    h = math.sin((b - a) / 2) ** 2 + math.cos(a) * math.cos(b) * math.sin(math.radians(lon2 - lon1) / 2) ** 2
    return 3958.8 * 2 * math.asin(math.sqrt(h))


def bearing(lat1, lon1, lat2, lon2):
    a, b, d = math.radians(lat1), math.radians(lat2), math.radians(lon2 - lon1)
    deg = math.degrees(math.atan2(math.sin(d) * math.cos(b), math.cos(a) * math.sin(b) - math.sin(a) * math.cos(b) * math.cos(d)))
    return ["N", "NE", "E", "SE", "S", "SW", "W", "NW"][round((deg % 360) / 45) % 8]


def rings(geojson):
    for f in geojson["features"]:
        g = f["geometry"]
        polys = g["coordinates"] if g["type"] == "MultiPolygon" else [g["coordinates"]]
        for poly in polys:
            yield from poly


def inside(rs, lat, lon):
    hit = False
    for ring in rs:
        for (x1, y1, *_), (x2, y2, *_) in zip(ring, ring[1:]):
            if (y1 > lat) != (y2 > lat) and lon < x1 + (lat - y1) * (x2 - x1) / (y2 - y1):
                hit = not hit
    return hit


class Place:
    def __init__(self, geojson, name):
        self.name = name
        self.rings = list(rings(geojson))
        # ponytail: nearest vertex, fine at these distances; boundary edges are short
        self.points = [(p[1], p[0]) for r in self.rings for p in r]
        lats, lons = zip(*self.points)
        self.lat, self.lon = (min(lats) + max(lats)) / 2, (min(lons) + max(lons)) / 2

    def distance(self, lat, lon):
        if inside(self.rings, lat, lon):
            return 0.0
        return min(miles(lat, lon, a, b) for a, b in self.points)

    def locate(self, lat, lon):
        d = self.distance(lat, lon)
        return {"lat": lat, "lon": lon, "miles": round(d, 1), "dir": bearing(self.lat, self.lon, lat, lon)}


# --- NWS ------------------------------------------------------------------

def compass(deg):
    return None if deg is None else ["N", "NE", "E", "SE", "S", "SW", "W", "NW"][round((deg % 360) / 45) % 8]


def val(q, scale=1.0, plus=0.0, nd=0):
    v = (q or {}).get("value")
    return None if v is None else round(v * scale + plus, nd or None)


def span(valid):
    start, dur = valid.split("/")
    m = re.match(r"P(?:(\d+)D)?(?:T(?:(\d+)H)?)?", dur)
    return datetime.fromisoformat(start), timedelta(days=int(m[1] or 0), hours=int(m[2] or 0))


def at(series, now):
    for v in (series or {}).get("values", []):
        s, d = span(v["validTime"])
        if s <= now < s + d:
            return v["value"]
    return None


def within(series, now, hours):
    end = now + timedelta(hours=hours)
    return [(v["value"], *span(v["validTime"])) for v in (series or {}).get("values", [])
            if v["value"] is not None and span(v["validTime"])[0] < end and sum(span(v["validTime"]), timedelta()) > now]


def latest_obs(stations):
    for s in stations[:5]:
        o = get(f"https://api.weather.gov/stations/{s}/observations/latest")["properties"]
        age = datetime.now(timezone.utc) - datetime.fromisoformat(o["timestamp"])
        if age < timedelta(hours=2) and o["temperature"]["value"] is not None:
            return s, o
    raise RuntimeError("no recent station report")


def pull_nws(place, _):
    pt = get(f"https://api.weather.gov/points/{place.lat:.3f},{place.lon:.3f}")["properties"]
    rel = pt["relativeLocation"]["properties"]
    county = get(pt["county"])["properties"]["name"]
    stations = [f["properties"]["stationIdentifier"] for f in get(pt["observationStations"])["features"]]
    sid, o = latest_obs(stations)
    station = get(f"https://api.weather.gov/stations/{sid}")
    slon, slat = station["geometry"]["coordinates"][:2]
    g = get(pt["forecastGridData"])["properties"]
    fc = get(pt["forecast"])["properties"]["periods"]
    alerts = get(f"https://api.weather.gov/alerts/active?point={place.lat:.2f},{place.lon:.2f}", "application/geo+json")
    now = datetime.now(timezone.utc)
    f_mi = 2.23694
    return {
        "state": rel["state"], "county": county, "near": rel["city"],
        "fire_zone": pt["fireWeatherZone"].rsplit("/", 1)[1], "county_zone": pt["county"].rsplit("/", 1)[1],
        "conditions": {
            "station": f"{sid}, {station['properties']['name']}",
            "station_miles": round(place.distance(slat, slon)), "lat": slat, "lon": slon,
            "observed": o["timestamp"], "sky": o["textDescription"], "sky_cover": at(g.get("skyCover"), now),
            "temp_f": val(o["temperature"], 1.8, 32), "humidity": val(o["relativeHumidity"]),
            "dew_f": val(o["dewpoint"], 1.8, 32),
            "wind_mph": val(o["windSpeed"], 0.621371), "wind_dir": compass(o["windDirection"]["value"]),
            "gust_mph": val(o["windGust"], 0.621371),
            "pressure_inhg": val(o["barometricPressure"], 0.0002953, nd=2),
            "visibility_mi": val(o["visibility"], 0.000621371, nd=1),
        },
        "fire_weather": {
            "humidity_now": at(g.get("relativeHumidity"), now),
            "humidity_min_24h": min((v[0] for v in within(g.get("relativeHumidity"), now, 24)), default=None),
            "wind_20ft_mph": _kmh(at(g.get("twentyFootWindSpeed"), now)),
            "gust_max_24h": _kmh(max((v[0] for v in within(g.get("windGust"), now, 24)), default=None)),
            "mixing_height_ft": _round(at(g.get("mixingHeight"), now), 3.28084, 100),
            "transport_wind_mph": _kmh(at(g.get("transportWindSpeed"), now)),
            "transport_wind_dir": compass(at(g.get("transportWindDirection"), now)),
            "dispersion_index": at(g.get("atmosphericDispersionIndex"), now),
            "low_visibility_risk": at(g.get("lowVisibilityOccurrenceRiskIndex"), now),
            "rain_chance_24h": max((v[0] for v in within(g.get("probabilityOfPrecipitation"), now, 24)), default=None),
            "rain_in_24h": round(sum(v[0] for v in within(g.get("quantitativePrecipitation"), now, 24)) / 25.4, 2),
        },
        "forecast": [{"name": p["name"], "temp": p["temperature"], "unit": p["temperatureUnit"],
                      "wind": f"{p['windDirection']} {p['windSpeed']}", "short": p["shortForecast"],
                      "rain": (p.get("probabilityOfPrecipitation") or {}).get("value")} for p in fc[:6]],
        "alerts": [{"event": a["event"], "severity": a["severity"], "urgency": a["urgency"],
                    "headline": a.get("headline"), "ends": a.get("ends") or a.get("expires")}
                   for a in (f["properties"] for f in alerts["features"])],
    }


def _kmh(v):
    return None if v is None else round(v * 0.621371)


def _round(v, scale, step):
    return None if v is None else int(round(v * scale / step) * step)


# --- fire -----------------------------------------------------------------

def is_active(p):
    return str(p.get("Status", "")).lower() not in INACTIVE


def pull_incidents(place, site):
    out = []
    for f in get(f"https://{site}.firesponse.com/public/api/Incident/geojson")["features"]:
        p, (lon, lat) = f["properties"], f["geometry"]["coordinates"][:2]
        active = is_active(p)
        if place.distance(lat, lon) > FIRE_RADIUS_MI or (not active and (p.get("differenceOfDays") or 0) > RECENT_DAYS):
            continue
        rx = "prescribed" in str(p.get("Category", "")).lower()
        # ponytail: fiResponse has no per-fire page, so the link opens the agency's public map
        out.append({"kind": "rx" if rx else "wildfire", "active": active, "source": site, "name": p.get("Name"),
                    "status": p.get("Status"), "acres": p.get("Size"), "contained": p.get("Contained"),
                    "county": p.get("AdminDivision"), "reported": utc(p.get("reporteddate")), "number": p.get("Number"),
                    "link": f"https://{site}.firesponse.com/public/", **place.locate(lat, lon)})
    return out


def utc(stamp):
    """fiResponse times are UTC but carry no zone; a browser would read them as local."""
    s = str(stamp or "")
    return s + "+00:00" if s and not re.search(r"(Z|[+-]\d\d:?\d\d)$", s) else (s or None)


def notice_points(rows):
    """Keep location, county and date only. The feed carries names, phones and IP addresses; drop them here."""
    out = []
    for r in rows:
        try:
            a, b = float(r["15"]), float(r["16"])
        except (KeyError, TypeError, ValueError):
            continue
        lat, lon = (a, b) if a > 0 else (b, a)
        if 24 < lat < 50 and -125 < lon < -66:
            out.append({"lat": lat, "lon": lon, "county": r.get("9"), "reported": r.get("date_created")})
    return out


def pull_notices(place):
    rows = get("https://www.scfc.gov/wp-json/scfcapi/v2/notifications/")
    # Gravity Forms stores date_created in UTC
    return [{"kind": "burn", "source": "scfc notice", "county": n["county"], "reported": str(n["reported"]).replace(" ", "T") + "+00:00",
             **place.locate(n["lat"], n["lon"])}
            for n in notice_points(rows) if place.distance(n["lat"], n["lon"]) <= FIRE_RADIUS_MI]


def confident(c):
    return int(c) >= MODIS_MIN_CONFIDENCE if c.isdigit() else c not in ("low", "l")


def firms_rows(text, sat, place, now=None, hours=HEAT_HOURS):
    cutoff = (now or datetime.now(timezone.utc)) - timedelta(hours=hours)
    hits = []
    for r in csv.DictReader(io.StringIO(text)):
        lat, lon = float(r["latitude"]), float(r["longitude"])
        t = r["acq_time"].zfill(4)
        seen = datetime.fromisoformat(f"{r['acq_date']}T{t[:2]}:{t[2:]}:00+00:00")
        if seen >= cutoff and confident(r["confidence"]) and abs(lat - place.lat) < 1 and abs(lon - place.lon) < 1.2 \
                and place.distance(lat, lon) <= FIRE_RADIUS_MI:
            hits.append({"kind": "heat", "source": "firms", "sat": sat, "frp": float(r["frp"]),
                         "reported": seen.isoformat(), **place.locate(lat, lon)})
    return hits


def swept_times(text, sat):
    """{satellite: {scan times}} from every row in a FIRMS file, anywhere in the US: proof a pass is already in the files."""
    out = {}
    for r in csv.DictReader(io.StringIO(text)):
        name = FIRMS_SAT.get(r.get("satellite") if sat == "MODIS" else sat)
        t = r["acq_time"].zfill(4)
        out.setdefault(name, set()).add(datetime.fromisoformat(f"{r['acq_date']}T{t[:2]}:{t[2:]}:00+00:00"))
    return out


def pull_heat(place):
    """Every FIRMS polar satellite. One dead file only costs that satellite; all dead raises."""
    hits, swept, ok = [], {}, 0
    for sat, path in FIRMS_FILES.items():
        try:
            text = get(FIRMS + path, "text/csv", raw=True)
            hits += firms_rows(text, sat, place, hours=HISTORY_HOURS)
            for k, v in swept_times(text, sat).items():
                swept.setdefault(k, set()).update(v)
            ok += 1
        except Exception as e:
            print(f"FIRMS {sat} failed: {e}", flush=True)
    if not ok:
        raise RuntimeError("every FIRMS file failed")
    return {"hits": hits, "swept": swept}


GOES_SEEN = {}


def goes_keys(now):
    keys = []
    for t in (now - timedelta(hours=1), now):
        prefix = f"{GOES_PRODUCT}/{t:%Y}/{t.timetuple().tm_yday:03d}/{t:%H}/"
        body = get(f"{GLM_BUCKET}/?list-type=2&prefix={prefix}", "application/xml", raw=True)
        keys += re.findall(r"<Key>([^<]+)</Key>", body)
    return keys


def fixed_grid_latlon(x, y, proj):
    """GOES-R ABI scan angles (radians) to lat/lon, from the GOES-R PUG vol 4 section 4.2.8."""
    h = proj["perspective_point_height"] + proj["semi_major_axis"]
    req, rpol, lon0 = proj["semi_major_axis"], proj["semi_minor_axis"], math.radians(proj["longitude_of_projection_origin"])
    sx, cx, sy, cy = math.sin(x), math.cos(x), math.sin(y), math.cos(y)
    a = sx ** 2 + cx ** 2 * (cy ** 2 + (req / rpol) ** 2 * sy ** 2)
    b = -2 * h * cx * cy
    c = h ** 2 - req ** 2
    disc = b ** 2 - 4 * a * c
    if disc < 0:
        return None  # off the earth's disk
    rs = (-b - math.sqrt(disc)) / (2 * a)
    s1, s2, s3 = rs * cx * cy, -rs * sx, rs * cx * sy
    lat = math.degrees(math.atan((req / rpol) ** 2 * s3 / math.sqrt((h - s1) ** 2 + s2 ** 2)))
    return lat, math.degrees(lon0 - math.atan(s2 / (h - s1)))


def goes_fires(body):
    """Fire pixels in one FDC scan as (lat, lon, MW). Power is blank on some fire pixels; those read 0."""
    import h5py  # same lazy import as lightning
    import numpy as np
    with h5py.File(io.BytesIO(body), "r") as h:
        mask = h["Mask"][()]
        rows, cols = np.nonzero(np.isin(mask, GOES_FIRE))
        if not len(rows):
            return []
        sc = lambda v: (float(v.attrs["scale_factor"][0]), float(v.attrs["add_offset"][0]))
        (xs, xo), (ys, yo) = sc(h["x"]), sc(h["y"])
        xr, yr, power = h["x"][()], h["y"][()], h["Power"][()]
        proj = {k: float(h["goes_imager_projection"].attrs[k][0]) for k in
                ("perspective_point_height", "semi_major_axis", "semi_minor_axis", "longitude_of_projection_origin")}
        out = []
        for r, c in zip(rows, cols):
            ll = fixed_grid_latlon(xr[c] * xs + xo, yr[r] * ys + yo, proj)
            if ll:
                out.append((*ll, max(float(power[r, c]), 0.0)))
        return out


def goes_file(key, place):
    return key, [f for f in goes_fires(fetch_bytes(f"{GLM_BUCKET}/{key}"))
                 if abs(f[0] - place.lat) < 1 and abs(f[1] - place.lon) < 1.2]


def pull_goes(place):
    """Last GOES_MINUTES of scans. A pixel seen in several scans keeps its newest time and counts the scans."""
    now = datetime.now(timezone.utc)
    keys = [k for k in goes_keys(now) if glm_time(k) >= now - timedelta(minutes=GOES_MINUTES)]
    seen = GOES_SEEN.setdefault(place.name, {})  # each property cuts the files to its own box
    new = [k for k in keys if k not in seen]
    with ThreadPoolExecutor(6) as ex:
        seen.update(ex.map(lambda k: goes_file(k, place), new))
    for k in set(seen) - set(keys):
        del seen[k]
    px = {}
    for k in sorted(keys, key=glm_time):
        for lat, lon, mw in seen.get(k, []):
            spot = px.setdefault((round(lat, 3), round(lon, 3)), {"scans": 0, "first": glm_time(k).isoformat()})
            spot.update(lat=lat, lon=lon, frp=mw, reported=glm_time(k).isoformat())
            spot["scans"] += 1
    return [{"kind": "heat", "source": "goes", "sat": "GOES-19", "frp": s["frp"], "scans": s["scans"],
             "first": s["first"], "reported": s["reported"], **place.locate(s["lat"], s["lon"])}
            for s in px.values() if place.distance(s["lat"], s["lon"]) <= FIRE_RADIUS_MI]


def merge_fire(official, heat, spacing=1.5):
    """One symbol per fire: official reports win, heat shows only where nothing else is nearby."""
    kept = list(official)
    for h in sorted(heat, key=lambda x: x["reported"], reverse=True):
        if all(miles(h["lat"], h["lon"], k["lat"], k["lon"]) > spacing for k in kept):
            kept.append(h)
    return sorted(kept, key=lambda x: x["miles"])


def pull_fires(place, _):
    jobs = {"GA fire": lambda: pull_incidents(place, "georgiafc"), "SC fire": lambda: pull_incidents(place, "scfc"),
            "SC notices": lambda: pull_notices(place), "FIRMS": lambda: pull_heat(place), "GOES": lambda: pull_goes(place)}
    got, failed = {}, []
    with ThreadPoolExecutor(len(jobs)) as ex:  # side by side: SCFC notices alone can take 20 s
        futures = {name: ex.submit(job) for name, job in jobs.items()}
    for name, f in futures.items():
        try:
            got[name] = f.result()
        except Exception as e:
            print(f"{name} failed: {e}", flush=True)
            failed.append(name)
    official = [f for k, v in got.items() if k not in ("FIRMS", "GOES") for f in v]
    firms, goes = got.get("FIRMS") or {}, got.get("GOES", [])
    history = firms.get("hits", [])
    now = datetime.now(timezone.utc)
    live = [h for h in history if datetime.fromisoformat(h["reported"]) >= now - timedelta(hours=HEAT_HOURS)]
    log = strike_log(place)
    polar = [track(h, history + goes, log, 1) for h in live]
    goes = [track(h, history + goes, log, GOES_SPACING_MI) for h in goes]
    try:
        looks = good_passes(place, now - timedelta(hours=HEAT_HOURS), now)
        polar = [retire(h, looks, firms.get("swept", {}), place) for h in polar]
        polar = [h for h in polar if h.get("active", True) or h.get("long_run")]  # retired heat leaves the map; piles stay gray
    except Exception as e:  # no orbit data or GOES: keep the heat; a missing check never hides a fire
        print(f"later-pass check failed: {e}", flush=True)
    # finest location wins: official, then polar 375 m-1 km, then GOES only where nothing else sees it
    fine = merge_fire(official, polar)
    return {"items": merge_fire(fine, goes, GOES_SPACING_MI), "failed": failed}


def day(t):
    return (t - timedelta(hours=5)).date()  # Eastern, close enough to split day and night passes


def track(h, history, strikes, radius):
    """Confirm heat by a second pass, fast-track it after a nearby strike, and park long-running heat.
    history is every polar hit from the last 7 days plus the GOES pixels from the last 30 min."""
    times = sorted({datetime.fromisoformat(t) for d in history if miles(h["lat"], h["lon"], d["lat"], d["lon"]) <= radius
                    for t in (d["reported"], d.get("first") or d["reported"])} | {datetime.fromisoformat(h["reported"])})
    recent = [t for t in times if t >= times[-1] - timedelta(hours=HEAT_HOURS)]
    first = times[0]
    two_pass = recent[-1] - recent[0] >= timedelta(minutes=PASS_GAP_MIN)
    # the strike must come before the heat was first seen, so a pile already burning before the storm never qualifies.
    # A lone GOES scan is too thin even with a strike; it needs a polar hit or a second scan.
    solid = h.get("source") == "firms" or h.get("scans", 1) > 1
    struck = solid and next((at for at, lat, lon in strikes
                             if first - timedelta(days=STRIKE_DAYS) <= at <= first
                             and miles(h["lat"], h["lon"], lat, lon) <= STRIKE_MATCH_MI), None)
    long_run = len({day(t) for t in times}) >= LONG_RUN_DAYS
    return {**h, "passes": len(recent), "first": first.isoformat(), "confirmed": not long_run and (two_pass or bool(struck)),
            "lightning": struck.isoformat() if struck else None, "long_run": long_run, "active": not long_run,
            "last": times[-1].isoformat()}


# --- later passes ---------------------------------------------------------

TLES = {}


def tles(now):
    """Orbit elements for each polar satellite, refreshed twice a day."""
    if not TLES or now - TLES["at"] > timedelta(hours=12):
        with ThreadPoolExecutor(len(POLAR)) as ex:  # five small files; one after another took 10 s
            bodies = dict(zip(POLAR, ex.map(lambda n: get(TLE.format(n), "text/plain", raw=True), (v[0] for v in POLAR.values()))))
        got = {}
        for name, (norad, half) in POLAR.items():
            l1, l2 = bodies[name].strip().splitlines()[-2:]
            got[name] = (l1.strip(), l2.strip(), half)
        TLES.clear()
        TLES.update(sats=got, at=now)
    return TLES["sats"]


def subpoint(r, jd):
    """TEME position (km) to the point under the satellite. GMST only; polar motion is far below a km."""
    gmst = math.radians((280.46061837 + 360.98564736629 * (jd - 2451545.0)) % 360)
    lon = math.degrees(math.atan2(r[1], r[0]) - gmst)
    return math.degrees(math.atan2(r[2], math.hypot(r[0], r[1]))), (lon + 180) % 360 - 180


def overpasses(lat, lon, sats, start, end, step=60):
    """[(satellite, time)] of each closest approach with the point inside that sensor's good half swath."""
    from sgp4.api import Satrec, jday  # MIT, offline; only the overpass check needs it
    out = []
    for name, (l1, l2, half_km) in sats.items():
        sat, last = Satrec.twoline2rv(l1, l2), []
        t = start
        while t <= end:
            jd, fr = jday(t.year, t.month, t.day, t.hour, t.minute, t.second)
            err, r, _ = sat.sgp4(jd, fr)
            last = (last + [(t, miles(lat, lon, *subpoint(r, jd + fr)) * 1.609344 if not err else 1e9)])[-3:]
            if len(last) == 3 and last[1][1] < last[0][1] and last[1][1] <= last[2][1] and last[1][1] <= half_km:
                out.append((name, last[1][0]))
            t += timedelta(seconds=step)
    return sorted(out, key=lambda x: x[1])


def good_passes(place, start, end):
    return overpasses(place.lat, place.lon, tles(end), start, end)


def latlon_to_fixed(lat, lon, proj):
    """GOES-R PUG 4.2.8.1, forward: geodetic lat/lon to fixed grid scan angles (x, y) in radians."""
    req, rpol = proj["semi_major_axis"], proj["semi_minor_axis"]
    h = proj["perspective_point_height"] + req
    phi = math.atan(rpol ** 2 / req ** 2 * math.tan(math.radians(lat)))
    rc = rpol / math.sqrt(1 - (req ** 2 - rpol ** 2) / req ** 2 * math.cos(phi) ** 2)
    dl = math.radians(lon - proj["longitude_of_projection_origin"])
    sx, sy, sz = h - rc * math.cos(phi) * math.cos(dl), -rc * math.cos(phi) * math.sin(dl), rc * math.sin(phi)
    return math.asin(-sy / math.sqrt(sx * sx + sy * sy + sz * sz)), math.atan(sz / sx)


GOES_LOOKS = {}


def goes_mask_near(at, place):
    """The GOES FDC scan closest to a pass, cut to the property's box: (mask, x radians, y radians, projection)."""
    import h5py
    import numpy as np
    keys = goes_keys(at + timedelta(minutes=10))
    key = min(keys, key=lambda k: abs(glm_time(k) - at))
    if (place.name, key) not in GOES_LOOKS:
        with h5py.File(io.BytesIO(fetch_bytes(f"{GLM_BUCKET}/{key}")), "r") as h:
            proj = {k: float(h["goes_imager_projection"].attrs[k][0]) for k in
                    ("perspective_point_height", "semi_major_axis", "semi_minor_axis", "longitude_of_projection_origin")}
            sc = lambda v: (float(v.attrs["scale_factor"][0]), float(v.attrs["add_offset"][0]))
            (xs, xo), (ys, yo) = sc(h["x"]), sc(h["y"])
            x, y = h["x"][()] * xs + xo, h["y"][()] * ys + yo
            corners = [latlon_to_fixed(place.lat + a, place.lon + b, proj) for a in (-1, 1) for b in (-1.2, 1.2)]
            cols = sorted(int(np.argmin(abs(x - cx))) for cx, _ in corners)
            rows = sorted(int(np.argmin(abs(y - cy))) for _, cy in corners)
            c0, c1, r0, r1 = cols[0], cols[-1] + 1, rows[0], rows[-1] + 1
            GOES_LOOKS[(place.name, key)] = (h["Mask"][r0:r1, c0:c1], x[c0:c1], y[r0:r1], proj, at)
        for k in [k for k, v in GOES_LOOKS.items() if at - v[4] > timedelta(hours=HEAT_HOURS + 2)]:
            del GOES_LOOKS[k]
    return GOES_LOOKS[(place.name, key)]


def clear_at(look, lat, lon):
    """True clear, False cloudy, None unknown (night glint zones, missing input, off grid)."""
    import numpy as np
    mask, x, y, proj, _ = look
    gx, gy = latlon_to_fixed(lat, lon, proj)
    v = int(mask[int(np.argmin(abs(y - gy))), int(np.argmin(abs(x - gx)))])
    return True if v == GOES_CLEAR else False if v >= GOES_CLOUD else None


def retire(h, looks, swept, place, look_at=None):
    """Count later clear looks that did not see the heat; enough of them and it goes gray, raising nothing."""
    if h.get("long_run"):
        return h
    last, misses = datetime.fromisoformat(h["last"]), 0
    for name, at in looks:
        if at <= last + timedelta(minutes=PASS_GAP_MIN):
            continue
        if not any(abs(s - at) <= timedelta(minutes=10) for s in swept.get(name, ())):
            continue  # that pass is not in the FIRMS files yet, so silence there means nothing
        clear = (look_at or (lambda t: clear_at(goes_mask_near(t, place), h["lat"], h["lon"])))(at)
        misses += clear is True
    if misses >= MISSES_TO_DROP[bool(h.get("confirmed"))]:
        return {**h, "misses": misses, "active": False, "confirmed": False}
    return {**h, "misses": misses}


# --- burn status and storms -----------------------------------------------

def pull_burn(place, nws):
    state, county = nws["state"], nws["county"]
    site = FIRESPONSE.get(state)
    if not site:
        return {"status": "unknown", "note": f"No {state} feed yet, check the state forestry agency."}
    rows = get(f"https://{site}.firesponse.com/burn-permit/api/burnrestriction/all")
    hit = any(str(r.get("Name", "")).lower() == county.lower() for r in rows)
    return {"status": "restricted" if hit else "none listed",
            "note": f"{county} County is on the state restriction list." if hit else
                    f"No state restriction listed for {county} County. County rules can still apply."}


def wind_grid_points(lat, lon):
    lats = [round(lat + (i - WIND_N // 2) * WIND_STEP, 3) for i in range(WIND_N)]
    lons = [round(lon + (j - WIND_N // 2) * WIND_STEP * 1.2, 3) for j in range(WIND_N)]
    return lats, lons


def qpe(lat, lon, keys):
    """Values from the NWS precipitation analysis at one point. None where the grid has no value."""
    q = urllib.parse.urlencode({"geometry": f"{lon},{lat}", "geometryType": "esriGeometryPoint", "sr": 4326,
                                "layers": "all:" + ",".join(str(QPE_LAYERS[k]) for k in keys), "tolerance": 1,
                                "mapExtent": f"{lon - 1},{lat - 1},{lon + 1},{lat + 1}", "imageDisplay": "400,400,96",
                                "returnGeometry": "false", "f": "json"})
    vals = {r["layerId"]: r["attributes"].get("Service Pixel Value") for r in get(f"{QPE}?{q}")["results"]}
    out = {}
    for k in keys:
        try:
            out[k] = max(round(float(vals[QPE_LAYERS[k]]), 2), 0.0)  # NOAA writes -10000 where no rain fell
        except (KeyError, TypeError, ValueError):
            out[k] = None
    return out


def pull_rain(place, _):
    """Observed rain at the property center over the strike window (the analysis has a 3 day layer, so STRIKE_DAYS stays 3)."""
    got = qpe(place.lat, place.lon, ["rain_1h", "rain_3d"])
    return {"inches": got["rain_3d"], "days": 3, "last_hour": got["rain_1h"]}


def cpc(service, layer, place):
    """One CPC outlook at the property. Outside every shape means equal chances (EC)."""
    q = urllib.parse.urlencode({"geometry": f"{place.lon},{place.lat}", "geometryType": "esriGeometryPoint", "inSR": 4326,
                                "spatialRel": "esriSpatialRelIntersects", "outFields": "*", "returnGeometry": "false", "f": "json"})
    hits = get(f"{CPC}{service}/MapServer/{layer}/query?{q}")["features"]
    a = hits[0]["attributes"] if hits else {}
    return {"cat": a.get("cat") or "EC",
            "prob": a.get("prob")}


def drought_history(fips, now):
    """Latest Drought Monitor week for the county, and how many past years were drier the same week (DSCI, 0-500)."""
    rows = get(f"{USDM}?" + urllib.parse.urlencode({"aoi": fips, "startdate": "1/1/2000", "enddate": f"{now:%m/%d/%Y}", "statisticsType": 1}))
    rows = sorted(rows, key=lambda r: r["mapDate"])
    dsci = lambda r: sum(r[k] for k in ("d0", "d1", "d2", "d3", "d4"))  # cumulative percents, the standard index
    last = rows[-1]
    when = datetime.fromisoformat(last["mapDate"])
    past = {}
    for r in rows:
        t = datetime.fromisoformat(r["mapDate"])
        gap = abs(t.timetuple().tm_yday - when.timetuple().tm_yday)
        if t.year < when.year and min(gap, 365 - gap) <= 3:  # same week, by day of year so Feb 29 and New Year cannot break it
            past[t.year] = dsci(r)
    worst = next((k for k in range(4, -1, -1) if last[f"d{k}"] > 0), None)
    return {"date": last["mapDate"][:10], "county": last["county"], "category": USDM_NAMES[worst] if worst is not None else "No drought",
            "coverage": last[f"d{worst}"] if worst is not None else 0, "dsci": dsci(last),
            "wetter_years": sum(v < dsci(last) for v in past.values()), "years": len(past)}


def twice(fn):
    """One retry: NOAA map services drop the odd request, and this feed is cached for 6 hours."""
    try:
        return fn()
    except Exception:
        time.sleep(2)
        return fn()


def pull_climate(place, nws):
    """Long range outlooks, drought and rain against normal. Each part fails on its own."""
    out, now = {}, datetime.now(timezone.utc)
    zone = nws["county_zone"]  # e.g. SCC009 -> FIPS 45009
    jobs = {
        "rain": lambda: qpe(place.lat, place.lon, ["pct_30d"]),
        "drought": lambda: drought_history(STATE_FIPS[zone[:2]] + zone[3:], now),
        "d8_14": lambda: {"temp": cpc("cpc_8_14_day_outlk", 0, place), "rain": cpc("cpc_8_14_day_outlk", 1, place)},
        "season": lambda: {"temp": cpc("cpc_sea_temp_outlk", 0, place), "rain": cpc("cpc_sea_precip_outlk", 0, place)},
    }
    with ThreadPoolExecutor(4) as ex:
        futs = {k: ex.submit(twice, fn) for k, fn in jobs.items()}
        for k, f in futs.items():
            try:
                out[k] = f.result()
            except Exception as e:
                print(f"climate {k} failed: {e}", flush=True)
                out[k] = None
    if not any(out.values()):
        raise RuntimeError("every climate source failed")
    return out


def primed(data):
    """Dry fuels and no soaking rain. Unknown fire danger or rain reads as not primed, so a dead feed cannot raise a caution."""
    rain = (data.get("rain") or {}).get("inches")
    return (data.get("fire_class") or {}).get("rating") in PRIMED_RATINGS and rain is not None and rain < PRIMED_RAIN_IN


def wind_obs(rows, now):
    """Airport reports to (lat, lon, u, v, time). u/v in mph point where the air goes; variable direction counts as calm."""
    out = []
    for r in rows:
        if not isinstance(r.get("wspd"), (int, float)) or now - (r.get("obsTime") or 0) > METAR_MAX_AGE:
            continue
        mph, d = r["wspd"] * 1.15078, r.get("wdir")
        rad = math.radians(d) if isinstance(d, (int, float)) else None  # direction it blows FROM
        out.append((r["lat"], r["lon"], round(-mph * math.sin(rad), 2) if rad is not None else 0.0,
                    round(-mph * math.cos(rad), 2) if rad is not None else 0.0, r["obsTime"]))
    return out


def idw(lat, lon, obs, i):
    # ponytail: inverse distance squared over every station, fine for the dozen or so airports in the box
    w = [(1 / max(miles(lat, lon, o[0], o[1]), 1) ** 2, o[i]) for o in obs]
    return round(sum(a * b for a, b in w) / sum(a for a, _ in w), 2)


def pull_wind(place, _):
    """Observed 10 m wind from airports around the property, spread onto the flow layer's grid."""
    lats, lons = wind_grid_points(place.lat, place.lon)
    box = f"{min(lats) - .5},{min(lons) - .5},{max(lats) + .5},{max(lons) + .5}"
    obs = wind_obs(get(f"{METAR}?bbox={box}&format=json"), time.time())
    if not obs:
        raise RuntimeError("no fresh airport wind reports")
    pts = [(a, b) for a in lats for b in lons]
    return {"lats": lats, "lons": lons, "u": [idw(a, b, obs, 2) for a, b in pts], "v": [idw(a, b, obs, 3) for a, b in pts],
            "stations": len(obs), "time": datetime.fromtimestamp(max(o[4] for o in obs), timezone.utc).isoformat()}


def pull_storms(place, _):
    out = []
    for s in get("https://www.nhc.noaa.gov/CurrentStorms.json").get("activeStorms", []):
        lat, lon = s.get("latitudeNumeric"), s.get("longitudeNumeric")
        if lat is None or lon is None:
            continue
        out.append({"name": s.get("name"), "type": s.get("classification"), "wind_kt": s.get("intensity"),
                    "moving": f"{s.get('movementDir')} deg at {s.get('movementSpeed')} kt", **place.locate(lat, lon)})
    return {"items": sorted(out, key=lambda x: x["miles"])}


# --- RAWS -----------------------------------------------------------------

def first_number(text):
    m = re.search(r"-?\d+(?:\.\d+)?", str(text or ""))
    return float(m[0]) if m else None


def raws_rows(features, place, limit=3, max_age_hours=3):
    now = time.time() * 1000
    out = []
    for f in features:
        a = f["attributes"]
        seen = a.get("ObservedDate") or 0
        # ponytail: portables move and report old dates, so only fixed stations count
        if "PORTABLE" in str(a.get("StationName", "")).upper() or now - seen > max_age_hours * 3600000:
            continue
        lat, lon = f["geometry"]["y"], f["geometry"]["x"]
        out.append({"name": a.get("StationName"), "nws_id": a.get("NWSID"), "county": a.get("County"), "agency": a.get("Agency"),
                    "observed": seen / 1000, "temp_f": first_number(a.get("AirTempStandPlace")),
                    "humidity": first_number(a.get("RelativeHumidity")), "wind_mph": first_number(a.get("WindSpeedMPH")),
                    "wind_dir": compass(first_number(a.get("WindDirDegrees"))), "gust_mph": first_number(a.get("WindSpeedPeak")),
                    "fuel_moisture": first_number(a.get("FuelMoisture")), "fuel_temp_f": first_number(a.get("FuelTemp")),
                    "solar_wm2": first_number(a.get("SolarRadiation")), **place.locate(lat, lon)})
    return sorted(out, key=lambda x: x["miles"])[:limit]


def pull_raws(place, _):
    q = urllib.parse.urlencode({"where": "1=1", "geometry": f"{place.lon},{place.lat}", "geometryType": "esriGeometryPoint",
                                "inSR": 4326, "distance": 70, "units": "esriSRUnit_StatuteMile", "outFields": "*",
                                "outSR": 4326, "f": "json"})
    return {"items": raws_rows(get(f"{RAWS}?{q}")["features"], place)}


# --- fire danger ----------------------------------------------------------

def class_at(im, lat, lon):
    """Read the USFS class map at a point. Grid from the map's own tick marks: -120 at x 290.5, 35N at y 453.5."""
    x, y = round(290.5 + (lon + 120) * 19.02), round(453.5 + (35 - lat) * 25.35)
    legend = [im.getpixel((px, FD_LEGEND_Y)) for px in FD_LEGEND_X]
    votes = {}
    # small window so a black station dot cannot decide the answer
    for dx in range(-3, 4):
        for dy in range(-3, 4):
            p = im.getpixel((x + dx, y + dy))
            if min(p) > 250 or max(p) < 60:
                continue
            i = min(range(6), key=lambda n: sum((a - b) ** 2 for a, b in zip(p, legend[n])))
            votes[i] = votes.get(i, 0) + 1
    return FD_NAMES[max(votes, key=votes.get)] if votes else None


def pull_fire_class(place, _):
    from PIL import Image  # only this feed needs it, so a missing install cannot take the others down
    req = urllib.request.Request(FD_CLASS, headers={"User-Agent": UA})
    with urllib.request.urlopen(req, timeout=25) as r:
        body, stamp = r.read(), r.headers.get("Last-Modified")
    if stamp and datetime.now(timezone.utc) - parsedate_to_datetime(stamp) > timedelta(days=4):
        raise RuntimeError("fire danger class map is out of date")
    rating = class_at(Image.open(io.BytesIO(body)).convert("RGB"), place.lat, place.lon)
    if not rating:
        raise RuntimeError("property is outside the fire danger class map")
    # posted once a day at about 06:00 UTC for the following calendar day
    made = parsedate_to_datetime(stamp).date() + timedelta(days=1) if stamp else None
    # the map only ever covers tomorrow, so each day's reading is kept; yesterday's "tomorrow" is today's rating
    f = STATE / (re.sub(r"\W+", "_", place.name).lower() + "_fireclass.json")
    try:
        hist = json.loads(f.read_text())
    except (OSError, ValueError):
        hist = {}
    if made:
        hist[made.isoformat()] = rating
        STATE.mkdir(exist_ok=True)
        f.write_text(json.dumps(dict(sorted(hist.items())[-30:])))
    t = datetime.now().date().isoformat()
    return {"rating": rating, "date": made and made.isoformat(), "today": {"rating": hist[t], "date": t} if t in hist else None}


# --- lightning ------------------------------------------------------------

GLM_SEEN = {}


def glm_keys(now):
    keys = []
    for t in (now - timedelta(hours=1), now):
        prefix = f"GLM-L2-LCFA/{t:%Y}/{t.timetuple().tm_yday:03d}/{t:%H}/"
        body = get(f"{GLM_BUCKET}/?list-type=2&prefix={prefix}", "application/xml", raw=True)
        keys += re.findall(r"<Key>([^<]+)</Key>", body)
    return keys


def glm_time(key):
    return datetime.strptime(re.search(r"_s(\d{13})", key)[1], "%Y%j%H%M%S").replace(tzinfo=timezone.utc)


def glm_flashes(body):
    import h5py  # only lightning needs it, so a missing install cannot take the other feeds down
    with h5py.File(io.BytesIO(body), "r") as h:
        def read(name):
            v = h[name]
            scale = v.attrs.get("scale_factor", [1])[0] if "scale_factor" in v.attrs else 1
            add = v.attrs.get("add_offset", [0])[0] if "add_offset" in v.attrs else 0
            return [float(x) * float(scale) + float(add) for x in v[()]]
        good = [q == 0 for q in h["flash_quality_flag"][()]]  # 0 = good; the rest are degraded flashes
        return [ll for ll, ok in zip(zip(read("flash_lat"), read("flash_lon")), good) if ok]


def glm_file(key, place):
    return key, [(a, b) for a, b in glm_flashes(fetch_bytes(f"{GLM_BUCKET}/{key}"))
                 if abs(a - place.lat) < 1 and abs(b - place.lon) < 1.2]


STRIKES = {}


def strike_file(place):
    return STATE / (re.sub(r"\W+", "_", place.name).lower() + "_strikes.json")


def strike_log(place):
    """[(time, lat, lon)] of good flashes over the last STRIKE_DAYS, kept on disk so a restart does not forget a storm."""
    if place.name not in STRIKES:
        try:
            STRIKES[place.name] = json.loads(strike_file(place).read_text())
        except (OSError, ValueError):
            STRIKES[place.name] = {}
    return [(datetime.fromisoformat(at), *map(float, cell.split(","))) for cell, at in STRIKES[place.name].items()]


def log_strikes(place, flashes, now):
    strike_log(place)
    log = STRIKES[place.name]
    # ponytail: newest flash per 0.01 deg cell (about 0.7 mi). Newest is the conservative pick: a strike after heat appeared never confirms it
    for f in flashes:
        cell = f"{f['lat']:.2f},{f['lon']:.2f}"
        log[cell] = max(log.get(cell, ""), f["at"])
    old = (now - timedelta(days=STRIKE_DAYS)).isoformat()
    for cell in [c for c, at in log.items() if at < old]:
        del log[cell]
    if flashes:
        STATE.mkdir(exist_ok=True)
        strike_file(place).write_text(json.dumps(log))


def pull_lightning(place, _):
    now = datetime.now(timezone.utc)
    start = now - timedelta(minutes=LIGHTNING_MINUTES)
    keys = [k for k in glm_keys(now) if glm_time(k) >= start]
    seen = GLM_SEEN.setdefault(place.name, {})
    new = [k for k in keys if k not in seen]
    with ThreadPoolExecutor(8) as ex:
        seen.update(ex.map(lambda k: glm_file(k, place), new))
    for k in set(seen) - set(keys):
        del seen[k]
    out = [{"at": glm_time(k).isoformat(), **place.locate(a, b)} for k in keys for a, b in seen.get(k, [])]
    out = sorted((x for x in out if x["miles"] <= FIRE_RADIUS_MI), key=lambda x: x["miles"])
    log_strikes(place, out, now)
    close = [at for at, lat, lon in strike_log(place) if place.distance(lat, lon) <= HOLDOVER_MI]
    return {"items": out, "minutes": LIGHTNING_MINUTES, "files": len(keys), "holdover": max(close).isoformat() if close else None}


# --- recent imagery -------------------------------------------------------

def post_json(url, body):
    req = urllib.request.Request(url, json.dumps(body).encode(), {"User-Agent": UA, "Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.load(r)


def tract_coverage(place, features, grid=40):
    """Share of the tract whose newest image is each date. Sampled on a grid, footprints only, so clouds are not counted."""
    lats, lons = zip(*place.points)
    points = [(min(lats) + (max(lats) - min(lats)) * (i + .5) / grid, min(lons) + (max(lons) - min(lons)) * (j + .5) / grid)
              for i in range(grid) for j in range(grid)]
    points = [p for p in points if inside(place.rings, *p)]
    scenes = sorted(((f["properties"]["datetime"][:10], list(rings({"features": [f]}))) for f in features), key=lambda x: x[0], reverse=True)
    hits = {}
    for lat, lon in points:
        date = next((d for d, rs in scenes if inside(rs, lat, lon)), "none")
        hits[date] = hits.get(date, 0) + 1
    return [{"date": d, "pct": round(100 * n / len(points))} for d, n in sorted(hits.items(), reverse=True)]


def cloud_pct(histogram):
    """Cloud share of the tract from an SCL categorical histogram [[counts], [classes]]; no-data pixels (0) left out."""
    counts = {int(v): n for n, v in zip(*histogram) if int(v) != 0}
    total = sum(counts.values())
    return 100 * sum(n for v, n in counts.items() if v in CLOUD_CLASSES) / total if total else 100


def tract_cloud(place, item_id):
    shape = {"type": "Feature", "properties": {}, "geometry": {"type": "MultiPolygon", "coordinates": [[[list(p[:2]) for p in r]] for r in place.rings]}}
    stats = post_json(f"{STATS}?collection=sentinel-2-l2a&item={item_id}&assets=SCL&categorical=true&max_size=1024", shape)
    return cloud_pct(next(iter(stats["properties"]["statistics"].values()))["histogram"])


ESRI_META = "https://services.arcgisonline.com/arcgis/rest/services/World_Imagery/MapServer/identify"


def pull_basemaps(place, _):
    """Capture date and resolution of the sharp basemaps at the tract center (Waters, 2026-11-12: Esri's
    image there was years old with no date shown). Esri: its own imagery metadata. NAIP: newest USDA flight
    over the tract in Planetary Computer's catalog, plus a newest-first mosaic the map draws from (cached tiles,
    about 0.6 s each; USGS's NAIP ImageServer renders on demand at 2 to 12 s a tile)."""
    pt = f"{place.lon},{place.lat}"
    box = f"{place.lon - .01},{place.lat - .01},{place.lon + .01},{place.lat + .01}"
    esri = get(ESRI_META + "?" + urllib.parse.urlencode({"geometry": pt, "geometryType": "esriGeometryPoint", "sr": 4326, "layers": "all",
               "tolerance": 0, "mapExtent": box, "imageDisplay": "400,400,96", "returnGeometry": "false", "f": "json"}))
    a = next((r["attributes"] for r in esri.get("results", []) if r["layerName"] == "World Imagery"), {})
    d = str(a.get("DATE (YYYYMMDD)", ""))
    newest = [{"field": "datetime", "direction": "desc"}]
    n = (post_json(STAC, {"collections": ["naip"], "intersects": {"type": "Point", "coordinates": [place.lon, place.lat]},
                          "limit": 1, "sortby": newest})["features"] or [None])[0]
    mosaic = post_json(MOSAIC, {"filter-lang": "cql2-json", "filter": {"op": "=", "args": [{"property": "collection"}, "naip"]}, "sortby": newest})
    return {"esri": {"date": f"{d[:4]}-{d[4:6]}-{d[6:8]}", "res": float(a["RESOLUTION (M)"])} if d.isdigit() and len(d) == 8 else None,
            "naip": {"date": n["properties"]["datetime"][:10], "res": n["properties"].get("gsd"), "mosaic": mosaic["id"]} if n else None}


def pull_imagery(place, _):
    now = datetime.now(timezone.utc)
    lats, lons = zip(*place.points)
    items = post_json(STAC, {"collections": ["sentinel-2-l2a"], "bbox": [min(lons), min(lats), max(lons), max(lats)], "limit": 100,
                             "datetime": f"{now - timedelta(days=IMAGERY_DAYS):%Y-%m-%dT00:00:00Z}/{now:%Y-%m-%dT%H:%M:%SZ}",
                             "sortby": [{"field": "datetime", "direction": "desc"}], "query": {"eo:cloud_cover": {"lt": SEARCH_MAX_CLOUD}}})["features"]
    clear = []
    for f in items[:MAX_CHECKS]:  # newest first; stop once clear scenes cover the whole tract
        try:
            if tract_cloud(place, f["id"]) <= TRACT_MAX_CLOUD:
                clear.append(f)
        except Exception as e:
            print(f"Sentinel-2 cloud check {f['id']} failed: {e}", flush=True)
        if clear and all(c["date"] != "none" for c in tract_coverage(place, clear)):
            break
    if not clear:
        raise RuntimeError("no scene clear over the tract in the window")
    # newest pixel wins and gaps fall through to older clear scenes. Outside the tract a chosen scene can still show its clouds.
    # two mosaics: the tract's own clear passes (drawn only over the tract's box) on top of a regional clear-scene fill.
    # The mosaic service needs the collection named and takes an "or" of ids, not "in".
    coll = {"op": "=", "args": [{"property": "collection"}, "sentinel-2-l2a"]}
    newest = [{"field": "datetime", "direction": "desc"}]
    pick = {"op": "or", "args": [{"op": "=", "args": [{"property": "id"}, f["id"]]} for f in clear]}
    tract = post_json(MOSAIC, {"filter-lang": "cql2-json", "filter": {"op": "and", "args": [coll, pick]}, "sortby": newest})
    base = post_json(MOSAIC, {"filter-lang": "cql2-json", "filter": {"op": "and", "args": [coll,
        {"op": ">=", "args": [{"property": "datetime"}, f"{now - timedelta(days=IMAGERY_DAYS):%Y-%m-%dT00:00:00Z}"]},
        {"op": "<=", "args": [{"property": "eo:cloud_cover"}, BASE_MAX_CLOUD]}]}, "sortby": newest})
    return {"mosaic": tract["id"], "base": base["id"], "coverage": tract_coverage(place, clear), "days": IMAGERY_DAYS}


# --- status ---------------------------------------------------------------

def level(data, errors):
    """Warning > Watch > Clear. A dead core feed can never read as Clear."""
    why = {"Warning": [], "Watch": []}
    for a in (data.get("nws") or {}).get("alerts", []):
        strong = "warning" in a["event"].lower() or a["severity"] in ("Extreme", "Severe")
        why["Warning" if strong else "Watch"].append(a["event"])
    for f in (data.get("fires") or {}).get("items", []):
        live = f["kind"] == "wildfire" and f.get("active", True)
        if live and f["miles"] <= HEAT_WARNING_MI:  # agency-reported wildfires use the same 2 mi Warning ring
            why["Warning"].append(f"Wildfire {f['miles']} mi {f['dir']}")
        elif live and f["miles"] <= 15:
            why["Watch"].append(f"Wildfire {f['miles']} mi {f['dir']}")
        elif f["kind"] == "heat" and f.get("active", True):  # long-running and not-seen-again heat raise nothing
            what = "Likely lightning fire" if f.get("lightning") else "Fire seen on 2 satellite passes"
            # a confirmed spot can still be a permitted burn GA does not publish, so far heat stays a Watch;
            # only heat near the line, or heat that followed a strike, is a Warning
            if f.get("confirmed") and (f["miles"] <= HEAT_WARNING_MI or (f.get("lightning") and f["miles"] <= 5)):
                why["Warning"].append(f"{what} {f['miles']} mi {f['dir']}")
            elif f.get("confirmed") and f["miles"] <= 15:
                why["Watch"].append(f"{what} {f['miles']} mi {f['dir']}")
            elif f["miles"] <= 5:
                why["Watch"].append(f"Possible fire, 1 pass, {f['miles']} mi {f['dir']}")
    for s in (data.get("storms") or {}).get("items", []):
        if s["miles"] <= STORM_RADIUS_MI:
            why["Watch"].append(f"{s['name']} {s['miles']:.0f} mi {s['dir']}")
    near = [x for x in (data.get("lightning") or {}).get("items", []) if x["miles"] <= LIGHTNING_WATCH_MI]
    hold = (data.get("lightning") or {}).get("holdover")
    # the ladder: primed (panel only) -> lightning on the property while primed (Watch) -> heat after it (Warning, in track()).
    # About 1 in 1000 strikes starts a fire, so the strike alone stays a Watch and the heat is a real upgrade.
    if hold and not near and primed(data):
        why["Watch"].append(f"Lightning hit the property {hold[:10]} with fuels primed, watch for holdover fire")
    if near:  # lightning alone is only ever a caution; a fire it starts is caught by the heat rules above
        why["Watch"].append("Lightning over the property" if near[0]["miles"] == 0 else f"Lightning {near[0]['miles']} mi {near[0]['dir']}")
    rated = ((data.get("fire_class") or {}).get("today") or {}).get("rating")  # USFS fire danger class for today
    if rated in ("Very High", "Extreme"):
        why["Watch"].append(f"USFS fire danger {rated} today")
    if (data.get("burn") or {}).get("status") == "restricted":
        why["Watch"].append("Burn restriction")
    for name in ("Warning", "Watch"):
        if why[name]:
            return name, why[name]
    missing = [f"No {k} data" for k in ("nws", "fires") if k in errors]
    missing += [f"No {k} data" for k in (data.get("fires") or {}).get("failed", [])]
    if missing:
        return "Unknown", missing
    return "Clear", []


def sky_words(cover, rain_hour):
    """Sky at the property: NWS grid cloud cover for its own cell (all heights; airport sensors stop at 12,000 ft),
    and Rain when the radar-gauge analysis has rain on the center in the last hour."""
    if rain_hour is not None and rain_hour >= 0.01:
        return f"Rain, {rain_hour:.2f} in last hour"
    if cover is None:
        return None
    return next(w for top, w in ((12.5, "Clear"), (37.5, "Mostly clear"), (62.5, "Partly cloudy"), (87.5, "Mostly cloudy"), (101, "Cloudy")) if cover < top)


def best_conditions(place, airport, raws):
    """One reading: the closest station to the property center, fire weather station on a near tie."""
    if not airport and not raws:
        return None
    r = raws[0] if raws else None
    a_mi = miles(place.lat, place.lon, airport["lat"], airport["lon"]) if airport else 1e9
    r_mi = miles(place.lat, place.lon, r["lat"], r["lon"]) if r else 1e9
    out = {"sky": (airport or {}).get("sky"), "fuel_moisture": r and r["fuel_moisture"]}
    if r and r_mi <= a_mi + STATION_TIE_MI:
        at = datetime.fromtimestamp(r["observed"], timezone.utc).isoformat()
        return {**out, "source": f"{r['name']} fire weather station", "miles": round(r_mi), "observed": at,
                **{k: r[k] for k in ("temp_f", "humidity", "wind_mph", "wind_dir", "gust_mph")}}
    return {**out, "source": airport["station"], "miles": round(a_mi), "observed": airport["observed"],
            **{k: airport[k] for k in ("temp_f", "humidity", "wind_mph", "wind_dir", "gust_mph")}}


class Live:
    def __init__(self, place):
        self.place = place
        self.cache = {}
        self.lock = threading.Lock()

    def fetch(self, key, fn, arg):
        with self.lock:
            hit = self.cache.get(key)
        # "tried" drives the refresh, "at" is the data's age; a feed that has never worked has no "at"
        if hit and time.time() - hit["tried"] < TTL[key]:
            return hit
        try:
            hit = {"at": time.time(), "tried": time.time(), "data": fn(self.place, arg), "error": None}
        except Exception as e:
            print(f"{key} failed: {e}", flush=True)
            # keep showing the last good pull; the page marks it stale
            hit = {"at": (hit or {}).get("at"), "tried": time.time(), "data": (hit or {}).get("data"), "error": str(e)}
        with self.lock:
            self.cache[key] = hit
        return hit

    def status(self, fresh=False):
        if fresh:
            with self.lock:
                # imagery changes a few times a week, so Reload leaves it cached
                self.cache = {k: v for k, v in self.cache.items() if k in ("imagery", "basemaps")}
        nws = self.fetch("nws", pull_nws, None)
        with ThreadPoolExecutor(8) as ex:
            jobs = {k: ex.submit(self.fetch, k, fn, None) for k, fn in
                    (("fires", pull_fires), ("storms", pull_storms), ("raws", pull_raws),
                     ("lightning", pull_lightning), ("imagery", pull_imagery), ("basemaps", pull_basemaps), ("fire_class", pull_fire_class),
                     ("wind", pull_wind), ("rain", pull_rain))}
            if nws["data"]:
                jobs["burn"] = ex.submit(self.fetch, "burn", pull_burn, nws["data"])
                jobs["climate"] = ex.submit(self.fetch, "climate", pull_climate, nws["data"])
            parts = {"nws": nws, **{k: j.result() for k, j in jobs.items()}}
        data = {k: v["data"] for k, v in parts.items()}
        data["current"] = best_conditions(self.place, (data.get("nws") or {}).get("conditions"), (data.get("raws") or {}).get("items", []))
        if data["current"]:
            sky = sky_words(((data.get("nws") or {}).get("conditions") or {}).get("sky_cover"), (data.get("rain") or {}).get("last_hour"))
            data["current"]["sky"] = sky or data["current"]["sky"]  # airport text only when the property's own values are missing
        errors = {k: v["error"] for k, v in parts.items() if v["error"]}
        data["primed"] = primed(data)
        name, why = level(data, errors)
        return {"name": self.place.name, "level": name, "why": why, "data": data,
                "errors": list(errors), "fetched": {k: v["at"] for k, v in parts.items()}, "now": time.time()}


def slug(name):
    return re.sub(r"\W+", "-", name).strip("-").lower()


def area(place):
    dy = AREA_MI / 69
    dx = dy / math.cos(math.radians(place.lat))
    return [round(v, 4) for v in (place.lon - dx, place.lat - dy, place.lon + dx, place.lat + dy)]


PORTAL_TYPES = {".html": "text/html; charset=utf-8", ".json": "application/json", ".geojson": "application/geo+json", ".png": "image/png"}


LOGIN_PAGE = b"""<!doctype html><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>Sign in</title><style>body{margin:0;min-height:100vh;display:grid;place-items:center;background:#14181c;color:#eef1f3;font:15px system-ui,sans-serif}
form{display:grid;gap:12px;width:min(320px,90vw)}img{height:40px;justify-self:center}input,button{font:inherit;padding:10px;border-radius:4px;border:1px solid #333c45}
input{background:#1d2329;color:inherit}button{background:#f2c230;color:#14181c;border:0;cursor:pointer}p{color:#e0796f;margin:0;text-align:center}</style>
<form method="post" action="/login"><img src="/logo.png" alt="JT Land"><input type="password" name="password" placeholder="Password" autofocus required>
<button>Sign in</button><!--ERR--></form>"""


def serve(props, port, portal=None, auth=None, edit=None):
    """props: [(Live, geojson)]. The page picks one with ?p=<slug>; no p means the first.
    portal: a built portal folder (build_portal.py), served read-only under /portal/.
    auth: password -> bool; when set, every page needs a sign-in (session cookie, in memory).
    edit: dict -> JSON-able, called for POST /portal/api/edit (the portal's schedule edits)."""
    portal = Path(portal).resolve() if portal else None
    by = {slug(lv.place.name): (lv, json.dumps(gj).encode()) for lv, gj in props}
    menu = json.dumps([{"p": k, "name": lv.place.name} for k, (lv, _) in by.items()]).encode()
    page = lambda: (HERE / "index.html").read_bytes().replace(b"/*PROPS*/null", menu)  # read per request: page edits show on reload, no restart
    logo = (HERE.parent.parent / "JT" / "land" / "JT_Land__White&Yellow.png").read_bytes()  # same land logo as the webmap skill
    sessions = set()  # ponytail: sessions die with the server; a restart means signing in again
    for lv, _ in props:  # warm the feeds now: the first pull takes about 30 s and the page would sit on "Checking..."
        threading.Thread(target=lv.status, daemon=True).start()

    class H(BaseHTTPRequestHandler):
        def send(self, body, kind, code=200, headers=()):
            self.send_response(code)
            self.send_header("Content-Type", kind)
            self.send_header("Cache-Control", "no-store")
            for k, v in headers:
                self.send_header(k, v)
            self.end_headers()
            self.wfile.write(body)

        def signed_in(self):
            if not auth:
                return True
            jar = dict(c.strip().partition("=")[::2] for c in self.headers.get("Cookie", "").split(";") if "=" in c)
            return jar.get("s") in sessions

        def body(self, limit=10_000):
            n = int(self.headers.get("Content-Length") or 0)
            if n > limit:
                raise ValueError("request too large")
            return self.rfile.read(n)

        def do_POST(self):
            path = self.path.partition("?")[0]
            if path == "/login" and auth:
                pw = urllib.parse.parse_qs(self.body().decode(errors="replace")).get("password", [""])[0]
                if auth(pw):
                    token = secrets.token_urlsafe(32)
                    sessions.add(token)
                    self.send(b"", "text/plain", 303, [("Location", "/portal/"),
                                                      ("Set-Cookie", f"s={token}; HttpOnly; SameSite=Strict; Path=/")])
                else:
                    time.sleep(1)  # slows guessing
                    self.send(LOGIN_PAGE.replace(b"<!--ERR-->", b"<p>Wrong password</p>"), "text/html; charset=utf-8", 401)
            # JSON content type: a cross-site form can't send it without a preflight, so no CSRF token needed
            elif path == "/portal/api/edit" and edit and self.signed_in() and \
                    self.headers.get("Content-Type", "").startswith("application/json"):
                try:
                    self.send(json.dumps(edit(json.loads(self.body()))).encode(), "application/json")
                except ValueError as e:
                    self.send(json.dumps({"error": str(e)}).encode(), "application/json", 400)
            else:
                self.send_error(403)

        def do_GET(self):
            path, _, q = self.path.partition("?")
            args = urllib.parse.parse_qs(q)
            if not self.signed_in() and path != "/logo.png":
                if path == "/login":
                    self.send(LOGIN_PAGE, "text/html; charset=utf-8")
                else:
                    self.send(b"", "text/plain", 303, [("Location", "/login")])
                return
            if path == "/portal/api/edit":
                self.send(json.dumps({"edit": bool(edit)}).encode(), "application/json")
                return
            live, boundary = by.get((args.get("p") or [""])[0]) or next(iter(by.values()))
            if path == "/":
                lats, lons = zip(*live.place.points)
                tract = [min(lons), min(lats), max(lons), max(lats)]
                self.send(page().replace(b"/*AREA*/null", json.dumps(area(live.place)).encode())
                          .replace(b"/*TRACT*/null", json.dumps(tract).encode()), "text/html; charset=utf-8")
            elif path == "/logo.png":
                self.send(logo, "image/png")
            elif path == "/boundary.geojson":
                self.send(boundary, "application/geo+json")
            elif path == "/api/status":
                self.send(json.dumps(live.status("1" in args.get("fresh", []))).encode(), "application/json")
            elif portal and path.startswith("/portal"):
                f = (portal / urllib.parse.unquote(path[len("/portal"):]).lstrip("/")).resolve()
                f = f / "index.html" if f.is_dir() else f
                # stay inside the portal folder, known file types only
                if f.is_relative_to(portal) and f.suffix in PORTAL_TYPES and f.is_file():
                    self.send(f.read_bytes(), PORTAL_TYPES[f.suffix])
                else:
                    self.send_error(404)
            else:
                self.send_error(404)

        def log_message(self, *_):
            pass

    print(f"http://127.0.0.1:{port}", flush=True)
    ThreadingHTTPServer(("127.0.0.1", port), H).serve_forever()


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    # repeat the pair for more properties: --boundary a.geojson --name A --boundary b.geojson --name B
    ap.add_argument("--boundary", action="append", required=True)
    ap.add_argument("--name", action="append", required=True)
    ap.add_argument("--port", type=int, default=8765)
    ap.add_argument("--portal", help="built portal folder to serve at /portal/")
    a = ap.parse_args()
    if len(a.boundary) != len(a.name):
        ap.error("give one --name per --boundary")
    props = []
    for path, name in zip(a.boundary, a.name):
        gj = json.loads(Path(path).read_text(encoding="utf-8"))
        props.append((Live(Place(gj, name)), gj))
    serve(props, a.port, a.portal)
