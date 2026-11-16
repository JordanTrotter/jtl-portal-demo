"""Live data for the static portal link. Runs in GitHub Actions about every 15 min (live.yml), no AI.

    python live_job.py <site-dir>     # reads <site>/live/boundary.enc, writes <site>/live/status.enc

LIVE_KEY (base64, 32 bytes) is an Actions secret. It is a random key, not the page passphrase;
the page gets it from inside the passphrase-encrypted bundle. The same seal() encrypts the
boundary at build time (build_portal.static_site).
"""
import base64
import json
import os
import sys
from pathlib import Path

from cryptography.hazmat.primitives.ciphers.aead import AESGCM

b64 = lambda b: base64.b64encode(b).decode()


def seal(obj, key):
    iv = os.urandom(12)
    return {"iv": b64(iv), "ct": b64(AESGCM(key).encrypt(iv, json.dumps(obj, separators=(",", ":"), default=list).encode(), None))}


def unseal(box, key):
    return json.loads(AESGCM(key).decrypt(base64.b64decode(box["iv"]), base64.b64decode(box["ct"]), None))


# Each Actions run is a fresh machine. The feed cache and the live map's small state files (fire-rating history, lightning
# log) ride between runs in the Actions cache (live.yml), sealed with LIVE_KEY: the repo is public and the cache names
# places near the tract. With it, each feed refreshes on its own TTL instead of every run (rate-limit review 2026-11-16).
def restore(lv, state, key):
    blob = state / "live_cache.enc"
    if not blob.exists():
        return
    try:
        saved = unseal(json.loads(blob.read_text()), key)
    except Exception as e:  # a rotated key or a bad file: start clean, never fail the run
        print("cache not restored:", type(e).__name__)
        return
    lv.cache = saved.get("cache", {})
    for name, text in saved.get("files", {}).items():
        (state / name).write_text(text)


def keep(lv, state, key):
    state.mkdir(exist_ok=True)
    files = {f.name: f.read_text() for f in state.glob("*.json")}
    (state / "live_cache.enc").write_text(json.dumps(seal({"cache": lv.cache, "files": files}, key)))


def main(site):
    import live_map  # beside this file in the Pages repo
    key = base64.b64decode(os.environ["LIVE_KEY"])
    live = Path(site) / "live"
    b = unseal(json.loads((live / "boundary.enc").read_text()), key)
    lv = live_map.Live(live_map.Place(b["geojson"], b["name"]))
    restore(lv, live_map.STATE, key)
    live_map.load_backoff()  # the backoff file came back with the restore
    status = lv.status()
    (live / "status.enc").write_text(json.dumps(seal(status, key)))
    keep(lv, live_map.STATE, key)
    print(status["level"], "errors:", status["errors"] or "none")


if __name__ == "__main__":
    if sys.argv[1:] == ["--check"]:
        k = os.urandom(32)
        box = seal({"stand": "TEST-STAND-0"}, k)
        assert unseal(box, k) == {"stand": "TEST-STAND-0"} and "TEST-STAND-0" not in box["ct"]
        try:
            unseal(box, os.urandom(32))
            raise AssertionError("wrong key opened it")
        except Exception as e:
            assert type(e).__name__ == "InvalidTag", e
        import tempfile

        class Fake:
            cache = {"nws": {"at": 1, "tried": 1, "data": {"swept": {1, 2}}, "error": None}}
        st = Path(tempfile.mkdtemp())
        (st / "x_fireclass.json").write_text('{"2026-11-16": "Low"}')
        keep(Fake(), st, k)
        assert "Low" not in (st / "live_cache.enc").read_text()  # sealed
        (st / "x_fireclass.json").unlink()
        f2 = Fake()
        f2.cache = {}
        restore(f2, st, k)
        assert f2.cache["nws"]["data"]["swept"] == [1, 2] and (st / "x_fireclass.json").read_text() == '{"2026-11-16": "Low"}'
        restore(f2, st, os.urandom(32))  # wrong key: no crash
        print("ok")
    elif len(sys.argv) == 2:
        main(sys.argv[1])
    else:
        sys.exit(__doc__)
