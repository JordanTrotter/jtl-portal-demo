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
    return {"iv": b64(iv), "ct": b64(AESGCM(key).encrypt(iv, json.dumps(obj, separators=(",", ":")).encode(), None))}


def unseal(box, key):
    return json.loads(AESGCM(key).decrypt(base64.b64decode(box["iv"]), base64.b64decode(box["ct"]), None))


def main(site):
    import live_map  # beside this file in the Pages repo
    key = base64.b64decode(os.environ["LIVE_KEY"])
    live = Path(site) / "live"
    b = unseal(json.loads((live / "boundary.enc").read_text()), key)
    status = live_map.Live(live_map.Place(b["geojson"], b["name"])).status()
    (live / "status.enc").write_text(json.dumps(seal(status, key)))
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
        print("ok")
    elif len(sys.argv) == 2:
        main(sys.argv[1])
    else:
        sys.exit(__doc__)
