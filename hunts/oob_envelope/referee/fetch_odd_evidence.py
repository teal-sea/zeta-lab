"""Download deciding odd artifacts and verify every saved payload hash.

Only file transfer and hashing run here; no matrix computation is local.
Intermediate panel matrices remain on the named volume with their hashes.
"""

import argparse
import gzip
import hashlib
import json
import subprocess
from pathlib import Path


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("revision")
    parser.add_argument("case", choices=("zhu", "main"))
    args = parser.parse_args()
    base = Path(__file__).resolve().parent
    dest = base/"outputs_odd"/args.revision/args.case
    dest.mkdir(parents=True, exist_ok=True)
    remote = f"/odd/{args.revision}/reduce_{args.case}"

    def get(name):
        target = dest/name
        if not target.exists():
            subprocess.run(["modal", "volume", "get", "oob-envelope-referee",
                            remote+"/"+name, str(target), "--profile", "teal-sea"], check=True)
        return target

    manifest = json.loads(get("manifest.json").read_text())
    assert manifest["status"] == "completed"
    files = ["result.json", "budget.json", "quadrature_checks.json", "assembly_manifest.json",
             "positivity.json", "ritz.json", "matrix.json.gz", "factor.json.gz"]
    if args.case == "main":
        files.append("controls.json")
    checks = {}
    for name in files:
        path = get(name)
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        assert digest == manifest["output_sha256"][name], name
        checks[name] = digest
        if name.endswith(".gz"):
            digest = hashlib.sha256()
            with gzip.open(path,"rb") as stream:
                for chunk in iter(lambda: stream.read(1024*1024), b""):
                    digest.update(chunk)
            assert digest.hexdigest() == manifest["output_sha256"][name[:-3]], name
            checks[name+":decompressed"] = digest.hexdigest()
    for name, digest in manifest["input_sha256"].items():
        assert hashlib.sha256((base/name).read_bytes()).hexdigest() == digest, name
    (dest/"download_verification.json").write_text(json.dumps({"verified":True,"hashes":checks},indent=2)+"\n")
    print(f"{args.case}: {len(files)} artifacts verified against the durable manifest",flush=True)


if __name__ == "__main__":
    main()
