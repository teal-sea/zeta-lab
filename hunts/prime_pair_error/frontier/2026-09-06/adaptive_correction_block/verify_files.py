#!/usr/bin/env python3
"""Fail-closed integrity check for this frozen research artifact.

It verifies archival bytes, not the mathematical claims. Normal Python bytecode
cache files are not payloads. Assertions are deliberately not used as gates.
"""
from pathlib import Path
import hashlib,json,zipfile
root=Path(__file__).resolve().parent
manifest=json.loads((root/'SHA256SUMS.json').read_text())
if not isinstance(manifest,dict) or not manifest:
 raise ValueError('Missing or empty inventory')
seen={p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
expected=set(manifest)|{'SHA256SUMS.json'}
if seen!=expected:
 raise ValueError(f'Inventory mismatch: {seen ^ expected}')
for name,record in manifest.items():
 relative=Path(name)
 if relative.is_absolute() or '..' in relative.parts:
  raise ValueError(f'Unsafe inventory name: {name}')
 p=root/relative
 if not p.is_file() or p.is_symlink() or p.stat().st_size!=record['bytes']:
  raise ValueError(f'Missing, linked, or wrong-size file: {name}')
 if hashlib.sha256(p.read_bytes()).hexdigest()!=record['sha256']:
  raise ValueError(f'Hash mismatch: {name}')
 if p.suffix=='.zip':
  with zipfile.ZipFile(p) as z:
   bad=z.testzip()
   if bad is not None:raise ValueError(f'ZIP CRC failure: {name}:{bad}')
print(f'PASS: {len(manifest)} payload files, exact lengths and hashes; input ZIP CRC checked')
