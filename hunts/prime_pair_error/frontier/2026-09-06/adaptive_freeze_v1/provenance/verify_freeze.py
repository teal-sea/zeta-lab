#!/usr/bin/env python3
"""Verify an immutable research snapshot. Checks bytes, not mathematical claims."""
from __future__ import annotations
import argparse
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import stat
import sys
import zipfile

SNAPSHOT_ID = 'zeta-adaptive-freeze-v1'
MAX_BYTES = 256 * 1024 * 1024
MAX_MEMBERS = 100000
MAX_DEPTH = 12

def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def safe_name(name: str) -> str:
    p = PurePosixPath(name)
    if not name or '\\' in name or p.is_absolute() or '..' in p.parts or ':' in name:
        raise ValueError(f'Unsafe archive/manifest path: {name!r}')
    normal = p.as_posix()
    if normal != name.rstrip('/') or normal == '.':
        raise ValueError(f'Non-canonical path: {name!r}')
    return normal

def inspect_archive(data: bytes, label: str, depth: int = 0,
                    budget: list[int] | None = None) -> list[dict]:
    if depth > MAX_DEPTH:
        raise ValueError('Archive nesting exceeds limit')
    if budget is None:
        budget = [0, 0]
    rows = []
    with zipfile.ZipFile(io.BytesIO(data)) as z:
        names = [i.filename for i in z.infolist()]
        if len(names) != len(set(names)):
            raise ValueError(f'Duplicate ZIP members in {label}')
        files = [i for i in z.infolist() if not i.is_dir()]
        if not files:
            raise ValueError(f'Empty archive: {label}')
        for info in z.infolist():
            safe_name(info.filename)
            mode = (info.external_attr >> 16) & 0xffff
            if stat.S_ISLNK(mode) or info.flag_bits & 1:
                raise ValueError(f'Linked or encrypted member: {label}!/{info.filename}')
            if info.is_dir():
                continue
            budget[0] += info.file_size
            budget[1] += 1
            if budget[0] > MAX_BYTES or budget[1] > MAX_MEMBERS:
                raise ValueError('Archive safety budget exceeded')
            raw = z.read(info)  # ZIP reader verifies CRC here.
            if len(raw) != info.file_size:
                raise ValueError('ZIP length mismatch')
            locator = f'{label}!/{info.filename}'
            rows.append({'locator': locator, 'bytes': len(raw), 'sha256': digest(raw)})
            if info.filename.lower().endswith('.zip'):
                rows.extend(inspect_archive(raw, locator, depth + 1, budget))
    return sorted(rows, key=lambda x: x['locator'])

def verify(root: Path) -> dict:
    root = root.resolve()
    manifest_path = root / 'FILE_MANIFEST.json'
    if not manifest_path.is_file() or manifest_path.is_symlink():
        raise ValueError('Missing or linked FILE_MANIFEST.json')
    manifest = json.loads(manifest_path.read_text(encoding='utf-8'))
    if manifest.get('snapshot_id') != SNAPSHOT_ID:
        raise ValueError('Wrong snapshot identity')
    entries = manifest.get('files')
    if not isinstance(entries, list) or not entries:
        raise ValueError('Empty or invalid file manifest')
    expected = {}
    for row in entries:
        if not isinstance(row, dict):
            raise ValueError('Invalid manifest row')
        name = safe_name(row['path'])
        if name in expected or name == 'FILE_MANIFEST.json':
            raise ValueError('Duplicate or self-referencing manifest entry')
        expected[name] = row
    actual = set()
    for p in root.rglob('*'):
        if p.is_symlink():
            raise ValueError(f'Symlink in snapshot: {p}')
        if p.is_file():
            actual.add(p.relative_to(root).as_posix())
    if actual != set(expected) | {'FILE_MANIFEST.json'}:
        raise ValueError(f'File inventory mismatch: {sorted(actual ^ (set(expected) | {"FILE_MANIFEST.json"}))}')
    for name, row in expected.items():
        raw = (root / name).read_bytes()
        if len(raw) != row['bytes'] or digest(raw) != row['sha256']:
            raise ValueError(f'Size/hash mismatch: {name}')
    archives = sorted(name for name in expected if name.startswith('original_archives/') and name.endswith('.zip'))
    if len(archives) != 17:
        raise ValueError('Expected 17 original archives')
    members = []
    budget = [0, 0]
    for name in archives:
        members.extend(inspect_archive((root / name).read_bytes(), name, budget=budget))
    members = sorted(members, key=lambda x: x['locator'])
    recorded = json.loads((root / 'ARCHIVE_CONTENTS.json').read_text(encoding='utf-8'))
    if not isinstance(recorded, list) or not recorded or recorded != members:
        raise ValueError('Recursive archive inventory mismatch')
    mapping = json.loads((root / 'IMPORT_MAP.json').read_text(encoding='utf-8'))
    if not isinstance(mapping, list) or len(mapping) != 3:
        raise ValueError('Missing latest-package import mapping')
    extracted_count = 0
    for item in mapping:
        with zipfile.ZipFile(root / item['archive']) as z:
            expected_names = set()
            for info in z.infolist():
                if info.is_dir():
                    continue
                member = safe_name(info.filename)
                if not member.startswith(item['member_prefix']):
                    raise ValueError('Unexpected package root')
                rel = member[len(item['member_prefix']):]
                target = root / item['extracted_path'] / rel
                if not target.is_file() or target.read_bytes() != z.read(info):
                    raise ValueError(f'Extracted file mismatch: {target}')
                expected_names.add(rel)
                extracted_count += 1
            actual_names = {p.relative_to(root / item['extracted_path']).as_posix()
                            for p in (root / item['extracted_path']).rglob('*') if p.is_file()}
            if actual_names != expected_names:
                raise ValueError('Extracted directory has missing or extra files')
    return {'snapshot_id': SNAPSHOT_ID, 'status': 'PASS', 'payload_files': len(entries),
            'original_archives': len(archives), 'recursive_archive_member_occurrences': len(members),
            'latest_extracted_files': extracted_count,
            'scope': 'Byte integrity, CRC and inventories only; not a proof review or fresh research run.'}

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    try:
        result = verify(args.root)
    except (OSError, ValueError, KeyError, TypeError, zipfile.BadZipFile) as e:
        print(f'FAIL: {e}', file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2))
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
