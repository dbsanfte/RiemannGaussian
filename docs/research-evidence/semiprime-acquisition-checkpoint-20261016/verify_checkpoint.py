#!/usr/bin/env python3
"""Verify this publication packet's hashes, originals when available, and local links."""
from pathlib import Path
import gzip,hashlib,json,re
H=Path(__file__).resolve().parent
R=H.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest()
m=json.loads((H/'manifest.json').read_text())
listed=set()
for rec in m['files']:
 p=H/rec['path'];b=p.read_bytes();assert len(b)==rec['bytes'] and sha(b)==rec['sha256'],p
 listed.add(p)
assert {p for p in H.rglob('*') if p.is_file()}==listed|{H/'manifest.json'},'unlisted payload'
sm=json.loads((H/'source-map.json').read_text())
for rec in sm['records']:
 p=R/rec['resolved_path'];b=p.read_bytes();b=gzip.decompress(b) if rec.get('gzip') else b
 assert len(b)==rec['bytes'] and sha(b)==rec['sha256'],p
 original=Path(rec['original_path'])
 if original.is_file():assert sha(original.read_bytes())==rec['sha256'],original
for name in ['README.md','latest-verdicts.md']:
 p=H/name
 for link in re.findall(r'\]\(([^)\s]+)\)',p.read_text()):
  if link.startswith(('https:','http:','#')):continue
  assert (p.parent/link.split('#')[0]).exists(),(name,link)
review=(H/'reviews/paid-cover-independent-617.md').read_text()
assert sha((H/'reports/group-gap-criterion.md').read_bytes()) in review,'review target pin'
for rec in json.loads((H/'sources/qrh-primary-source-pins.json').read_text())['files']:
 p=Path(rec['file'])
 if p.is_file():assert len(p.read_bytes())==rec['bytes'] and sha(p.read_bytes())==rec['sha256'],p
validation=json.loads((H/'validation/source-and-pin-recheck.json').read_text())
for rec in validation['files']:
 p=R/rec['path'];b=p.read_bytes();assert len(b)==rec['bytes'] and sha(b)==rec['sha256'],p
pins=0
for audit in validation['audit_pin_recheck']:
 for rec in audit['pins']:
  p=R/rec['path'];assert sha(p.read_bytes())==rec['expected'] and rec['status']=='MATCH',p;pins+=1
assert pins==58,pins
assert m['goal_status']=='paused' and m['all_input_sixth_rate_proved'] is False
print(f"PASS: {len(listed)} pinned payloads; {len(sm['records'])} portable original/alias resolutions; original bytes unchanged when present; reviewed GAP target pin and README links valid.")
