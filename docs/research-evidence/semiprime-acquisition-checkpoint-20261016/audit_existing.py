#!/usr/bin/env python3
"""Read-only audit of the 29 frozen evidence packets preceding this checkpoint."""
from pathlib import Path
import collections, gzip, hashlib, json, re, sys
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parent
DIRS=sorted(p for p in HERE.parent.glob('semiprime-*') if p != HERE and (p/'manifest.json').is_file())
def sha(data): return hashlib.sha256(data).hexdigest()
def readj(p): return json.loads(p.read_text())
def records(sm): return sm if isinstance(sm,list) else sm.get('records',sm.get('entries',[]))
def resolved(base,r):
 s=r.get('resolved_path') or r.get('path') or r.get('archive_path') or r.get('historical_archive_path')
 if not s:return None
 p=Path(s)
 return p if p.is_absolute() else ROOT/p if s.startswith(('docs/','RiemannGaussian/','scripts/')) else base/p
report={'scope':'29 frozen packets; read-only integrity and publication hygiene audit, not mathematical re-review','packets':[], 'manifest_errors':[], 'source_map_errors':[], 'broken_markdown_links':[], 'historical_context_links':[], 'unresolved_tmp_references':[], 'oversized_files':[], 'generated_or_secret_candidates':[], 'historical_current_file_drift':[], 'source_map_external_records':0}
allmap={}
for d in DIRS:
 sm=readj(d/'source-map.json')
 for r in records(sm)+readj(d/'manifest.json').get('source_pin_resolutions',[]):
  if r.get('original_path'):allmap[r['original_path']]=(d,r)
# Two aliases occur only in preserved historical prose. Resolve to existing bytes.
for original,rel,digest,length in [
 ('/tmp/semiprime-direct-frontier-20261016/norm/qholonomic.txt','semiprime-long-query-20261015/primary/qproducts-by.txt.gz','ae779c48d317414bc0223e381d6bc40296c5c9630903b4959e715e6b14d63c83',121716),
 ('/tmp/semiprime-mask-acquisition-20261007/cyclic-norm-obstruction.md','research-checkpoint-20261012/objects/26/264fca0018ff33277a172ea0e93f6273311a0178a038b127bca8978f8d315b4f.gz','264fca0018ff33277a172ea0e93f6273311a0178a038b127bca8978f8d315b4f',11565)]:
 p=HERE.parent/rel
 raw=gzip.decompress(p.read_bytes())
 assert sha(raw)==digest and len(raw)==length
 allmap[original]=(HERE,{'resolved_path':str(p.relative_to(ROOT)),'gzip':True,'sha256':digest,'bytes':length})
all_files=[]
for d in DIRS:
 m=readj(d/'manifest.json'); fs=[p for p in d.rglob('*') if p.is_file()];all_files+=fs
 listed=m.get('files',[]);listedpaths=set()
 for r in listed:
  p=d/r['path'];listedpaths.add(p)
  if not p.is_file():report['manifest_errors'].append({'packet':d.name,'path':r['path'],'error':'missing'});continue
  data=p.read_bytes()
  if len(data)!=r['bytes'] or sha(data)!=r['sha256']:report['manifest_errors'].append({'packet':d.name,'path':r['path'],'error':'size/hash mismatch'})
 unlisted=[str(p.relative_to(d)) for p in fs if p not in listedpaths and p.name!='manifest.json']
 if unlisted:report['manifest_errors'].append({'packet':d.name,'unlisted':unlisted})
 for r in records(readj(d/'source-map.json')):
  p=resolved(d,r)
  if p is None:
   report['source_map_external_records']+=1;continue
  if not p.is_file():report['source_map_errors'].append({'packet':d.name,'path':str(p),'error':'missing'});continue
  data=p.read_bytes()
  if r.get('uncompressed_sha256'):
   wanted=r['sha256'];length=r.get('bytes');actual=sha(data)
   if actual!=wanted or length is not None and len(data)!=length:report['source_map_errors'].append({'packet':d.name,'path':str(p),'error':'archive size/hash mismatch'})
   raw=gzip.decompress(data) if p.suffix=='.gz' else data
   if sha(raw)!=r['uncompressed_sha256'] or len(raw)!=r['uncompressed_bytes']:report['source_map_errors'].append({'packet':d.name,'path':str(p),'error':'uncompressed size/hash mismatch'})
  else:
   raw=gzip.decompress(data) if r.get('gzip') else data
   if sha(raw)!=r['sha256'] or len(raw)!=r['bytes']:
    key='source_map_errors' if '/docs/research-evidence/' in str(p) else 'historical_current_file_drift'
    report[key].append({'packet':d.name,'path':str(p),'error':'historical source size/hash differs from current file','expected_sha256':r['sha256'],'current_sha256':sha(raw)})
 for p in fs:
  data=p.read_bytes()
  if len(data)>5_000_000:report['oversized_files'].append({'path':str(p.relative_to(ROOT)),'bytes':len(data)})
  if p.is_symlink() or p.suffix in ('.olean','.pyc','.o','.so') or p.name in ('.env','id_rsa','credentials.json'):report['generated_or_secret_candidates'].append(str(p.relative_to(ROOT)))
  if p.suffix not in ('.md','.json','.txt','.py'):continue
  text=data.decode('utf-8',errors='replace')
  if re.search(r'-----BEGIN (?:OPENSSH |RSA |EC )?PRIVATE KEY-----|\bgh[pousr]_[A-Za-z0-9]{30,}|\bAKIA[A-Z0-9]{16}\b',text):report['generated_or_secret_candidates'].append(str(p.relative_to(ROOT)))
  if p.suffix=='.md':
   for link in re.findall(r'\]\(([^)\s]+)\)',text):
    if link.startswith(('http:','https:','#','mailto:','data:')):continue
    link=link.split('#')[0].strip('<>');link=re.sub(r':\d+$','',link)
    if not link:continue
    target=Path(link) if link.startswith('/') else p.parent/link
    if target.exists():continue
    if link in allmap:continue
    if p.name=='journal-entry.md' and (ROOT/'docs'/link).exists():
     report['historical_context_links'].append({'file':str(p.relative_to(ROOT)),'target':link,'resolved_path':str((ROOT/'docs'/link).relative_to(ROOT))});continue
    report['broken_markdown_links'].append({'file':str(p.relative_to(ROOT)),'target':link})
   for ref in set(re.findall(r'/tmp/[A-Za-z0-9_./+\-]+',text)):
    ref=ref.rstrip('.')
    if ref in allmap or any(k.startswith(ref.rstrip('/')+'/') for k in allmap):continue
    report['unresolved_tmp_references'].append({'file':str(p.relative_to(ROOT)),'reference':ref})
 report['packets'].append({'directory':d.name,'manifest_sha256':sha((d/'manifest.json').read_bytes()),'source_map_sha256':sha((d/'source-map.json').read_bytes()),'manifest_payloads':len(listed),'files_including_manifest':len(fs),'bytes':sum(p.stat().st_size for p in fs)})
report['totals']={'packets':len(DIRS),'manifest_payloads':sum(p['manifest_payloads'] for p in report['packets']),'files_including_manifests':len(all_files),'bytes':sum(p.stat().st_size for p in all_files)}
report['largest_files']=[{'path':str(p.relative_to(ROOT)),'bytes':p.stat().st_size} for p in sorted(all_files,key=lambda p:p.stat().st_size,reverse=True)[:10]]
if '--write' in sys.argv:(HERE/'existing-packets-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:(len(v) if isinstance(v,list) else v) for k,v in report.items() if k!='packets'},indent=2))
