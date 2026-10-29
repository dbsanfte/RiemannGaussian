"""Finish the reviewed archive after its initial forward-manifest link check."""
from pathlib import Path
import hashlib,json,re,shutil,subprocess
r=Path('/home/dbsanfte/riemann/formal');w=Path('/tmp/semiprime-ternary-machine-20261027')
p=r/'docs/research-evidence/semiprime-paid-materialization-20261027'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
assert p.is_dir() and not (p/'manifest.json').exists()
base=json.loads((p/'preservation-before.json').read_text())
for k in ['protected','concurrent']:
 for rel,h in base[k].items():assert sha(r/rel)==h,(k,rel)
for rel,x in base['prefixes'].items():
 data=(r/rel).read_bytes();assert hashlib.sha256(data[:x['bytes']]).hexdigest()==x['sha256']
 assert data[x['bytes']:].decode().count('## Paid materialization gives a paper bit-time result, 2026-10-27')==1
prov=json.loads((p/'archive-provenance.json').read_text())
empty=p/'archive-result.json';assert empty.stat().st_size==0;empty.unlink();prov.pop('archive-result.json')
for name in ['paid-materialization-route.md','archive_materialization.py','seal_archive.py']:
 shutil.copyfile(w/name,p/name);prov[name]={'source':str(w/name),'sha256':sha(w/name)}
for name,x in prov.items():assert sha(p/name)==x['sha256'],name
dump(p/'archive-provenance.json',prov)
v=json.loads((p/'verification.json').read_text());assert v['generated_declarations']==409 and v['theorem_constants']==202
for m,x in v['modules'].items():
 assert sha(r/x['source'])==x['source_sha256']==sha(p/(m+'.lean'))
 assert sha(r/'.lake/build/lib/lean/RiemannGaussian'/(m+'.olean'))==x['olean_sha256']
for rel,h in json.loads((p/'runtime-dependencies.json').read_text()).items():assert sha(Path(rel))==h
files={str(f.relative_to(p)):{'bytes':f.stat().st_size,'sha256':sha(f)} for f in sorted(p.rglob('*')) if f.is_file()}
dump(p/'manifest.json',{'status':'PASS','files':files})
links=0
for f in p.glob('*.md'):
 s=re.sub(r'```.*?```','',f.read_text(),flags=re.S);s=re.sub(r'`[^`]*`','',s)
 for target in re.findall(r'\]\(([^)]+)\)',s):
  if target.startswith(('http://','https://','#')):continue
  assert (f.parent/target.split('#')[0]).exists(),(f.name,target);links+=1
assert subprocess.run(['git','diff','--check'],cwd=r,capture_output=True).returncode==0
print(json.dumps({'status':'PASS','packet':str(p),'files':len(files)+1,'manifest_entries':len(files),'links_checked':links,'prior_files_preserved':len(base['protected']),'concurrent_files_preserved':len(base['concurrent']),'append_prefixes_preserved':len(base['prefixes'])},indent=2))
