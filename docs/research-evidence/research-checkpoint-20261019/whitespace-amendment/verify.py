#!/usr/bin/env python3
"""Read-only verification of the immutable base and additive EOF amendment."""
from pathlib import Path
from collections import Counter
import argparse,gzip,hashlib,json,subprocess
HERE=Path(__file__).resolve().parent;BASE=HERE.parent;ROOT=BASE.parents[2]
def sha(b):return hashlib.sha256(b).hexdigest()
def raw(folder,e):
 p=Path(e['archive_path']);assert not p.is_absolute() and '..' not in p.parts
 b=gzip.decompress((folder/p).read_bytes());assert sha(b)==e['sha256'] and len(b)==e['bytes'];return b

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check-live',action='store_true',help='Additionally require all1550 original research inputs locally; not needed for portable archive verification.')
 args=ap.parse_args();i=json.loads((HERE/'index.json').read_text())
 for name,h in i['immutable_base'].items():assert sha((BASE/name).read_bytes())==h,name
 for folder in [BASE,HERE]:
  m=json.loads((folder/'manifest.json').read_text())
  for x in m['files']:
   b=(folder/x['path']).read_bytes();assert sha(b)==x['sha256'] and len(b)==x['bytes'],x['path']
 subprocess.run(['python3',str(BASE/'restore.py'),'--verify'],check=True,capture_output=True,text=True)
 old=json.loads((BASE/'index.json').read_text());oldmap={e['repository_relative_path']:e for e in old['entries']}
 newmap={e['repository_relative_path']:e for e in i['entries']}
 for e in i['entries']:raw(HERE,e)
 changes=json.loads(raw(HERE,newmap[i['normalization_record']]))['changes']
 assert len(changes)==4
 for c in changes:
  before=raw(BASE,oldmap[c['path']]);after=raw(HERE,newmap[c['path']])
  saved=raw(HERE,newmap[c['original_snapshot']])
  assert sha(before)==c['before'] and sha(after)==c['after'] and saved==before
  assert before==after+b'\n'*c['removed_trailing_LF'] and before.rstrip(b'\n')==after.rstrip(b'\n')
  assert c['removed_trailing_LF']==1 and c['only_trailing_LF_changed']
 canonical=json.loads(raw(HERE,newmap[i['current_checkpoint']]))
 coverage=Counter();unresolved=[]
 excluded={e['repository_relative_path']:e for e in json.loads((BASE/'excluded-primary-fingerprints.json').read_text())['excluded']}
 oldcoverage=json.loads((BASE/'publication-coverage.json').read_text())
 tracked={e['path']:e['sha256'] for e in oldcoverage['pin_records'] if e['portable_status']=='tracked-source-or-document'}
 for pin in canonical['source_pins']:
  p=pin['path'];a=newmap.get(p) or oldmap.get(p)
  if a and a['sha256']==pin['sha256']:kind='archived-exact-bytes'
  elif tracked.get(p)==pin['sha256']:kind='tracked-source-or-document'
  elif p in excluded and excluded[p]['sha256']==pin['sha256']:kind='excluded-primary-fingerprint'
  elif '.lake/packages/' in p:kind='locked-upstream-package-source'
  elif any(x in p for x in ['.olean','.ilean','.ir','.trace']):kind='excluded-compiled-artifact'
  elif Path(p).is_absolute() and any(e['original_path']==p and e['sha256']==pin['sha256'] for e in old['entries']):kind='archived-exact-bytes'
  else:unresolved.append(p);kind='unresolved'
  coverage[kind]+=1
  if args.check_live:
   f=Path(p) if Path(p).is_absolute() else ROOT/p
   assert f.is_file() and sha(f.read_bytes())==pin['sha256'],p
 assert not unresolved,unresolved
 deps=json.loads((BASE/'replay-dependencies.json').read_text())
 for p in deps['topological_compile_order']:
  e=newmap.get(p) or oldmap.get(p);assert e is not None
  if args.check_live:assert sha((ROOT/p).read_bytes())==e['sha256'],p
 assert len(canonical['source_pins'])==1550
 print(json.dumps({'terminal_exit_code':0,'base_files_verified':len(old['entries']),'amendment_files_verified':len(i['entries']),'normalizations_verified':len(changes),'only_one_trailing_LF_removed_each':True,'current_checkpoint_pins':1550,'portable_pin_coverage':dict(coverage),'unresolved_portable_references':0,'isolated_source_leaves':len(deps['topological_compile_order']),'source_dependencies_complete':not deps['missing_local_sources'],'all_live_pins_checked':args.check_live,'fresh_Lean_build_claimed':False}))
if __name__=='__main__':main()
