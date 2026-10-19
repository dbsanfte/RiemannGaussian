#!/usr/bin/env python3
"""Check portable payload coverage and current isolated-leaf source dependencies."""
from pathlib import Path
from collections import Counter
import argparse,hashlib,json,subprocess
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
WRITE_RECORDS=False
def dump(name,data):
 if WRITE_RECORDS:(HERE/name).write_text(json.dumps(data,indent=2)+'\n')
def main():
 global WRITE_RECORDS
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write-records',action='store_true',help='Explicitly regenerate metadata for a new publication preparation; default is read-only.')
 WRITE_RECORDS=ap.parse_args().write_records
 index=json.loads((HERE/'index.json').read_text());inv=json.loads((HERE/'inventory.json').read_text())
 canonical=ROOT/inv['canonical_checkpoint'];j=json.loads(canonical.read_text())
 arch={e['repository_relative_path']:e for e in index['entries']};archabs={e['original_path']:e for e in index['entries']}
 excluded={e['repository_relative_path']:e for e in json.loads((HERE/'excluded-primary-fingerprints.json').read_text())['excluded']}
 tracked=set(subprocess.check_output(['git','ls-files','-z'],cwd=ROOT).decode().split('\0'))
 counts=Counter();records=[];unknown=[];mismatch=[]
 for x in j['source_pins']:
  s=x['path'];p=ROOT/s if not Path(s).is_absolute() else Path(s)
  if not p.is_file() or digest(p)!=x['sha256']:mismatch.append(s)
  a=arch.get(s) or archabs.get(s)
  if a and a['sha256']==x['sha256']:kind='archived-exact-bytes'
  elif s in tracked:kind='tracked-source-or-document'
  elif s in excluded and excluded[s]['sha256']==x['sha256']:kind='excluded-primary-fingerprint'
  elif '.lake/packages/' in s:kind='locked-upstream-package-source'
  elif any(z in s for z in ['.olean','.ilean','.ir','.trace']):kind='excluded-compiled-artifact'
  else:kind='unresolved-portable-payload';unknown.append(s)
  counts[kind]+=1;records.append({'path':s,'sha256':x['sha256'],'portable_status':kind})
 assert not unknown,unknown
 assert not mismatch,mismatch
 deps=json.loads((HERE/'replay-dependencies.json').read_text());texts=[]
 for e in index['entries']:
  if e['repository_relative_path'].endswith('.json'):
   p=ROOT/e['repository_relative_path']
   if p.exists():texts.append((e['repository_relative_path'],p.read_text(errors='replace')))
 leafhash={}
 for s in deps['topological_compile_order']:
  h=digest(ROOT/s);refs=[p for p,t in texts if h in t]
  assert refs,('No preserved hash reference',s)
  assert s in arch and arch[s]['sha256']==h,('Source snapshot missing',s)
  leafhash[s]={'sha256':h,'hash_reference_paths':refs,'has_preserved_hash_reference':True}
 assert not deps['missing_local_sources']
 scriptmods={m for mods in deps['imports'].values() for m in mods if m.startswith('scripts.')}
 dump('leaf-hash-reference-map.json',{'scope':'Current source SHA occurrences in preserved JSON metadata; not alone a terminal compiler certificate.','sources':leafhash})
 coverage={'scope':'Research source/canonical pin coverage; root publication generated assets and historical compiler checks are separate.','canonical_checkpoint':inv['canonical_checkpoint'],'canonical_checkpoint_sha256':digest(canonical),'canonical_pins':len(j['source_pins']),'all_current_live_pins_match':True,'pin_payload_counts':dict(counts),'unresolved_portable_payloads':unknown,'untracked_research_proof_leaves':len(leafhash),'all_local_import_sources_present':True,'distinct_scripts_module_dependencies':len(scriptmods),'unqualified_bootstrap_aliases':deps['unqualified_bootstrap_aliases'],'all_current_leaf_hashes_have_preserved_json_references':True,'normal_candidate_counts':{'untracked_lean':inv['untracked_lean_leaves'],'untracked_docs':inv['untracked_docs']},'excluded_transient_publication_paths':inv['normal_publication_paths_not_snapshotted'],'pin_records':records}
 dump('publication-coverage.json',coverage)
 checked=subprocess.run(['python3',str(HERE/'restore.py'),'--verify'],capture_output=True,text=True,check=True)
 result={'terminal_exit_code':checked.returncode,'archive':json.loads(checked.stdout),'canonical_live_pins':len(j['source_pins']),'canonical_live_pin_mismatches':0,'source_leaves':len(leafhash),'distinct_scripts_module_dependencies':len(scriptmods),'unqualified_bootstrap_aliases':len(deps['unqualified_bootstrap_aliases']),'missing_local_sources':0,'unresolved_portable_payloads':0,'scope':'Archive/hash/source-closure audit only; no Lean rebuild, analytic verification, semiprime research or optional numerical certificate replay.'}
 dump('verification.json',result);print(json.dumps(result))
if __name__=='__main__':main()
