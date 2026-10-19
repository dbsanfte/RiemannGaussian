#!/usr/bin/env python3
"""Build a byte-preserving research archive without caches or external paper bodies.
Only this checkpoint directory is written. Source reports are never modified.
"""
from pathlib import Path
from collections import Counter
import argparse, gzip, hashlib, io, json, os, re, subprocess

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
EXTERNAL_MD={'rstation-paper8-v1.md','rstation-paper10-v2.md','harmonic_mobius_ratio_recovery.md','hybrid-character-moment.md','method-comparison.md'}
OWN_TXT={'unitary-convolution-preflight.txt','coprime-inverse-preflight.txt','probe.stdout.txt'}
CACHE_SUFFIX={'.olean','.ilean','.c','.ir','.hash','.trace','.sig','.private','.server','.pyc','.pack','.idx','.png','.jpg','.jpeg','.svg','.zip','.tar','.gz','.so','.a','.o'}
TEXT_SUFFIX={'.md','.json','.py','.lean','.log','.sh','.txt','.csv','.yaml','.yml','.toml','.patch','.diff','.sha256'}
PRUNE={'.git','.lake','__pycache__','node_modules','.venv','venv','packages'}

def digest(data):return hashlib.sha256(data).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
def rel(p):
 try:return str(p.relative_to(ROOT))
 except ValueError:return 'external/riemann/'+p.name
def dump(name,data):(HERE/name).write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n')
def classify(p):
 s=p.suffix.lower(); parts=p.parts
 if '/openai-math-review/verification/OAI/' in str(p):return 'upstream-software-copy'
 if '/openai-math-review/preprints/' in str(p):return 'external-primary-body'
 if p.name in EXTERNAL_MD or ('/openai-math-review/' in str(p) and p.name=='CONTENTS.md'):return 'external-primary-body'
 if s in {'.pdf','.html','.htm','.tex','.bib','.epub','.ps','.sty','.png','.jpg','.jpeg'}:return 'external-primary-body'
 if s=='.txt' and p.name not in OWN_TXT:return 'external-primary-body'
 if s in CACHE_SUFFIX:return 'generated-cache'
 if p.name in {'tree.json','tree-recursive.json'} and p.stat().st_size>1000000:return 'upstream-tree-cache'
 if s in TEXT_SUFFIX or p.name in {'lean-toolchain','lake-manifest.json','lakefile.lean','LICENSE'}:return 'archive'
 return 'nonresearch-or-cache'

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--inventory-only',action='store_true');args=ap.parse_args()
 untracked=[x.decode() for x in git('ls-files','--others','--exclude-standard','-z').split(b'\0') if x]
 untracked=[s for s in untracked if not s.startswith(rel(HERE)+'/')]
 tracked_changes=git('diff','--name-only','HEAD').decode().splitlines()
 roots=sorted(p for p in (ROOT/'.lake').iterdir() if p.is_dir() and ((p.name.startswith('arithmetic-operator-') and not p.name.startswith('arithmetic-operator-publication-')) or p.name.startswith('siegel')))
 candidates=[];pruned=[]
 for root in roots:
  for base,dirs,files in os.walk(root):
   for d in list(dirs):
    p=Path(base)/d
    if d in PRUNE or p.is_symlink() or ('/openai-math-review/' in str(p) and d in {'preprints','OAI'}):
     dirs.remove(d);pruned.append(rel(p))
   for name in files:
    p=Path(base)/name
    if not p.is_symlink():candidates.append(p)
 counts=Counter();sizes=Counter();included=[];excluded=[]
 for p in sorted(candidates):
  category=classify(p);size=p.stat().st_size;counts[category]+=1;sizes[category]+=size
  if category=='archive':included.append(p)
  elif category in {'external-primary-body','upstream-tree-cache'}:
   excluded.append({'original_path':str(p),'repository_relative_path':rel(p),'reason':category,'bytes':size,'sha256':digest(p.read_bytes())})
 # A few primary metadata/software paths may have been pruned wholesale; record policy rather than claiming their hashes.
 source_records=[]
 for s in untracked+tracked_changes:
  p=ROOT/s
  if not p.is_file():continue
  source_records.append({'path':s,'status':'untracked' if s in untracked else 'tracked-modified','bytes':p.stat().st_size,'sha256':digest(p.read_bytes())})
 leaves=[s for s in untracked if s.endswith('.lean')]
 names={Path(s).stem:s for s in leaves}
 imports={};local_edges={};missing=[];aliases={}
 for s in leaves:
  text=(ROOT/s).read_text();mods=re.findall(r'^import\s+([^\n]+)',text,re.M)
  mods=[m for line in mods for m in line.split() if not m.startswith('--')]
  imports[s]=mods;local_edges[s]=[]
  for m in mods:
   src=ROOT/(m.replace('.','/')+'.lean')
   if m.startswith('scripts.'):
    if not src.is_file():missing.append({'leaf':s,'import':m})
    elif rel(src) in leaves:local_edges[s].append(rel(src))
   elif '.' not in m and m in names:
    local_edges[s].append(names[m]);aliases[m]=names[m]
 order=[];visiting=set();visited=set()
 def visit(s):
  if s in visited:return
  if s in visiting:raise RuntimeError('Local import cycle: '+s)
  visiting.add(s)
  for dep in local_edges[s]:visit(dep)
  visiting.remove(s);visited.add(s);order.append(s)
 for s in leaves:visit(s)
 assert not missing,missing
 deps={'scope':'Source import inventory; no broad rebuild. Historical leaf-specific strict producers remain separately archived.','lean_toolchain':(ROOT/'lean-toolchain').read_text().strip(),'leaf_count':len(leaves),'imports':imports,'local_source_dependencies':local_edges,'topological_compile_order':order,'unqualified_bootstrap_aliases':aliases,'missing_local_sources':missing,'command_pattern':'lake env bash -c \'export LEAN_PATH="$AUDIT_OUTPUT:$LEAN_PATH"; exec lean -DwarningAsError=true -o "$AUDIT_OUTPUT/scripts/LEAF.olean" scripts/LEAF.lean\'','notes':['Initialize AUDIT_OUTPUT/scripts and all documented run_cmd output directories before cold compilation.','Use a separate fresh checkout/worktree: run_cmd writes historical per-leaf axiom output paths. Do not replay against frozen local artifacts.','Prepend the private audit output AFTER lake env so lake does not overwrite LEAN_PATH.','Compile dependencies first in the listed order; scripts.* imports resolve under AUDIT_OUTPUT/scripts.','For each listed unqualified bootstrap alias, make the same built olean available under AUDIT_OUTPUT/<alias>.olean as the historical bootstrap does.','OAI imports are the tracked vendor/openai-quasi-rh closure; Mathlib/dependency revisions are fixed by lake-manifest.json and lean-toolchain.','Historical command absolute paths may be relocated; frozen report bytes and expected hashes are preserved. A fresh rerun is new evidence and must not rewrite the historical records.']}
 dump('replay-dependencies.json',deps)
 # Find local source terminal evidence, without treating an unbuilt source as certified.
 terminal={}
 for p in included:
  if p.suffix not in {'.json','.log','.md'}:continue
  try:t=p.read_text()
  except (UnicodeError,OSError):continue
  for s in leaves:
   if Path(s).name in t:
    terminal.setdefault(s,[]).append(rel(p))
 dump('leaf-evidence-map.json',{'scope':'Textual evidence-reference map only; a reference is not an assertion that every historical diagnostic succeeded. Final strict/axiom metadata must be assessed separately.','leaves':[{ 'source':s,'source_sha256':digest((ROOT/s).read_bytes()),'evidence_paths':terminal.get(s,[])} for s in leaves]})
 checkpoint=ROOT/'docs/arithmetic-operator-source-normalized-marked-gates.json'
 pinned=json.loads(checkpoint.read_text());bad=[]
 for x in pinned['source_pins']:
  f=ROOT/x['path']
  if not f.is_file() or digest(f.read_bytes())!=x['sha256']:bad.append(x['path'])
 # The parent may intentionally refresh live shared docs during publication; report rather than rewrite history.
 summary={'head':git('rev-parse','HEAD').decode().strip(),'recorded_date':'2026-10-19','untracked_count':len(untracked),'untracked_lean_leaves':len(leaves),'untracked_docs':sum(s.startswith('docs/') for s in untracked),'tracked_modified_count':len(tracked_changes),'research_roots':len(roots),'research_candidates':len(candidates),'classification_counts':dict(counts),'classification_bytes':dict(sizes),'pruned_cache_or_upstream_roots':pruned,'normal_publication_candidates':source_records,'normal_publication_paths_not_snapshotted':[s for s in untracked+tracked_changes if not ((s.startswith('scripts/') and s.endswith('.lean')) or (s.startswith('docs/arithmetic-operator-') and not s.startswith('docs/arithmetic-operator-publication-')) or s=='docs/siegel-interpolation-review.md' or s in {'AGENTS.md','arithmetic_operator_research_roadmap.md'})],'canonical_checkpoint':rel(checkpoint),'canonical_checkpoint_sha256':digest(checkpoint.read_bytes()),'canonical_pins':len(pinned['source_pins']),'canonical_pin_live_mismatches':bad,'canonical_pin_scope':'Historical frozen expected values are never rewritten; live shared doc changes during parent publication are reported explicitly.','semiprime':'Paused; no semiprime research or optional numerical certificate replay performed.'}
 dump('inventory.json',summary);dump('excluded-primary-fingerprints.json',{'policy':'Full third-party primary paper bodies are not republished, including extracted text/HTML/Markdown. Frozen source pin/URL records remain archived. Compiler/bootstrap caches are omitted and source replay is documented.','excluded':excluded})
 if args.inventory_only:
  print(json.dumps({'inventory_only':True,'included':len(included),'counts':dict(counts),'bytes':dict(sizes),'leaves':len(leaves)}));return
 entries=[];seen={};urlrefs=[]
 # Normal publication leaves/docs are also snapshotted for audit reproducibility, but remain ordinary tracked candidates.
 research_sources=[s for s in untracked+tracked_changes if (s.startswith('scripts/') and s.endswith('.lean')) or (s.startswith('docs/arithmetic-operator-') and not s.startswith('docs/arithmetic-operator-publication-')) or s=='docs/siegel-interpolation-review.md' or s in {'AGENTS.md','arithmetic_operator_research_roadmap.md'}]
 payloads=included+[ROOT/s for s in research_sources if (ROOT/s).is_file()]
 roadmap=ROOT.parent/'arithmetic_operator_research_roadmap.md'
 if roadmap.is_file():payloads.append(roadmap)
 for p in sorted(set(payloads)):
  data=p.read_bytes();h=digest(data);obj=Path('objects')/h[:2]/(h+'.gz')
  if h not in seen:
   dest=HERE/obj;dest.parent.mkdir(parents=True,exist_ok=True)
   buf=io.BytesIO()
   with gzip.GzipFile(filename='',mode='wb',fileobj=buf,mtime=0,compresslevel=9) as gz:gz.write(data)
   compressed=buf.getvalue()
   if dest.exists():assert dest.read_bytes()==compressed
   else:dest.write_bytes(compressed)
   seen[h]=len(compressed)
  entries.append({'original_path':str(p),'repository_relative_path':rel(p),'sha256':h,'bytes':len(data),'archive_path':str(obj),'status':'external-roadmap-snapshot' if p==roadmap else ('normal-source-snapshot' if rel(p) in research_sources else 'ignored-research-evidence')})
  if p.suffix in {'.json','.md','.txt','.py'}:
   try:
    for u in sorted(set(re.findall(r'https?://[^\s<>"\)\]\\]+',data.decode()))):urlrefs.append({'source_path':rel(p),'url':u.rstrip('.,;')})
   except UnicodeError:pass
 dump('primary-url-catalog.json',{'scope':'URLs retained verbatim from archived research/pin/probe sources; catalog membership is not availability or mathematical verification.','references':urlrefs})
 index={'created_utc':'2026-10-19','repository_head':summary['head'],'scope':'Byte-preserving publication checkpoint of accumulated ignored arithmetic-operator/Siegel research plus current isolated source snapshots. No new mathematical verification is implied.','source_roots':[str(r) for r in roots],'entries':entries,'readable_latest_semiprime':[],'objects':len(seen),'uncompressed_entry_bytes':sum(e['bytes'] for e in entries),'compressed_object_bytes':sum(seen.values()),'external_papers_republished':False,'compiled_artifacts_republished':False,'notes':['Old source manifests retain original bytes and historical hashes, including references to intentionally excluded oleans and primary bodies.','Excluded primary fingerprints and URL catalog preserve provenance without republishing paper bodies.','Normal tracked/publication source paths may subsequently change under the parent publication task; this archive records the exact snapshot rather than resetting historical hashes.']}
 dump('index.json',index)
 print(json.dumps({'entries':len(entries),'objects':len(seen),'compressed_bytes':sum(seen.values()),'uncompressed_entries':index['uncompressed_entry_bytes'],'leaves':len(leaves),'excluded_primaries':len(excluded),'checkpoint_mismatches':bad}))
if __name__=='__main__':main()
