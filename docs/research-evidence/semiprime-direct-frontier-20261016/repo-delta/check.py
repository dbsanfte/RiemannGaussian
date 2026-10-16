#!/usr/bin/env python3
"""Offline, standard-library-only saved official GitHub delta verification."""
from pathlib import Path
import gzip,hashlib,json
p=Path(__file__).resolve().parent
cert=json.loads((p/'certificate.json').read_text())
for f,pin in cert['files'].items():
 b=(p/f).read_bytes();assert len(b)==pin['bytes'] and hashlib.sha256(b).hexdigest()==pin['sha256'],f

def tree(name):
 raw=gzip.decompress((p/(name+'-preprints-tree.json.gz')).read_bytes());d=json.loads(raw)
 assert not d.get('truncated')
 assert d['sha']==cert['preprint_roots'][name]
 assert hashlib.sha256(raw).hexdigest()==cert['plain_tree_hashes'][name]
 entries={x['path']:x for x in d['tree']}
 byparent={}
 for x,e in entries.items():byparent.setdefault(x.rpartition('/')[0],[]).append((x.rsplit('/',1)[-1],e))
 # Verify Git tree objects bottom-up, including all directory entries.
 dirs=['']+[x for x,e in entries.items() if e['type']=='tree']
 for folder in sorted(dirs,key=lambda x:x.count('/')+(bool(x)),reverse=True):
  children=byparent.get(folder,[])
  children.sort(key=lambda z:(z[0]+('/' if z[1]['type']=='tree' else '')).encode())
  payload=b''.join(e['mode'].lstrip('0').encode()+b' '+n.encode()+b'\0'+bytes.fromhex(e['sha']) for n,e in children)
  sha=hashlib.sha1(b'tree '+str(len(payload)).encode()+b'\0'+payload).hexdigest()
  assert sha==(d['sha'] if not folder else entries[folder]['sha']),folder
 return {x:e['sha'] for x,e in entries.items() if e['type']=='blob'}
a,b=tree('base'),tree('head')
for version in ['base','head']:
 root=json.loads((p/(version+'-root.json')).read_text())
 assert json.loads((p/(version+'-commit.json')).read_text())['sha']==cert[version]
 lean=json.loads((p/(version+'-lean-root.json')).read_text())
 oai=json.loads((p/(version+'-oai-root.json')).read_text())
 for doc in [root,lean,oai]:
  children=sorted(doc['tree'],key=lambda e:(e['path']+('/' if e['type']=='tree' else '')).encode())
  payload=b''.join(e['mode'].lstrip('0').encode()+b' '+e['path'].encode()+b'\0'+bytes.fromhex(e['sha']) for e in children)
  expected=(json.loads((p/(version+'-commit.json')).read_text())['tree']['sha'] if doc is root else doc['sha'])
  assert hashlib.sha1(b'tree '+str(len(payload)).encode()+b'\0'+payload).hexdigest()==expected
 assert root['sha']==cert['repository_roots'][version]
 rm={e['path']:e['sha'] for e in root['tree']};lm={e['path']:e['sha'] for e in lean['tree']}
 assert rm['preprints']==cert['preprint_roots'][version]
 assert rm['lean']==lean['sha'] and lm['OAI']==oai['sha']
for group,mapping in cert['unchanged_families'].items():
 aa={x:s for x,s in a.items() if x.startswith(group)};bb={x:s for x,s in b.items() if x.startswith(group)}
 assert aa==bb==mapping,group
ar={x['path']:x['sha'] for x in json.loads((p/'base-oai-root.json').read_text())['tree']}
br={x['path']:x['sha'] for x in json.loads((p/'head-oai-root.json').read_text())['tree']}
for x,sha in cert['unchanged_oai_subtrees'].items():assert ar[x]==br[x]==sha
def git_blob(raw):
 return hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
headroot={e['path']:e['sha'] for e in json.loads((p/'head-root.json').read_text())['tree']}
assert git_blob((p/'history.md').read_bytes())==headroot['history.md']
assert '300 / 719' in (p/'history.md').read_text()
parent=br['Computability']
for filename,child in [('head-computability-root.json','Logspace'),('head-logspace-root.json',None)]:
 doc=json.loads((p/filename).read_text());assert not doc.get('truncated')
 children=sorted(doc['tree'],key=lambda e:(e['path']+('/' if e['type']=='tree' else '')).encode())
 payload=b''.join(e['mode'].lstrip('0').encode()+b' '+e['path'].encode()+b'\0'+bytes.fromhex(e['sha']) for e in children)
 assert hashlib.sha1(b'tree '+str(len(payload)).encode()+b'\0'+payload).hexdigest()==doc['sha']==parent
 mapping={e['path']:e['sha'] for e in children}
 if child:parent=mapping[child]
 else:
  for filename in ['Equality.lean','Deterministic.lean']:
   assert git_blob((p/filename).read_bytes())==mapping[filename]
added={x for x in b if x not in a}
removed={x for x in a if x not in b}
modified={x for x in a.keys()&b.keys() if a[x]!=b[x]}
assert (len(added),len(removed),len(modified))==(381,31,6)
assert len({x.split('/')[0] for x in added|removed|modified})==30
print('PASS: complete preprint Git Merkle trees; 62 unchanged relevant blobs; 4 unchanged OAI subtrees; 381 added/6 modified/31 removed preprint files in 30 folders; linked history and 2 logspace sources. Internal consistency only; no build or theorem certification.')
