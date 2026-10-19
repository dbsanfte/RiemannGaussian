#!/usr/bin/env python3
"""Verify preserved research bytes, or restore them under a separate repository root.

No source file or frozen local artifact is changed unless --destination is
explicitly provided. Existing destination files with different bytes are refused.
"""
from pathlib import Path,PurePosixPath
import argparse,fnmatch,gzip,hashlib,json

def safe_relative(value):
 p=PurePosixPath(value)
 if p.is_absolute() or '..' in p.parts:raise ValueError('Unsafe archive relative path: '+value)
 return p

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--verify',action='store_true',help='Verify all selected raw byte hashes (default without destination).')
 ap.add_argument('--destination',type=Path,help='Separate repository root under which original relative paths are restored.')
 ap.add_argument('--select',default='*',help='Glob of repository-relative paths.')
 args=ap.parse_args();root=Path(__file__).resolve().parent
 j=json.loads((root/'index.json').read_text())
 entries=[e for e in j['entries'] if fnmatch.fnmatchcase(e['repository_relative_path'],args.select)]
 if not entries:ap.error('No archived files match this selection.')
 checked={};restored=0
 for e in entries:
  h=e['sha256']
  if h not in checked:
   a=safe_relative(e['archive_path']);data=gzip.decompress((root/str(a)).read_bytes())
   if hashlib.sha256(data).hexdigest()!=h:raise ValueError('Object hash mismatch: '+str(a))
   checked[h]=data
  data=checked[h]
  if len(data)!=e['bytes']:raise ValueError('Length mismatch: '+e['repository_relative_path'])
  if args.destination is not None:
   r=safe_relative(e['repository_relative_path']);base=args.destination.resolve();target=base/str(r)
   if not target.resolve().is_relative_to(base):raise ValueError('Destination symlink escapes root: '+str(r))
   if target.exists():
    if not target.is_file() or target.read_bytes()!=data:raise ValueError('Refusing to replace different bytes: '+str(target))
   else:target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
   restored+=1
 print(json.dumps({'files_verified':len(entries),'objects_verified':len(checked),'files_restored':restored,'external_paper_bodies_included':j['external_papers_republished'],'compiled_artifacts_included':j['compiled_artifacts_republished']}))
if __name__=='__main__':main()
