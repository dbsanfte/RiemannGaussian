#!/usr/bin/env python3
"""Run a leaf with the pinned original SAT objects and ordinary repo imports.

No published source/object is written. This explicit opt-in environment must
never import OpenAISemiprime, which exports overlapping SAT constant names.
"""
from pathlib import Path
import os,subprocess,sys
ROOT=Path('/home/dbsanfte/riemann/formal')
WORK=Path('/tmp/semiprime-ternary-machine-20261027')
UPSTREAM=Path('/tmp/semiprime-d1-audit-20261026/lean-build')
QUASI=ROOT/'vendor/openai-quasi-rh/.lake/build/lib/lean'
overlay=WORK/'original-imports'
(overlay/'OAI').mkdir(parents=True,exist_ok=True)
for name,target in [('Algorithms',UPSTREAM/'OAI/Algorithms'),('NumberTheory',QUASI/'OAI/NumberTheory')]:
 dest=overlay/'OAI'/name
 if dest.is_symlink():assert dest.resolve()==target.resolve()
 else:
  assert not dest.exists(),dest
  dest.symlink_to(target,target_is_directory=True)
env=dict(os.environ)
if 'LEAN_PATH' not in env:
 env['LEAN_PATH']=subprocess.check_output(['/home/dbsanfte/.elan/bin/lake','env','printenv','LEAN_PATH'],cwd=ROOT,text=True).strip()
env['LEAN_PATH']=str(overlay)+':'+env['LEAN_PATH']
lean='/home/dbsanfte/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
raise SystemExit(subprocess.run([lean,'-DautoImplicit=false','-DwarningAsError=true',*sys.argv[1:]],cwd=ROOT,env=env).returncode)
