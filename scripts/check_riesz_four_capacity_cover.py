#!/usr/bin/env python3
"""Optional kernel checks of generated Riesz capacity chunks and assembly.

No proof result is inferred from the manifest. Each claimed theorem is
elaborated and checked by Lean. This command is intentionally outside CI.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import threading
import time


ROOT=Path(__file__).resolve().parents[1]


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--directory',type=Path,default=Path('.lake/riesz-four-capacity-cover'))
    p.add_argument('--jobs',type=int,default=2)
    p.add_argument('--lake',default='lake')
    args=p.parse_args()
    assert 1<=args.jobs<=4
    directory=args.directory.resolve()
    manifest=json.loads((directory/'manifest.json').read_text())
    env=os.environ.copy()
    lean_path=subprocess.check_output([args.lake,'env','printenv','LEAN_PATH'],cwd=ROOT,env=env,text=True).strip()
    env['LEAN_PATH']=str(directory)+os.pathsep+lean_path
    lean=subprocess.check_output([args.lake,'env','which','lean'],cwd=ROOT,env=env,text=True).strip()
    logs=directory/'checks'
    logs.mkdir(exist_ok=True)
    # A failed or interrupted rerun must not leave a previous assembly
    # verdict looking current.
    (logs/'assembly.json').unlink(missing_ok=True)
    (logs/'progress.json').write_text(json.dumps({'status':'running',
        'complete':0,'total':len(manifest['chunks']),'results':[]},indent=2)+'\n')
    for name,expected in manifest['source_sha256'].items():
        candidates=[ROOT/'scripts'/name,ROOT/'RiemannGaussian'/name]
        source=next((p for p in candidates if p.is_file()),None)
        if source is None or hashlib.sha256(source.read_bytes()).hexdigest()!=expected:
            raise SystemExit(f'Changed or missing generator/proof input: {name}; regenerate first.')
    interrupted=threading.Event()
    children={}
    child_lock=threading.Lock()

    def stop(signum,frame):
        interrupted.set()
        with child_lock:
            for child in children.values():
                try:
                    os.killpg(child.pid,signal.SIGTERM)
                except ProcessLookupError:
                    pass

    signal.signal(signal.SIGTERM,stop)
    signal.signal(signal.SIGINT,stop)

    def check(entry):
        source=directory/entry['file']
        assert hashlib.sha256(source.read_bytes()).hexdigest()==entry['sha256'],source
        start=time.monotonic()
        with (logs/(source.stem+'.log')).open('w') as out:
            with child_lock:
                if interrupted.is_set():
                    return {'file':entry['file'],'exit_code':125,'seconds':0,'interrupted':True}
                child=subprocess.Popen([lean,'-DwarningAsError=true','--root='+str(directory),
                                        '-o',str(source.with_suffix('.olean')),str(source)],
                                       cwd=ROOT,env=env,stdout=out,stderr=subprocess.STDOUT,
                                       start_new_session=True)
                children[child.pid]=child
            code=child.wait()
            with child_lock:
                children.pop(child.pid,None)
        return {'file':entry['file'],'exit_code':code,
                'seconds':round(time.monotonic()-start,2)}

    results=[]
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        jobs={pool.submit(check,entry):entry for entry in manifest['chunks']}
        for job in as_completed(jobs):
            result=job.result()
            results.append(result)
            (logs/'progress.json').write_text(json.dumps({'status':
                'interrupted' if interrupted.is_set() else 'checking', 'complete':len(results),
                'total':len(jobs),'results':results},indent=2)+'\n')
            print(json.dumps({'complete':len(results),'total':len(jobs),**result}),flush=True)
            if result['exit_code']:
                for pending in jobs:
                    pending.cancel()
                break
    if interrupted.is_set() or len(results)!=len(manifest['chunks']) or any(r['exit_code'] for r in results):
        (logs/'progress.json').write_text(json.dumps({'status':
            'interrupted' if interrupted.is_set() else 'failed',
            'complete':len(results),'total':len(manifest['chunks']),'results':results},indent=2)+'\n')
        raise SystemExit('Some chunks failed; assembly has not been checked.')
    result=check(manifest['assembly'])
    (logs/'assembly.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'assembly':result}),flush=True)
    if interrupted.is_set() or result['exit_code']:
        raise SystemExit('Assembly failed.')
    (logs/'progress.json').write_text(json.dumps({'status':'all_chunks_and_assembly_passed',
        'complete':len(results),'total':len(manifest['chunks']),'results':results},indent=2)+'\n')


if __name__=='__main__':
    main()
