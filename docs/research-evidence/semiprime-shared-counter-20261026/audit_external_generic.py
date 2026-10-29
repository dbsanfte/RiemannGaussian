"""Audit already-built pinned algebra dependencies without restarting the build.

Invoke via the repository's `lake env python3 audit_external_generic.py`.
This uses the live build paths recorded in the previous checkpoint.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
WORK = Path('/tmp/semiprime-d1-audit-20261026')
SOURCE = WORK / 'openai-math/lean'
BUILD = WORK / 'lean-build'
LEAN = '/home/dbsanfte/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
PIN = '7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a'
ROOTS = ['OAI.Algorithms.SubexponentialSAT.' + name for name in
         ('GlobalPolynomial', 'Separation', 'SqrtLog.LayoutExactBuckets')]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    graph = json.loads((WORK/'lean-closure.json').read_text())
    state = json.loads((WORK/'lean-build-state.json').read_text())
    assert graph['head'] == state['commit'] == PIN
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=SOURCE,
                                   text=True).strip() == PIN
    seen = set()

    def visit(name):
        if name in seen or name not in graph['modules']:
            return
        seen.add(name)
        for dependency in graph['modules'][name]:
            visit(dependency)

    for name in ROOTS:
        visit(name)
    records = {}
    for name in sorted(seen):
        record = state['completed'][name]
        relative = Path(name.replace('.', '/'))
        src, obj = SOURCE/relative.with_suffix('.lean'), BUILD/relative.with_suffix('.olean')
        assert record['exit_code'] == 0
        assert sha(src) == record['source_sha256']
        assert sha(obj) == record['olean_sha256']
        records[name] = {k: record[k] for k in ('source_sha256', 'olean_sha256')}
    cache = [p for p in os.environ['LEAN_PATH'].split(':')
             if '/.lake/packages/' in p or '/.elan/toolchains/' in p]
    env = dict(os.environ, LEAN_PATH=':'.join([str(BUILD)] + cache))
    command = [LEAN, '-DautoImplicit=false', '-DwarningAsError=true',
               str(HERE/'ExternalGenericAudit.lean')]
    proc = subprocess.run(command, cwd=SOURCE, env=env, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (HERE/'external-generic-audit.log').write_text(proc.stdout)
    assert proc.returncode == 0, proc.stdout
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", proc.stdout)
    assert len(reports) == 6, proc.stdout
    permitted = {'propext', 'Classical.choice', 'Quot.sound'}
    axioms = {}
    for theorem, names in reports:
        used = {x.strip() for x in names.split(',') if x.strip()}
        assert used <= permitted, (theorem, used)
        axioms[theorem] = sorted(used)
    result = dict(status='PASS', source_commit=PIN, external_baseline=True,
                  scope='six reusable algebra theorems; not complete counter or SAT endpoint',
                  built_dependency_modules=len(seen), dependency_hashes=records,
                  theorem_axioms=axioms, full_endpoint_verified=False,
                  proof_license='Apache-2.0; see prior pinned-source provenance')
    (HERE/'external-generic-audit.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()
                      if k not in ('dependency_hashes', 'theorem_axioms')}))


if __name__ == '__main__':
    main()
