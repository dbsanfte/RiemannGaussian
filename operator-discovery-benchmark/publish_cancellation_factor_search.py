"""Publish the factor obstruction, computational retries and signed projection calibration."""
import hashlib
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parent


def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,v):
    with p.open('x') as f:json.dump(v,f,sort_keys=True,indent=2,allow_nan=False);f.write('\n')


def publish():
    base=ROOT/'cancellation-arithmetic-results';old=base/'publication-002'
    factor=base/'pilot-001/factor-probe-001';native=factor/'native-dual-001';lp=factor/'lp-retry-001'
    gcd=base/'gcd-projection-calibration-001';out=base/'publication-003'
    if out.exists():raise FileExistsError('new publication required')
    for n,h in read(old/'manifest.json')['files'].items():
        if sha(ROOT/n)!=h:raise ValueError('previous publication changed: '+n)
    verified={}
    for name,d in [('factor',factor),('native',native),('lp',lp),('gcd',gcd)]:
        v=read(d/'independent_verification.json')
        if v['all_passed'] is not True:raise ValueError('independent audit required: '+name)
        verified[name]=v
        for n,h in v.get('input_sha256',{}).items():
            path=d/(n if n.endswith('.json') else n+'.json')
            if sha(path)!=h:raise ValueError('audit binding changed: '+name+'/'+n)
    uniform=read(native/'uniform_scope_independent_review.json')
    if not uniform['all_passed'] or uniform['constant_coordinates']!=['0']*5 or uniform['lhs_dot_y']!='-1':
        raise ValueError('uniform cone scope verification')
    for n,h in uniform['input_sha256'].items():
        # Scope review records workspace-relative inputs.
        p=ROOT/n
        if not p.is_file():p=native/(n if n.endswith('.json') else n+'.json')
        if sha(p)!=h:raise ValueError('uniform input binding changed: '+n)
    for n,h in uniform['source_sha256'].items():
        if sha(ROOT/n)!=h:raise ValueError('uniform source changed: '+n)
    for d in [factor,native,lp]:
        for n,h in read(d/'source_seal.json')['hashes'].items():
            if sha(ROOT/n)!=h or sha(d/'frozen_source'/n)!=h:raise ValueError('frozen source changed: '+n)
    for n,h in read(gcd/'manifest.json')['files'].items():
        if sha(gcd/n)!=h:raise ValueError('gcd archive changed')
    root_gcd=read(gcd/'root_verification.json')
    if not root_gcd['all_passed'] or root_gcd['manifest_sha256']!=sha(gcd/'manifest.json'):raise ValueError('gcd root audit')
    native_result=read(native/'result.json')['dual']
    lp_training=read(lp/'training.json')['attempts'];lp_final=read(lp/'final.json')['results']
    if native_result['status']!='exact_separator' or not native_result['certified']:raise ValueError('exact obstruction required')
    out.mkdir()
    report=dict(schema=3,previous_publication='publication-002',prior_manifest_sha256=sha(old/'manifest.json'),
        factor=dict(templates=44,groups=dict(squares=282,relations=319),
            original_training_statuses=verified['factor']['training_statuses'],original_dual_status=verified['factor']['dual_status'],
            original_failures_preserved=True,source_scale='N=4X-1',normalization='degree-one kernels divided by N'),
        exact_obstruction=dict(status='exact_separator',independently_verified=True,
            support_replayed=420,new_float_proposal=False,
            native_reconstruction_elapsed_seconds=native_result['diagnostics']['elapsed_seconds'],
            scope=uniform['uniform_claim'],gate_necessity_scope=uniform['gate_necessity_scope'],actual_arithmetic_refutation=False),
        sparse_lp_retry=dict(grams_fixed_zero=True,
            training_statuses=[a['synthesis']['status'] for a in lp_training],
            final_statuses=[[o['status'] for o in f['observations']] for f in lp_final],
            finite_critical_certificate_found=any(a['program']['claim']=='critical' and a['synthesis']['status']=='finite_certificate' for a in lp_training)),
        signed_gcd_projection=dict(supplied_identity_calibration=True,tests=6,fixtures=6,
            signed_weights_retained=True,is_PSD_bound=False,actual_signed_values_substituted=False),
        next_action='search complete inverse-row/gcd pair multipliers and signed divisor-energy interactions; prove any accepted full template uniformly',
        global_bound_proved=False,RH_proved=False)
    write(out/'report.json',report)
    names=['publish_cancellation_factor_search.py','CANCELLATION_FACTOR_SEARCH_HANDOFF.txt',
           'cancellation_factor_closure_scope.txt','cancellation_factor_contrast_normalforms.txt',
           'cancellation_coprime_box_scope.txt','cancellation_factor_cone_uniform_independent_review.txt',
           'cancellation_factor_search_independent_builder_review.txt',
           'cancellation_factor_solver_remedy_scope.txt','cancellation_factor_unsigned_embedding_audit.json',
           'cancellation_factor_lp_unsigned_adjudication.txt','cancellation_factor_lp_unsigned_adjudication.json']
    files={ROOT/n for n in names};files.update([old/'manifest.json',old/'report.json',out/'report.json'])
    for d in [factor,gcd]:files.update(p for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts)
    for d in [factor,native,lp]:files.update(ROOT/n for n in read(d/'source_seal.json')['hashes'])
    files.update(ROOT/n for n in read(gcd/'spec.json')['code'])
    manifest=dict(schema=1,files={str(p.relative_to(ROOT)):sha(p) for p in sorted(files)},global_bound_proved=False,RH_proved=False)
    write(out/'manifest.json',manifest)
    for n,h in manifest['files'].items():
        if sha(ROOT/n)!=h:raise ValueError('publication end hash changed')
    pointer=dict(publication='publication-003',report_sha256=sha(out/'report.json'),manifest_sha256=sha(out/'manifest.json'),global_bound_proved=False,RH_proved=False)
    temp=base/'latest-003.tmp';write(temp,pointer);temp.replace(base/'latest.json')
    print(json.dumps(dict(publication='publication-003',bound_files=len(manifest['files']),global_bound_proved=False,RH_proved=False)))


if __name__=='__main__':publish()
