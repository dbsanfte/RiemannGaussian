"""One frozen complete prime-bank study, symbolic selection and independent audit."""
import argparse
from concurrent.futures import ProcessPoolExecutor, as_completed
import json
import multiprocessing as mp
import os
from pathlib import Path
import re
import resource
import signal
import subprocess
import sys
import time

from flint import ctx
import prime_bank_candidates as P
import prime_bank_language as L
import prime_bank_measurements as M

ROOT=Path(__file__).resolve().parent
MENU=['1/2','2/3','3/4','4/5','5/6']
DISCOVERY=[1,2,4,8,64,256,1024,4096,8192,16384]
FINAL=[196608,262144]
TOTAL=1500000000
SECONDS=7200
RESERVE=1000000
TESTS=['test_prime_bank_candidates','test_check_prime_bank_candidates','test_prime_bank_workflow']
RECEIPTS=['prime_bank_producer_development.json','prime_bank_checker_development.json',
          'prime_bank_workflow_development.json']
SOURCES=['prime_bank_candidates.py','check_prime_bank_candidates.py','prime_bank_language.py',
         'prime_bank_measurements.py','run_prime_bank_search.py','prime_bank_protocol.txt',
         'candidate10_prime_bank_obligation.json','PRIME_BANK_COVARIANCE_REVIEW_001.txt',
         'OBSTRUCTION_AUXILIARY_ANALYTIC_REVIEW_001.txt','SHIFTED_QUOTIENT_CANDIDATE_10_REVIEW_001.txt']
SOURCES += [n+'.py' for n in TESTS]+RECEIPTS
FAILURES=(ValueError,ArithmeticError,OverflowError,TimeoutError,MemoryError)
_STATE=None
_BACKEND=None


def read(path):
    raw=Path(path).read_bytes()
    if len(raw)>32*1024**2: raise OverflowError('bounded artifact')
    return json.loads(raw)


def write(path,data):
    raw=(json.dumps(data,sort_keys=True,indent=2,allow_nan=False)+'\n').encode()
    if len(raw)>32*1024**2: raise OverflowError('bounded artifact')
    with Path(path).open('xb') as stream:stream.write(raw)


def checkpoint(path,data):
    with Path(path).open('a') as stream:
        stream.write(json.dumps(data,sort_keys=True,allow_nan=False)+'\n');stream.flush()


def receipts():
    result={}
    for name in RECEIPTS:
        row=read(ROOT/name)
        if (not row['runs'] or row['runs'][-1]['returncode']!=0 or
            row['operations']!=sum(r['operations'] for r in row['runs'])):
            raise ValueError('complete cumulative development receipt '+name)
        result[name]=row
    return result


def language():
    return L.catalogue(read(ROOT/'candidate10_prime_bank_obligation.json'),MENU)


def specification():
    compiled=language()
    return dict(schema='complete-prime-bank-pilot-v1',language=compiled,
                discovery_scales=DISCOVERY,discovery_horizon=65535,
                final_scales=FINAL,final_horizon=1048575,
                final_cutoffs=L.select_regimes(compiled),
                selection='critical paid regime and smallest strictly decaying paid regime; symbolic only',
                numeric_fitting=False,prior_arithmetic_overlap=True,
                work_limit=TOTAL,seconds=SECONDS,memory_bytes=16*1024**3,
                process_memory_bytes=4*1024**3,max_scalar_cells=48000000,
                processes='isolated source parent plus two fork workers; root conductor remains small',
                development=receipts(),hashes=False,
                uniform_signed_bound_proved=False,RH_proved=False)


def freeze(directory):
    directory=Path(directory).resolve();spec=specification()
    files={name:(ROOT/name).read_bytes() for name in SOURCES}
    if directory.exists():raise FileExistsError('new immutable directory required')
    directory.mkdir(parents=True);(directory/'source_snapshot').mkdir()
    for name,raw in files.items():(directory/'source_snapshot'/name).write_bytes(raw)
    write(directory/'source_files.json',SOURCES);write(directory/'protocol.json',spec)
    # Final choices are committed BEFORE any discovery arithmetic is observed.
    write(directory/'final_batch.json',dict(theta=spec['final_cutoffs'],scales=FINAL,
                                          selection=spec['selection'],numeric_fitting=False))


def verify_source(directory):
    if read(directory/'source_files.json')!=SOURCES:raise ValueError('source manifest')
    for name in SOURCES:
        if (ROOT/name).read_bytes()!=(directory/'source_snapshot'/name).read_bytes():
            raise ValueError('changed frozen source '+name)
    if specification()!=read(directory/'protocol.json'):raise ValueError('changed frozen specification')


def memory_limit():
    _,hard=resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS,(4*1024**3,hard))


def theta_worker(directory,label,theta,scales,old,cap,deadline):
    meter=P.Meter(cap=cap,seconds=max(0.001,deadline-time.monotonic()));meter.deadline=deadline
    rows=[];checked_scalars=0;reason=None;identity_points=0
    stem=label+'_theta_'+theta.replace('/','_')
    try:
        values=_BACKEND.evaluate(theta,_STATE,meter)
        identity_points=M.check_identity(values,meter)
        for index,X in enumerate(scales):
            current=M.measure(values,X,meter)
            if old is not None:
                if len(old)!=len(scales):raise ValueError('complete audit case list')
                checked_scalars+=M.compare(old[index],current,meter)
            row=M.encode(current);rows.append(row)
            checkpoint(Path(directory)/(stem+'_checkpoints.jsonl'),dict(case=row,operations=meter.operations))
        status='verified' if old is not None else 'evaluated'
    except FAILURES as error:
        status='incomplete';reason=str(error) or type(error).__name__
    result=dict(theta=theta,status=status,reason=reason,cases=rows,identity_points=identity_points,
                checked_scalars=checked_scalars,counts=meter.counts(),
                peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    write(Path(directory)/(stem+'.json'),result)
    return result


def stage(directory,label,cap,deadline):
    """Called in a fresh interpreter; source is made ONCE, then inherited readonly."""
    global _STATE,_BACKEND
    directory=Path(directory);memory_limit()
    audit=label.startswith('audit_');final=label.endswith('_final')
    H=1048575 if final else 65535;scales=FINAL if final else DISCOVERY
    theta=read(directory/'final_batch.json')['theta'] if final else MENU
    if audit:
        import check_prime_bank_candidates as checker
        _BACKEND=checker;ctx.prec=192
        original=read(directory/('producer_final.json' if final else 'producer_discovery.json'))
        if original['status']!='complete':raise ValueError('complete producer required before audit')
        saved={r['theta']:r['cases'] for r in original['records']}
        if set(saved)!=set(theta):raise ValueError('complete frozen theta set')
    else:_BACKEND=P;ctx.prec=128;saved={}
    meter=P.Meter(cap=cap,seconds=max(0.001,deadline-time.monotonic()));meter.deadline=deadline
    rows=[];reason=None;status='incomplete'
    try:
        _STATE=_BACKEND.source_state(H,meter)
        checkpoint(directory/(label+'_source_checkpoint.jsonl'),dict(H=H,counts=meter.counts(),
                    peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss))
        allowance=(cap-meter.operations)//len(theta)
        if allowance<=0:raise OverflowError('no remaining complete worker allowance')
        # Explicit fork shares the complete source, without dense state pickling.
        with ProcessPoolExecutor(max_workers=2,mp_context=mp.get_context('fork')) as pool:
            futures=[pool.submit(theta_worker,str(directory),label,t,scales,saved.get(t),allowance,deadline) for t in theta]
            for future in as_completed(futures):
                row=future.result();rows.append(row)
                print(json.dumps(dict(stage=label,theta=row['theta'],status=row['status'],
                                      operations=row['counts']['operations'])),flush=True)
        if len(rows)==len(theta) and all(r['status']==('verified' if audit else 'evaluated') for r in rows):status='complete'
    except FAILURES as error:reason=str(error) or type(error).__name__
    spent=meter.operations+sum(r['counts']['operations'] for r in rows)
    result=dict(label=label,status=status,reason=reason,horizon=H,
                source_counts=meter.counts(),records=sorted(rows,key=lambda r:theta.index(r['theta'])),
                operations=spent,cap=cap,source_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                uniform_signed_bound_proved=False,RH_proved=False)
    write(directory/(label+'.json'),result)
    if spent>cap:raise ArithmeticError('stage cap violated')


def feedback(compiled):
    # The new target is the exact signed support kernel from the analytic review.
    # It retains all diagonals, all other cross terms, the unit and the main term.
    return dict(schema='prime-bank-overlap-obligation-v1',status='open',
                source='actual_mu_candidate10',scope=dict(L.SCOPE),
                source_obligation=compiled['source_obligation']['id'],
                selected_theta=L.select_regimes(compiled),
                energy_atoms=['K','-L0','Lu','-main'],
                kernel=dict(entry='tau_theta(p)=min{n integer>=1:n^a>=p^b}, theta=a/b',
                    formula='max(0,min(2X,tau_theta(q))-max(X,h,tau_theta(Pplus(h)),q*k))',
                    coefficient='a(h)*z_b(k)*q^(-b)/X^2',
                    domain='h>=2, k>=2, q prime; all finite support terms retained',
                    exact_support='positive kernel implies q>Pplus(h), k<q, gcd(h,q)=1',
                    high_smooth_variant='replace min(2X,tau_theta(q)) by min(2X,tau_theta(q),h^2) after the sqrt(n) coefficient-prefix peel',
                    same_largest_prime_diagonal='identically zero by opposed entry conditions'),
                paid_cutoff_transport='R_new(Y2)-R_new(Y1)=J_v(Y1,Y2) at fixed x',
                paid_smooth_prefix=dict(expression='sum_{2<=h<=sqrt(n)} a(h)',
                    bound='9*sqrt(n)*(1+log(n)/2)',energy='O((1+log X)^2)',
                    next_high_smooth_support='h>sqrt(n), Pplus(h)<=n^theta',
                    outside_domain_warning='q>n^theta and h>sqrt(n) imply q*h>n; pairing must retain outside-domain compensation'),
                difference_channel=dict(identity='Delta=z_u-z_v=beta*(a_v-a_u)=-beta*(mu*(n^-u-n^-v))',
                    paid='its v bank has finite critical norm already at theta=3/4',
                    unproved='the u-weighted difference and common z0 bank still require joint source control'),
                unproved='signed joint energy across fresh dyadic coefficients; kernel support does not bound its signed sum',
                next_productions=['ordered coprime coefficient correlations','complete entry/exit kernels',
                                  'fresh-scale covariance with all smooth and bank terms',
                                  'recurrences whose forcing is a proved source correlation'],
                disallowed=['discarding the smooth remainder','separate RH-strength companion assumptions',
                            'equivalent target used as its own premise','finite energy or support identity promoted to a uniform bound'],
                analytic_provenance=L.REVIEW,equivalence_class=compiled['source_obligation']['id'],
                complete_uniform_bound_proved=False,RH_proved=False)


def run(directory):
    directory=Path(directory).resolve();verify_source(directory)
    started=time.monotonic();deadline=started+SECONDS
    write(directory/'started.json',dict(attempt=1,monotonic=started))
    testing=subprocess.run([sys.executable,'-B','-m','unittest',*TESTS],cwd=ROOT,capture_output=True,text=True,timeout=120)
    matches=re.findall(r'^SYNTHETIC_WORK module=(\w+) operations=(\d+)$',testing.stdout,re.M)
    frozen=sum(int(n) for _,n in matches)
    write(directory/'frozen_tests.json',dict(returncode=testing.returncode,stdout=testing.stdout,
                                           stderr=testing.stderr,operations=frozen))
    if testing.returncode or sorted(n for n,_ in matches)!=sorted(TESTS):raise RuntimeError('complete frozen suite required')
    preparation=sum(r['operations'] for r in receipts().values())+frozen+RESERVE
    spent=preparation;stages=[]
    for label,ceiling in (('producer_discovery',150000000),('audit_discovery',180000000),
                          ('producer_final',600000000),('audit_final',TOTAL)):
        cap=min(ceiling,TOTAL-spent)
        if cap<=0 or time.monotonic()>=deadline:break
        process=subprocess.Popen([sys.executable,'-B',str(Path(__file__).resolve()),'stage',str(directory),
                                  '--label',label,'--cap',str(cap),'--deadline',str(deadline)],cwd=ROOT,
                                 start_new_session=True)
        try:process.wait(timeout=max(1,deadline-time.monotonic()))
        except subprocess.TimeoutExpired:
            # Stop the whole fork tree; a timeout must not leave arithmetic workers running.
            os.killpg(process.pid,signal.SIGTERM)
            try:process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid,signal.SIGKILL);process.wait()
        if not (directory/(label+'.json')).exists():
            write(directory/'interrupted.json',dict(stage=label,returncode=process.returncode,
                  accounted_operations=spent,unresolved_stage_work_cap=cap,
                  instruction='retain all checkpoints; never repeat unchanged completed work'))
            return
        data=read(directory/(label+'.json'));spent+=data['operations'];stages.append(data)
        if process.returncode or data['status']!='complete':break
    verify_source(directory)
    checked=sum(len(row['cases']) for s in stages if s['label'].startswith('audit_') for row in s['records'])
    expected=len(MENU)*len(DISCOVERY)+len(read(directory/'final_batch.json')['theta'])*len(FINAL)
    verified=len(stages)==4 and all(s['status']=='complete' for s in stages) and checked==expected and spent<=TOTAL
    report=dict(status='COMPLETE_PRIME_BANK_IDENTITIES_AND_GRAMS_VERIFIED' if verified else 'INCOMPLETE',
                checked_cases=checked,expected_cases=expected,
                checked_scalars=sum(r['checked_scalars'] for s in stages for r in s['records']),
                all_horizon_identity_points=sum(r['identity_points'] for s in stages for r in s['records']),
                total_operations=spent,preparation_operations=preparation,
                stage_operations={s['label']:s['operations'] for s in stages},
                elapsed_seconds=time.monotonic()-started,final_theta=read(directory/'final_batch.json')['theta'],
                analytic_component_result='Chebyshev bound removes the log loss; critical Lv block energy is bounded',
                algebraic_component_result='exact factored transfer, cutoff cancellation, and ordered coprime support kernel',
                numerical_constant_fits=0,new_complete_uniform_bounds=0,
                uniform_signed_bound_proved=False,RH_proved=False)
    write(directory/'report.json',report)
    write(directory/'next_search_input.json',feedback(language()))
    print(json.dumps(report,sort_keys=True),flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('action',choices=['freeze','run','stage'])
    parser.add_argument('directory');parser.add_argument('--label');parser.add_argument('--cap',type=int)
    parser.add_argument('--deadline',type=float);args=parser.parse_args()
    if args.action=='stage':stage(args.directory,args.label,args.cap,args.deadline)
    else:globals()[args.action](args.directory)
