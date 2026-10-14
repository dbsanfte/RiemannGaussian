"""One frozen post-analysis of cofinal filters; no repeated candidate search."""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import re
import resource
import subprocess
import sys
import time

import prime_slide_discovery as P
import prime_slide_recovery as R
import run_prime_slide_discovery as D

ROOT=Path(__file__).resolve().parent
PARENT=ROOT/'prime-slide-results/pilot-001'
RECEIPT='prime_slide_recovery_development.json'
FILES=['prime_slide_recovery.py','run_prime_slide_recovery.py','test_prime_slide_recovery.py',RECEIPT,
       'prime_slide_discovery.py','check_prime_slide_discovery.py','run_prime_slide_discovery.py',
       'PRIME_SLIDE_RECOVERY_REVIEW_001.txt','CENTERED_COMMON_BANK_CLOSURE_REVIEW_001.txt',
       'PRIME_TRANSFER_MARTINGALE_REVIEW_001.txt','ORDERED_PRIME_PAIRING_REVIEW_001.txt']


def read(path):return json.loads(Path(path).read_text())
def write(path,data):
    with Path(path).open('x') as f:json.dump(data,f,indent=2,sort_keys=True);f.write('\n')


def development():
    receipt=read(ROOT/RECEIPT)
    if (not receipt['runs'] or receipt['runs'][-1]['returncode'] or
        receipt['operations']!=sum(r['operations'] for r in receipt['runs'])):
        raise ValueError('passed cumulative development receipt')
    return receipt


def parent_rows():
    D.verify_source(PARENT);report=read(PARENT/'report.json')
    if report['status']!='PRIME_ADJUNCTION_AUXILIARIES_INDEPENDENTLY_VERIFIED':raise ValueError('verified parent study')
    rows=[];count=0
    with (PARENT/'candidates.jsonl').open() as stream:
        for line in stream:
            row=json.loads(line);count+=1
            if row['auxiliary_cofinal_bound_proved']:rows.append(row)
    if count!=report['candidates'] or len(rows)!=report['cofinal_auxiliary_words']:raise ValueError('complete cofinal extraction')
    selected=[r for r in rows if r['id'] in report['selected_ids'] and r['baseline_coefficient']]
    if not selected:raise ValueError('selected cofinal baseline filter')
    target=min(selected,key=lambda r:(Q(r['bound']['energy_power']),r['term_count'],r['coefficient_l1'],r['id']))
    return report,rows,target['id']


def freeze(directory):
    directory=Path(directory).resolve();report,rows,target=parent_rows();dev=development()
    files={name:(ROOT/name).read_bytes() for name in FILES}
    if directory.exists():raise FileExistsError('fresh post-analysis directory')
    directory.mkdir(parents=True);(directory/'source_snapshot').mkdir()
    for name,raw in files.items():(directory/'source_snapshot'/name).write_bytes(raw)
    write(directory/'source_files.json',FILES);write(directory/'parent_report.json',report)
    write(directory/'parent_cofinal.json',rows)
    write(directory/'parent_obligation.json',read(PARENT/'next_search_input.json'))
    write(directory/'protocol.json',dict(schema='prime-slide-recovery-postanalysis-v1',
        parent=str(PARENT.relative_to(ROOT)),selected_candidate_id=target,
        purpose='exact recurrence reduction, complete support pullback and scoped local recovery obstruction',
        frozen_search_not_repeated=True,new_actual_source_evaluations=0,development=dev,
        work_limit=1000000,combined_work_limit=150000000,metadata_reserve=100000,
        seconds=120,memory_bytes=4*1024**3,hashes=False,
        reviewed_analytical_inputs=['local recurrence valid at every prime power',
            'complete kernel pullback domains','bounded local recovery obstruction',
            'joint centering and conditional smaller-scale rule'],
        proof_text_is_not_formally_checked=True,whole_signed_bound_proved=False,RH_proved=False))


def verify(directory):
    if read(directory/'source_files.json')!=FILES:raise ValueError('post-analysis manifest')
    for name in FILES:
        if (ROOT/name).read_bytes()!=(directory/'source_snapshot'/name).read_bytes():raise ValueError('changed frozen '+name)
    report,rows,target=parent_rows()
    if report!=read(directory/'parent_report.json') or rows!=read(directory/'parent_cofinal.json'):
        raise ValueError('changed exact parent records')
    if read(PARENT/'next_search_input.json')!=read(directory/'parent_obligation.json'):
        raise ValueError('changed recovery parent')
    protocol=read(directory/'protocol.json')
    if protocol['development']!=development() or protocol['selected_candidate_id']!=target:
        raise ValueError('changed development or selected target')


def run(directory):
    directory=Path(directory).resolve();verify(directory);start=time.monotonic()
    _,hard=resource.getrlimit(resource.RLIMIT_AS);resource.setrlimit(resource.RLIMIT_AS,(4*1024**3,hard))
    write(directory/'started.json',dict(attempt=1,monotonic=start))
    protocol=read(directory/'protocol.json');parent=read(directory/'parent_report.json')
    test=subprocess.run([sys.executable,'-B','-m','unittest','test_prime_slide_recovery'],
                        cwd=ROOT,capture_output=True,text=True,timeout=30)
    work=re.findall(r'^SYNTHETIC_WORK module=test_prime_slide_recovery operations=(\d+)$',test.stdout,re.M)
    frozen=sum(int(n) for n in work)
    write(directory/'frozen_tests.json',dict(returncode=test.returncode,stdout=test.stdout,stderr=test.stderr,operations=frozen))
    if test.returncode or len(work)!=1:raise RuntimeError('passed complete frozen recovery suite')
    preparation=protocol['metadata_reserve']+development()['operations']+frozen
    cap=min(protocol['work_limit'],protocol['combined_work_limit']-parent['total_operations'])-preparation
    meter=P.Meter(cap,protocol['seconds']);meter.deadline=start+protocol['seconds']
    rows=read(directory/'parent_cofinal.json')
    analyses=[R.analyse_row(row,meter) for row in rows]
    obstruction=R.bounded_local_recovery_obstruction(rows,meter)
    output=R.feedback(read(directory/'parent_obligation.json'),analyses,obstruction,protocol['selected_candidate_id'])
    output['centering_feedback']=dict(
        analytic_provenance='CENTERED_COMMON_BANK_CLOSURE_REVIEW_001.txt',
        proof_status='reviewed analytical input; proof text is not formally checked',
        theta='3/4',prime_parameter='t=q^(-1/3)',
        state=['J','M_u','M_v'],goal_relation='sufficient coupled route; equivalence to the original target is not asserted',
        prime_domain='q prime, n^theta<q<=n/2; m=floor(n/q)>=2',
        unit_prime_strip='q prime, max(n^theta,n/2)<q<=n',
        transfer_matrix=[
            [[[0,'-2'],[1,'1'],[2,'1']],[[0,'-9/2'],[2,'9/2']],[[0,'-9/2'],[1,'9/2']]],
            [[],[[0,'-1'],[1,'1']],[]],
            [[],[],[[0,'-1'],[2,'1']]]],
        exact_identity='F(n)=H(n)+sum_q A_q*F(floor(n/q))',
        smooth_compensator=[
            'H_J=K+D-m_u*n^(2/3)-m_v*n^(1/3)+sum_q[-C0(m)+t*Cu(m)+t^2*Cv(m)]',
            'H_u=K_u-c_u*n^(2/3)+sum_q[(t-1)*c_u*m^(2/3)]+sum_unit_strip(t-1)',
            'H_v=K_v-c_v*n^(1/3)+sum_q[(t^2-1)*c_v*m^(1/3)]+sum_unit_strip(t^2-1)'],
        shared_prime_rule=dict(storage='identity matrix on the three states',matrix_norm_squared_upper='93/2',
            premise='same simultaneous cumulative induction sum_{m<=T}||F(m)||^2<=A_epsilon*T^(2+epsilon)',
            bound='(93/2)*2^(2+epsilon)*(1+1/epsilon)*A_epsilon*X^(epsilon/4)',
            horizon='T<=2*X^(1/4)',premise_established=False),
        remaining_joint_forcing='X^-2*sum_n[||H||^2+2*sum_q H^T*A_q*F(m_q)+sum_{q!=r}F(m_q)^T*A_q^T*A_r*F(m_r)]',
        isolated_payment_excluded=dict(expression='P_theta=m_u*n^(2/3)+sum_q[C0(m)-t*Cu(m)]',
            conclusion='P_theta alone has no cofinal critical-energy bound',
            reason='nonzero deterministic profile has a prime-zeta logarithmic Mellin singularity at s=1',
            scope='standalone pole compensation only; joint cancellation with K and centered banks remains open'),
        whole_signed_bound_proved=False,RH_proved=False)
    verify(directory)
    report=dict(status='EXACT_RECOVERY_REDUCTIONS_VERIFIED',checked_candidates=len(rows),
        selected_candidate_id=protocol['selected_candidate_id'],
        all_reduce_to_weighted_first_prime_actions=True,
        local_recovery_obstruction=obstruction,
        work_operations=meter.operations,preparation_operations=preparation,
        total_operations=preparation+meter.operations,
        combined_operations=parent['total_operations']+preparation+meter.operations,
        elapsed_seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        new_actual_source_evaluations=0,original_target_recovered=False,whole_signed_bound_proved=False,RH_proved=False)
    write(directory/'reductions.json',analyses);write(directory/'next_search_input.json',output)
    write(directory/'report.json',report);print(json.dumps(report),flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('action',choices=['freeze','run']);parser.add_argument('directory')
    args=parser.parse_args();globals()[args.action](args.directory)
