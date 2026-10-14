"""Append a certified rejection rule to a completed, unchanged bound search."""
from collections import Counter
import gzip
import json
from pathlib import Path
import resource
import sys
import time

import core_pole_growth_obstruction as P
from prime_bank_candidates import Meter

ROOT=Path(__file__).resolve().parent
PILOT=ROOT/'core-bound-results/pilot-001'
SOURCE_PARENT=ROOT/'joint-preconditioner-results/pilot-001'
CAP=50000000
SECONDS=600
SOURCES=['core_pole_growth_obstruction.py','run_core_pole_feedback.py',
         'test_core_pole_growth_obstruction.py','core_pole_growth_development.json',
         'CORE_BOUND_POLE_ORDER_REVIEW_006.txt','CORE_BOUND_CANDIDATE_REVIEW_006.txt',
         'prime_bank_candidates.py']


def read(path):return json.loads(Path(path).read_text())


def write(path,data):
    with Path(path).open('x') as f:
        json.dump(data,f,sort_keys=True,indent=2);f.write('\n')


def verify_parent():
    report=read(PILOT/'report.json')
    if report['status']!='AUTOMATIC_CORE_BOUND_SEARCH_AND_INDEPENDENT_EVALUATION_COMPLETE':
        raise ValueError('completed independently checked experiment required')
    for name in read(PILOT/'source_files.json'):
        if (ROOT/name).read_bytes()!=(PILOT/'source_snapshot'/name).read_bytes():
            raise ValueError('changed frozen source '+name)
    if read(PILOT/'frozen_tests.json')['returncode']:
        raise ValueError('passed parent checks')
    return report


def freeze(directory):
    directory=Path(directory).resolve();parent=verify_parent()
    receipt=read(ROOT/'core_pole_growth_development.json')
    if any(r['returncode'] for r in receipt['runs']):raise ValueError('passed owned checks')
    if directory.exists():raise FileExistsError('new postanalysis only')
    directory.mkdir();(directory/'source_snapshot').mkdir()
    for name in SOURCES:(directory/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
    write(directory/'source_files.json',SOURCES)
    write(directory/'protocol.json',dict(schema='core-pole-feedback-v1',parent_report=parent,
        centre=list(P.CENTRE),radius=P.RADIUS,witnesses=[dict(bits=256,method='rouche'),dict(bits=320,method='newton_contraction')],
        source='unique dominant integral exponent of the exact complete source AST',
        filters='all13 generated delay multipliers and the proved log-Abel leading-pole identity',
        operations_limit=CAP,seconds_limit=SECONDS,metadata_reserve=1000000,
        development=receipt,source_rerun=False,reselection=False,refitting=False,hashes=False,
        whole_signed_bound_proved=False,RH_proved=False))
    (directory/'parent_selection.json').write_bytes((SOURCE_PARENT/'selection.json').read_bytes())


def verify(directory):
    verify_parent()
    if read(directory/'source_files.json')!=SOURCES:raise ValueError('source manifest')
    for name in SOURCES:
        if (ROOT/name).read_bytes()!=(directory/'source_snapshot'/name).read_bytes():
            raise ValueError('changed feedback source '+name)
    if (directory/'parent_selection.json').read_bytes()!=(SOURCE_PARENT/'selection.json').read_bytes():
        raise ValueError('unchanged exact complete source AST')


def run(directory):
    directory=Path(directory).resolve();verify(directory)
    _,hard=resource.getrlimit(resource.RLIMIT_AS);resource.setrlimit(resource.RLIMIT_AS,(4*1024**3,hard))
    start=time.monotonic();write(directory/'started.json',dict(attempt=1))
    m=Meter(CAP,SECONDS);m.charge(1000000)
    protocol=read(directory/'protocol.json')
    certs=[]
    for spec in protocol['witnesses']:
        cert=P.certify_local_zero(spec['bits'],spec['method'],m)
        certs.append(cert);write(directory/(spec['method']+'_witness.json'),cert)
        print(json.dumps(dict(stage='local_zero_witness',method=spec['method'],margin=cert['margin'],operations=m.operations)),flush=True)
    source=read(directory/'parent_selection.json')['selected']
    constants=read(PILOT/'producer_cases.json')
    from flint import arb
    coeffs={'beta':'9/2','-beta':'-9/2','-R_u':str(-arb(constants['R_u']))}
    witness=P.make_witness(source['terms'],coeffs,*certs)
    write(directory/'pole_witness.json',witness)
    programs={p['id']:p for p in read(PILOT/'programs.json')}
    totals=Counter();transitions=Counter();rejected=0;count=0
    with gzip.open(PILOT/'hypotheses.jsonl.gz','rt') as old, gzip.open(directory/'hypothesis_feedback.jsonl.gz','xt',compresslevel=1) as new:
        for line in old:
            r=json.loads(line);p=programs[r['program_id']]['program']
            updated=P.annotate(r,p,witness);decision=updated['critical_pole_gate']
            totals[updated['status']]+=1;transitions[(r['status'],updated['status'])]+=1
            rejected+=int(decision['uniform_shape_disproved']);count+=1;m.charge(200)
            json.dump(dict(program_id=r['program_id'],rho=r['rho'],gamma=r['gamma'],log_power=r['log_power'],
                           prior_status=r['status'],status=updated['status'],cofinal_candidate=updated['cofinal_candidate'],
                           critical_pole_gate=decision),new);new.write('\n')
    selection=read(PILOT/'selection.json')['selected']
    final={r['program_id']:r for r in read(PILOT/'final_bounds.json')}
    decisions=[]
    for r in selection:
        out=P.annotate(r,r['program'],witness)
        decisions.append(dict(program_id=r['program_id'],lane=r['lane'],program=r['program'],
                              rho=r['rho'],gamma=r['gamma'],log_power=r['log_power'],constant=r['constant'],
                              critical_pole_gate=out['critical_pole_gate'],status=out['status'],
                              original_final_score=final[r['program_id']]['final_score']))
        m.charge(1000)
    write(directory/'selected_feedback.json',decisions)
    minimum=witness['source_pole']['minimum_dyadic_energy_log_degree']
    next_input=dict(schema='pole-admitted-core-bound-obligations-v1',status='open',
        prior_input='candidate10_joint_preconditioner_obligation.json',
        target=read(PILOT/'next_search_input.json')['target'],
        completed_search='core-bound-results/pilot-001/report.json',
        witness='core-bound-results/pilot-001/pole-feedback-001/pole_witness.json',
        search_language='core_bound_synthesis.py',preselection_gate='core_pole_growth_obstruction.gate',
        required_execution_order=['generate expression and recurrence shapes','apply certified pole and recovery gates',
                                  'evaluate/rank admitted conjectures','freeze choices and constants','evaluate genuinely fresh scales','attempt proof'],
        pole_constraint=dict(source_pole_order=witness['source_pole']['order'],minimum_log_degree=minimum,
            rho_below_one_minimum_forcing_log_power=minimum,rho_equal_one_minimum_forcing_log_power=minimum-1,
            certified_filters=witness['surviving_filters'],scope='gamma=0; nonnegative auxiliary storage dominating E_G'),
        allowed_unproved_examples=[dict(rho='1',gamma='0',log_power=1),dict(rho='1/2',gamma='0',log_power=2)],
        grammar_extension='include forcing log power2 for strict contractions; retain rho1/logpower1 and fractional weights',
        rejected_selected_obligations=[dict(program_id=r['program_id'],status=r['status']) for r in decisions],
        next_priority='generate signed recurrence/auxiliary proofs obeying the necessary pole degree; fixed finite fits do not discharge the all-scale increment',
        fresh_data_policy='all prefixes through262143 and all final scores are now observed; a subsequent final test needs a new declared range',
        proof_rules_available=['nonnegative square domination','conditional dyadic induction','bounded/polylog recovery',
                               'uniform weak absolute reference','retained critical pole minimum-log-degree rejection'],
        sharper_log_abel_recovery='same block log degree, with explicit finite head and bounded floor discrepancy; review006',
        all_scale_signed_control_proved=False,whole_signed_bound_proved=False,RH_proved=False)
    write(directory/'next_search_input.json',next_input)
    development=protocol['development']['operations']
    report=dict(status='CERTIFIED_POLE_GROWTH_FEEDBACK_COMPLETE',hypotheses_annotated=count,
                uniform_shapes_disproved=rejected,postanalysis_status_counts=dict(totals),
                transitions=[dict(before=a,after=b,count=n) for (a,b),n in sorted(transitions.items())],
                selected_bounds=len(decisions),selected_all_scale_premises_disproved=sum(r['critical_pole_gate']['uniform_shape_disproved'] for r in decisions),
                selected_finite_final_passes=sum(r['original_final_score']['failed']==0 for r in decisions),
                certified_simple_critical_zero=True,shifted_numerator_nonzero=True,
                whole_disk_delay_nonvanishing_count=13,source_pole_order=witness['source_pole']['order'],minimum_log_degree=minimum,
                new_arithmetic_source_evaluations=0,refitting=False,reselection=False,
                operations=m.operations,development_operations=development,total_feedback_operations=m.operations+development,
                total_with_parent_operations=protocol['parent_report']['total_operations']+m.operations+development,
                elapsed_seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                all_scale_signed_control_proved=False,whole_signed_bound_proved=False,RH_proved=False)
    if report['total_feedback_operations']>CAP:raise OverflowError('inclusive work cap')
    verify(directory);write(directory/'report.json',report)
    print(json.dumps(report),flush=True)


if __name__=='__main__':
    action,directory=sys.argv[1:]
    if action not in ('freeze','run'):raise ValueError('freeze or run')
    globals()[action](directory)
