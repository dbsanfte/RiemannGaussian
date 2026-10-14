"""Admit scoped adversarial certificates without another source experiment."""
from copy import deepcopy
import json
from pathlib import Path
import time

import finite_prime_obstruction_042 as PRODUCER
import check_finite_prime_obstruction_042 as CHECKER


ROOT=Path(__file__).resolve().parent
PARENT=ROOT/'centered-mobius-bound-results/recovery-001'
OUT=ROOT/'finite-prime-obstruction-results/pilot-001'
FILES=['finite_prime_obstruction_042.py','check_finite_prime_obstruction_042.py',
       'test_finite_prime_obstruction_042.py','test_check_finite_prime_obstruction_042.py',
       'finite_prime_obstruction_042_development.json','check_finite_prime_obstruction_042_development.json',
       'FINITE_PRIME_OBSTRUCTION_042.txt','FINITE_PRIME_OBSTRUCTION_SCOPE_042.txt',
       'run_finite_prime_obstruction_042.py','finite_prime_obstruction_protocol_042.txt']


def read(path):return json.loads(path.read_text())


def write(path,obj):
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('x') as stream:
        json.dump(obj,stream,indent=2,sort_keys=True);stream.write('\n')


def main():
    started=time.monotonic()
    parent_report=read(PARENT/'report.json')
    if parent_report['status']!='CENTERED_MOBIUS_COVARIANCE_CANDIDATES_AUDITED_UNIFORM_BOUND_OPEN':
        raise ValueError('completed041 finite experiment required')
    previous=read(PARENT/'proof_search_input.json')
    source=read(PARENT/'bound_search_frontier.json')['source_binding']
    normalization=read(PARENT/'conditional_verification.json')['coefficient_normalization']
    if source['r']!=normalization['r'] or source['q']!=normalization['q']:
        raise ValueError('complete parent source and scalar parameters')
    r,q=source['r'],source['q']
    if (r,q)!=('1/3',2):raise ValueError('declared042 actual scalar calibration')
    OUT.mkdir(parents=True,exist_ok=False)
    try:
        for name in FILES:
            dest=OUT/'source_snapshot'/name;dest.parent.mkdir(parents=True,exist_ok=True)
            dest.write_bytes((ROOT/name).read_bytes())
        for name in ('proof_search_input.json','mechanism_diagnostic.json','bound_search_frontier.json'):
            (OUT/'source_snapshot'/('parent041_'+name)).write_bytes((PARENT/name).read_bytes())
        spec=dict(schema='finite-prime-obstruction-run-spec-v1',
            mode='symbolic negative proof-scope calibration; not a numerical candidate search',
            r=r,q=q,k_lower='1/10',K_upper=int(normalization['absolute_ceiling']),
            prime_sets=[[2],[2,3],[2,3,5,7,11]],
            producer_work_cap=10_000_000,checker_work_cap=50_000_000,
            no_actual_coefficient_generation=True,no_source_array_replay=True,
            expected_claim_scope='finite-prime-only rules, excluding the full global source identity',
            bound_candidates_reselected=False)
        write(OUT/'run_spec.json',spec)
        rows=[]
        for i,P in enumerate(spec['prime_sets'],1):
            producer_meter=PRODUCER.Meter(cap=spec['producer_work_cap'],seconds=60)
            proposal=PRODUCER.generate_certificate(P,r,q,spec['k_lower'],spec['K_upper'],producer_meter)
            checker_meter=CHECKER.Meter(cap=spec['checker_work_cap'])
            checked=CHECKER.verify(proposal,checker_meter)
            if (not checked['verified'] or not checked['finite_prime_only_rule_obstructed']
                or checked['actual_source_refuted'] or checked['existing_041_source_binding_refuted']
                or checked['RH_proved'] or checked['RH_refuted']):
                raise ValueError('independent scoped admission failed')
            path='certificate_%03d.json'%i
            write(OUT/path,dict(proposal=proposal,verification=checked,
                producer_counts=producer_meter.counts(),checker_operations=checker_meter.operations))
            rows.append(dict(path=path,primes=P,verification=checked,
                producer_counts=producer_meter.counts(),checker_operations=checker_meter.operations))
        feedback=dict(status='FINITE_PRIME_ONLY_PROOF_SCOPE_OBSTRUCTED',
            certificate_family='for any fixed finite set of registered primes and every valuation',
            retained_premises=['coefficient unit and absolute bound',
                'all coefficient/divisibility laws at the registered primes',
                'complete periodic dilation and externally stipulated actual analytic scalar'],
            excluded_premises=['universal actual Euler laws at all primes',
                'actual global Dirichlet identity',
                'actual source residue relation for the stipulated analytic center'],
            first_missing_prime_witnesses=[row['verification']['first_missing_prime'] for row in rows],
            finite_prefix_alias=dict(condition='P contains every prime <=H',
                conclusion='fake and actual coefficients, centered prefixes and supported finite tests agree through H',
                proof='all prime factors and valuations of every n<=H are registered',
                implementation_prime_cap_is_only_a_resource_limit=True),
            full_source_proof_scope='OPEN; this countermodel does not apply',
            next_action='use and certify a universally quantified source relation inside the bound argument',
            actual_arithmetic_bound_proved=False,actual_source_refuted=False,RH_proved=False,RH_refuted=False)
        write(OUT/'proof_scope_feedback.json',feedback)
        continuation=deepcopy(previous)
        continuation['authoritative_parent']=str((PARENT/'proof_search_input.json').relative_to(ROOT))
        continuation['finite_prime_scope_calibration']=dict(
            results=str(OUT.relative_to(ROOT)),feedback=feedback,
            certificates=[str((OUT/row['path']).relative_to(ROOT)) for row in rows],
            numerical_bound_candidates_replaced=False,original_target_replaced=False)
        continuation['next_construction']['proof_scope_requirement']=dict(
            rejection='registered finite prime laws alone do not certify the target',
            distinction='a universally quantified local law may be used in a finite symbolic proof',
            input_source_definition_is_not_itself_an_estimate=True,
            requirement='record where the full arithmetic identity supplies an inequality or a paid auxiliary',
            existing_all_prime_identities_should_not_be_rerun_as_new_discoveries=True)
        write(OUT/'next_search_input.json',continuation)
        report=dict(status='FINITE_PRIME_PROOF_SCOPE_OBSTRUCTION_VERIFIED_ACTUAL_BOUND_OPEN',
            certificates=rows,uniform_scope_obstruction_verified=True,
            actual_source_coefficient_observations=0,source_studies_rerun=0,
            independent_scalar_normalization_checked=True,
            producer_operations=sum(row['producer_counts']['operations'] for row in rows),
            checker_operations=sum(row['checker_operations'] for row in rows),
            parent_covariance_bounds_proved=0,actual_source_bound_proved=False,
            actual_source_refuted=False,existing_041_source_binding_refuted=False,
            RH_proved=False,RH_refuted=False,elapsed_seconds=time.monotonic()-started,
            development_receipts={name:read(ROOT/name) for name in FILES if name.endswith('_development.json')})
        for name in FILES:
            if (ROOT/name).read_bytes()!=(OUT/'source_snapshot'/name).read_bytes():
                raise ValueError('frozen042 code changed: '+name)
        write(OUT/'report.json',report)
        print(json.dumps({key:value for key,value in report.items() if key!='development_receipts'}),flush=True)
    except Exception as error:
        write(OUT/'failure.json',dict(type=type(error).__name__,message=str(error),elapsed_seconds=time.monotonic()-started))
        raise


if __name__=='__main__':main()
