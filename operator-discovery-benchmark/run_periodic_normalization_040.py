"""Actual-source040 symbolic search and independent uniform reduction replay."""
from copy import deepcopy
import json
from pathlib import Path
import resource
import time

import arithmetic_prefix_relations as SOURCE
import check_prime_cofactor_discovery as BASE
import check_coupled_scale_bounds as DEPENDENCIES
import periodic_normalization_search_040 as SEARCH
import check_periodic_normalization_040 as CHECK


ROOT=Path(__file__).resolve().parent
BASE_DIR=ROOT/'prime-cofactor-bound-results/pilot-001'
PARENT=ROOT/'global-multiplier-bound-results/pilot-001'
OUT=ROOT/'periodic-normalization-results/pilot-001'
RECEIPTS=['periodic_normalization_search_040_development.json',
          'check_periodic_normalization_040_development.json',
          'finite_normalization_backend_040_development.json']
FILES=['periodic_normalization_search_040.py','check_periodic_normalization_040.py',
       'run_periodic_normalization_040.py','periodic_normalization_protocol_040.txt',
       'test_periodic_normalization_search_040.py','test_check_periodic_normalization_040.py',
       'PERIODIC_NORMALIZATION_SCOPE_040.txt',
       'finite_normalization_backend_040.py','test_finite_normalization_backend_040.py',
       'FINITE_NORMALIZATION_BACKEND_040.txt','FINITE_NORMALIZATION_SCOPE_040.txt',
       'arithmetic_prefix_relations.py','check_source_pole_guard.py',
       'check_prime_cofactor_discovery.py','prime_cofactor_discovery_protocol.txt',
       'check_coupled_scale_bounds.py']+RECEIPTS


def read(path):return json.loads(path.read_text())


def write(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('x') as stream:
        json.dump(value,stream,indent=2,sort_keys=True);stream.write('\n')


def unchanged(name,directory):
    if (ROOT/name).read_bytes()!=(directory/'source_snapshot'/name).read_bytes():
        raise ValueError('changed inherited proof premise: '+name)


def frontier(source,selected):
    reduction=selected['reduction']
    graph=[dict(id='source_binding',status='PROVED',requires=[]),
           dict(id='exact_normalization',status='PROVED',requires=['source_binding']),
           dict(id='periodic_inversion',status='PROVED',requires=[]),
           dict(id='complete_source_transform',status='PROVED',requires=['source_binding','periodic_inversion']),
           dict(id='all_real_kernel_bounds',status='PROVED',requires=['periodic_inversion']),
           dict(id='complete_remainder',status='PROVED',
                requires=['exact_normalization','complete_source_transform','all_real_kernel_bounds']),
           dict(id='centered_mobius_energy',status='OPEN',requires=['source_binding']),
           dict(id='preconditioned_source_energy',status='CONDITIONAL',
                requires=['complete_remainder','centered_mobius_energy']),
           dict(id='RH_via_surviving_pole',status='CONDITIONAL',requires=['preconditioned_source_energy']),
           dict(id='original_F_energy',status='OPEN',requires=['source_binding'])]
    DEPENDENCIES._verify_dependencies(graph)
    return dict(schema='periodic-normalization-bound-frontier-v1',source_binding=source,
        selected=dict(q=selected['q'],power=selected['power']),
        new_target=dict(id='centered_mobius_energy',status='OPEN',
            definition=reduction['target'],r='1/3',theta='2/3',q=selected['q'],
            convolution='Dirichlet',prefix='sum_(1<=n<=x)',
            energy='E_Jq(X)=X^-2 sum_(X<=n<2X) J_q(n)^2',
            required='for EVERY epsilon>0, E_Jq(X)<=C_epsilon X^epsilon, EVERY integer X>=1',
            constant_uniform_in='X; q and the source parameters are fixed',
            analytic_main='1/zeta(theta); ordinary mu(theta) convergence is not assumed',
            subunit_centering='J(x)=-x^theta/(theta*zeta(theta)) for0<x<1',
            numerical_source_values_used=False,uniform_bound_proved=False),
        paid_remainder=reduction['paid_remainder'],
        exact_reduction=reduction,
        dependency_graph=graph,dependency_graph_verified=True,
        search_feedback=dict(
            leading_inverse_degree_before=2,leading_inverse_degree_after=1,
            eliminated_obstruction='joint shifted-inverse terms after exact theta normalization',
            remaining_obstruction='unshifted signed Mobius cancellation in the centered linear prefix',
            failed_provider='absolute shifted contraction needs v+sigma>1; an unshifted inverse has v=0',
            next_grammar=['complete signed correlation decompositions',
                          'cross-scale storage and telescoping identities',
                          'auxiliary weights with independently priced recovery',
                          'rational exponents constrained by complete proof costs'],
            candidate_lemma_example=dict(status='OPEN_NOT_TESTED',
                statement='E_Jq(2X)<=E_Jq(X)+C, for every dyadic X>=1 with fixed C>=0',
                conditional_consequence='O(log X) dyadic energy and, by covering, all-integer subpower energy',
                example_is_not_required_search_shape=True),
            priorities=['prove an exponent or scale recurrence','reduce to genuinely paid arithmetic inputs'],
            reject=['critical inverse erasure without another RH bridge',
                    'target or equivalent endpoint used as its own paid premise',
                    'ordinary critical Mobius moment convergence assumed from analytic continuation',
                    'omitted units, signed tails, cross terms or subunit main',
                    'numerical constant tuning presented as a stronger growth theorem']),
        registered_RH_bridge=selected['pole_budget'],
        original_F_bound_proved=False,RH_proved=False)


def main():
    started=time.monotonic()
    resource.setrlimit(resource.RLIMIT_AS,(16*1024**3,resource.getrlimit(resource.RLIMIT_AS)[1]))
    for name in ('check_prime_cofactor_discovery.py','prime_cofactor_discovery_protocol.txt'):
        unchanged(name,BASE_DIR)
    for name in ('arithmetic_prefix_relations.py','check_source_pole_guard.py'):
        unchanged(name,PARENT)
    unchanged('check_coupled_scale_bounds.py',ROOT/'coupled-scale-bound-results/pilot-001')
    if read(PARENT/'report.json')['status']!='GLOBAL_MULTIPLIERS_AND_EXACT_NORMALIZATION_VERIFIED_BOUND_OPEN':
        raise ValueError('verified039 parent required')
    previous=read(PARENT/'next_search_input.json')
    if previous['source']!='original_complete_core_f' or previous['whole_signed_bound_proved']:
        raise ValueError('retained complete original OPEN source')
    OUT.mkdir(parents=True,exist_ok=False)
    try:
        for name in FILES:
            path=OUT/'source_snapshot'/name;path.parent.mkdir(parents=True,exist_ok=True)
            path.write_bytes((ROOT/name).read_bytes())
        base=read(BASE_DIR/'search.json')['certificate'];source=base['source']
        base_meter=BASE.Meter();admission=BASE.verify(source,base,base_meter)
        if not admission['verified']:raise ValueError('independent original source admission')
        binding=read(PARENT/'source_scalar_binding.json')
        actual_R=[dict(coefficient='9/2',powers=[['2/3',-2],['4/3',1]]),
                  dict(coefficient='-9/2',powers=[['2/3',-1]])]
        if binding['source_binding']!=source or binding['definition']!=actual_R:
            raise ValueError('separate exact035 source scalar binding')
        normalization=dict(actual_R=actual_R,source_pole_certificate=read(PARENT/'source_pole_certificate.json'))
        write(OUT/'source_normalization.json',normalization)
        producer_meter=SOURCE.Meter(cap=1_000_000,seconds=120)
        proposal=SEARCH.search(source,meter=producer_meter)
        producer_counts=producer_meter.counts()
        write(OUT/'search.json',proposal)
        checker_meter=SOURCE.Meter(cap=1_000_000,seconds=120)
        verification=CHECK.verify(source,proposal,normalization,meter=checker_meter)
        checker_counts=checker_meter.counts()
        write(OUT/'verification.json',verification)
        if proposal['selected'] is None:raise ValueError('no independently eligible periodic reduction')
        selected=next(p for p in proposal['programs']
                      if dict(q=p['q'],power=p['power'])==proposal['selected'])
        obligations=frontier(source,selected)
        write(OUT/'bound_search_frontier.json',obligations)
        continuation=deepcopy(previous)
        continuation['authoritative_parent']=str((PARENT/'next_search_input.json').relative_to(ROOT))
        continuation['periodic_normalization_search']=dict(
            results=str(OUT.relative_to(ROOT)),verified=True,exact_normalization_used_in_bound=True,
            selected=proposal['selected'],paid_remainder=selected['reduction']['paid_remainder'],
            new_target_status='OPEN',original_F_obligations_retained=True,
            inverse_periodic_operator_assumed_bounded=False,
            frontier=str((OUT/'bound_search_frontier.json').relative_to(ROOT)),
            whole_signed_bound_proved=False,RH_proved=False)
        continuation['global_multiplier_search']['finite_normalization_bridge_implemented']=True
        continuation['global_arithmetic_constraints']['next_required_capability']='signed centered-Mobius bound argument synthesis'
        continuation['previous_construction']=continuation['next_construction']
        continuation['next_construction']=dict(id='centered_mobius_energy',priority=1,status='OPEN',
            target=obligations['new_target'],
            required_output='a complete signed estimate or recursive auxiliary lemma plus its uniform bound argument',
            inherited_original_F_obligation_replaced=False,
            conditional_RH_bridge='verified periodic preconditioning and surviving rightmost reciprocal-zeta pole',
            frontier=str((OUT/'bound_search_frontier.json').relative_to(ROOT)))
        write(OUT/'next_search_input.json',continuation)
        report=dict(status='PERIODIC_NORMALIZATION_REDUCTION_VERIFIED_LINEAR_SIGNED_BOUND_OPEN',
            programs=len(proposal['programs']),paid_reductions=verification['paid_reductions'],
            selected=proposal['selected'],hyperbola=proposal['hyperbola_search'],
            paid_remainder=selected['reduction']['paid_remainder'],
            rejected_pole_erasure_controls=sum(not p['pole_budget']['RH_pole_bridge_available'] for p in proposal['programs']),
            exact_source_normalization_replayed=True,fixed_normalization_used_in_finite_bound=True,
            source_checker_operations=base_meter.operations,producer=producer_counts,checker=checker_counts,
            development_receipts={name:read(ROOT/name) for name in RECEIPTS},
            numerical_source_observations=0,prior_coefficient_archives_read=False,
            supplied_grammar='periodic preconditioning, analytic centering and reviewed kernel bound rules',
            generated_choices='periodic coefficient, period/copy programs, exact fractional split, complete bound costs',
            general_finite_backend_independently_admitted=False,
            new_linear_target_bound_proved=False,original_F_bound_proved=False,RH_proved=False,
            whole_signed_bound_proved=False,elapsed_seconds=time.monotonic()-started,
            peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
        write(OUT/'report.json',report)
        print(json.dumps({k:report[k] for k in ('status','programs','paid_reductions','selected','paid_remainder',
                         'rejected_pole_erasure_controls','elapsed_seconds','peak_rss_kib')},indent=2))
    except Exception as exc:
        write(OUT/'failure.json',dict(type=type(exc).__name__,message=str(exc),elapsed_seconds=time.monotonic()-started))
        raise


if __name__=='__main__':main()
