"""Frozen symbolic039 experiment; no arithmetic coefficient archive is read."""
import json
from pathlib import Path
import resource
import time

import arithmetic_prefix_relations as REL
import check_arithmetic_prefix_relations as RELCHECK
import check_prime_cofactor_discovery as BASE
import source_pole_guard as POLE
import check_source_pole_guard as POLECHECK
import global_multiplier_bounds as SEARCH
import check_global_multiplier_bounds as CHECK


ROOT=Path(__file__).resolve().parent
BASE_DIR=ROOT/'prime-cofactor-bound-results/pilot-001'
REL_DIR=ROOT/'arithmetic-prefix-relation-results/pilot-001'
PREVIOUS=REL_DIR/'analytical_followup-001/next_search_input.json'
OUT=ROOT/'global-multiplier-bound-results/pilot-001'
FILES=[
    'global_multiplier_bounds.py','check_global_multiplier_bounds.py',
    'global_multiplier_proto_039.py','source_pole_guard.py','check_source_pole_guard.py',
    'run_global_multiplier_bounds.py','global_multiplier_bounds_protocol.txt',
    'test_global_multiplier_bounds.py','test_check_global_multiplier_bounds.py',
    'global_multiplier_proto_039_test.py','test_source_pole_guard.py','test_check_source_pole_guard.py',
    'global_multiplier_bounds_development.json','global_multiplier_checker_development.json',
    'global_multiplier_proto_039_development.json','source_pole_guard_development.json',
    'check_source_pole_guard_development.json','GLOBAL_MULTIPLIER_BACKEND_039.txt',
    'MULTIPLIER_PROOF_SCOPE_039.txt',
    'arithmetic_prefix_relations.py','check_arithmetic_prefix_relations.py',
    'check_prime_cofactor_discovery.py','prime_cofactor_discovery_protocol.txt']


def read(path):return json.loads(path.read_text())


def write(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('x') as stream:
        json.dump(value,stream,indent=2,sort_keys=True);stream.write('\n')


def unchanged(name,directory):
    if (ROOT/name).read_bytes()!=(directory/'source_snapshot'/name).read_bytes():
        raise ValueError('unchanged inherited source premise: '+name)


def main():
    started=time.monotonic()
    resource.setrlimit(resource.RLIMIT_AS,(16*1024**3,resource.getrlimit(resource.RLIMIT_AS)[1]))
    for name in ('check_prime_cofactor_discovery.py','prime_cofactor_discovery_protocol.txt'):
        unchanged(name,BASE_DIR)
    for name in ('arithmetic_prefix_relations.py','check_arithmetic_prefix_relations.py'):
        unchanged(name,REL_DIR)
    if not read(BASE_DIR/'verification.json')['verified']:
        raise ValueError('verified original source required')
    if read(REL_DIR/'report.json')['status']!='GLOBAL_ARITHMETIC_PREFIX_CONSTRAINTS_VERIFIED_BOUND_OPEN':
        raise ValueError('verified038 all-scale constraints required')
    next_input=read(PREVIOUS)
    if next_input['source']!='original_complete_core_f' or next_input['whole_signed_bound_proved']:
        raise ValueError('complete original OPEN target continuation')
    OUT.mkdir(parents=True,exist_ok=False)
    try:
        for name in FILES:
            dest=OUT/'source_snapshot'/name;dest.parent.mkdir(parents=True,exist_ok=True)
            dest.write_bytes((ROOT/name).read_bytes())
        base=read(BASE_DIR/'search.json')['certificate'];source=base['source']
        source_meter=BASE.Meter();source_admission=BASE.verify(source,base,source_meter)
        if not source_admission['verified']:raise ValueError('source admission')
        relations=read(REL_DIR/'relations.json')
        relation_meter=RELCHECK.Meter(cap=1_000_000,seconds=180)
        RELCHECK.verify_certificate(source,relations,relation_meter)
        # Literal exact translation of the unchanged035 protocol/_actual_R,
        # not an expression supplied by the newly generated pole solution.
        actual_R=[dict(coefficient='9/2',powers=[['2/3',-2],['4/3',1]]),
                  dict(coefficient='-9/2',powers=[['2/3',-1]])]
        binding=dict(source_binding=source,definition=actual_R,
            inherited_definition='(9/2)[zeta(4/3)/zeta(2/3)^2-1/zeta(2/3)]',
            admitted_by='unchanged035 protocol and independent check_prime_cofactor_discovery._actual_R',
            source_checker_replayed=True,R_interval=['1','5'],R_enclosure=source_admission['R_enclosure'])
        write(OUT/'source_scalar_binding.json',binding)
        pole_meter=REL.Meter(cap=1_000_000,seconds=180)
        pole_certificate=POLE.inspect(source,pole_meter)
        pole_checker_meter=POLECHECK.Meter()
        pole_verification=POLECHECK.verify(source,pole_certificate,actual_R=actual_R,
                                         formal_R='2',meter=pole_checker_meter)
        relevant=[row for row in pole_verification['pole_checks'] if SEARCH.Q(row['point'])>SEARCH.Q(1,2)]
        if not relevant or not all(row.get('exact_cancellation_proved') for row in relevant):
            raise ValueError('necessary fixed-source normalization has not been admitted')
        write(OUT/'source_pole_certificate.json',pole_certificate)
        write(OUT/'source_pole_verification.json',pole_verification)
        producer_meter=REL.Meter(cap=20_000_000,seconds=180)
        result=SEARCH.search(source,relations,producer_meter)
        write(OUT/'search.json',result)
        check_started=time.monotonic()
        verification=CHECK.verify_search(source,relations,result)
        checker_seconds=time.monotonic()-check_started
        write(OUT/'verification.json',verification)
        equivalents=[case for case in result['auxiliary_cases'] if case['equivalent_obligation'] is not None]
        root_cases=result['cases']+result['auxiliary_cases']
        verified_full=[case for case in root_cases if case.get('meets_subpower_target')]
        if verified_full:raise ValueError('new full bound requires complete downstream proof integration')
        obligations=dict(schema='normalization-aware-bound-frontier-v1',source_binding=source,
            inherited_input=str(PREVIOUS.relative_to(ROOT)),
            target=dict(prefix='complete original F',energy='X^-2 sum_(X<=n<2X) F(n)^2',
                        requirement='O_epsilon(X^epsilon) for every epsilon>0, every integer X>=1',
                        constants_uniform_in='X; no free change to the fixed source scalar',status='OPEN'),
            admitted=[dict(id='source_pole_normalization',status='PROVED_NECESSARY_CONDITION',
                           certificate='source_pole_verification.json',bound_payment=False),
                      dict(id='complete_source_prefix_relations',status='PROVED_IDENTITY',
                           certificate=str((REL_DIR/'relations.json').relative_to(ROOT)),bound_payment=False),
                      dict(id='global_quadratic_implications',status='VERIFIED_WITH_RETAINED_DEBTS',
                           certificate='verification.json',bound_payment=False)],
            failed_relaxation=dict(rule='complete scalar joined-tail relation and RHS energy providers',
                source_specific_normalization_finite_consequence_used=False,
                actual_source_refuted=False,more_scalar_tuning_same_span_useful=False),
            equivalent_endpoints=[dict(name=case['name'],identity=case['equivalent_obligation'],status='OPEN')
                                  for case in equivalents],
            next_search_targets=[
                dict(id='finite_normalization_bridge',priority=1,status='OPEN',
                     input='source-generated residue equation and original complete finite convolution',
                     search_for='finite truncation/smoothing identity retaining all boundary and signed tail terms',
                     required_output='a proved remainder bound or a concrete independently testable signed lemma',
                     forbidden_assumption='ordinary reciprocal-zeta Dirichlet series convergence at the cancelled pole'),
                dict(id='normalization_sensitive_signed_control',priority=2,status='OPEN',
                     input='complete original source, exact fixed scalar, all floor/source identities',
                     search_for='joint prime/composite Gram, finite kernel remainder, or scale recurrence',
                     target='full original energy or one of the six retained037 recurrences',
                     required_output='explicit all-scale argument with every forcing and recovery price'),
                dict(id='finite_stencil_extension',priority=3,status='OPEN',
                     search_for='moving support or approximate jointly signed inverse with full remainder',
                     fixed_finite_exact_inverse='excluded only for individual positive convolution kernels')],
            equivalent_links_are_not_proof_dependencies=True,
            whole_signed_bound_proved=False,RH_proved=False)
        write(OUT/'bound_search_frontier.json',obligations)
        next_input['authoritative_parent']=str(PREVIOUS.relative_to(ROOT))
        next_input['previous_scheduled_construction']=next_input['next_construction']
        next_input['next_construction']=obligations['next_search_targets'][0]
        next_input['global_multiplier_search']=dict(
            results=str(OUT.relative_to(ROOT)),verified=True,
            argument_synthesis_implemented=True,
            argument_class='all-integer complete-relation rational quadratic multipliers',
            finite_normalization_bridge_implemented=False,
            fixed_source_scalar_binding=str((OUT/'source_scalar_binding.json').relative_to(ROOT)),
            source_family_scope_guard=str((OUT/'source_pole_verification.json').relative_to(ROOT)),
            frontier=str((OUT/'bound_search_frontier.json').relative_to(ROOT)),
            successful_full_source_bounds=0,
            same_span_scalar_tuning_deprioritized=True,whole_signed_bound_proved=False)
        next_input['global_arithmetic_constraints']['next_required_capability']='finite normalization-sensitive signed remainder construction and proof search'
        next_input['whole_signed_bound_proved']=False;next_input['RH_proved']=False
        write(OUT/'next_search_input.json',next_input)
        cases=result['cases']+result['auxiliary_cases']+result['calibrations']
        report=dict(status='GLOBAL_MULTIPLIERS_AND_EXACT_NORMALIZATION_VERIFIED_BOUND_OPEN',
            original_source_scalar_exactly_bound=True,
            generated_positive_real_poles=len(pole_certificate['positive_poles']),
            exact_source_residue_cancellations=sum(row.get('exact_cancellation_proved',False)
                                                 for row in pole_verification['pole_checks']),
            family_R2_pole_obstructions=sum(row.get('family_subpower_energy_excluded',False)
                                          for row in pole_verification['pole_checks']),
            actual_source_refuted=False,source_coefficient_observations=False,
            real_zeta_constants_evaluated_rigorously=True,
            core_cases=len(result['cases']),rational_auxiliary_coefficients=len(result['rational_auxiliary_coefficients']),
            complete_auxiliary_constructions=len(result['auxiliary_cases']),
            span_obstructions=sum(case['status']=='no_bound_in_provider_span' for case in root_cases),
            exact_equivalent_endpoints=len(equivalents),
            actual_full_source_quadratic_implications=sum('certificate' in case.get('search',{}) for case in root_cases),
            convolved_channel_calibrations=len(result['calibrations']),
            subpower_convolved_calibrations=sum(case.get('meets_subpower_target',False) for case in result['calibrations']),
            calibration_is_original_target=False,
            all_scale_floor_templates=len(result['floor_templates']),
            finite_inverse_rejections=sum(item['finite_inverse']['status']=='rejected' for item in result['floor_templates']),
            total_coefficient_trials=sum(case['coefficient_trials'] for case in cases),
            source_checker_operations=source_meter.operations,relation_checker_operations=relation_meter.operations,
            pole_producer=pole_meter.counts(),pole_checker_operations=pole_checker_meter.operations,
            producer=producer_meter.counts(),independent_quadratic_checker_seconds=checker_seconds,
            development_receipts={name:read(ROOT/name) for name in FILES if name.endswith('_development.json')},
            elapsed_seconds=time.monotonic()-started,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            fixed_normalization_used_in_finite_bound=False,
            successful_full_source_bounds=0,successful_uniform_recurrences=0,
            whole_signed_bound_proved=False,RH_proved=False)
        for name in FILES:unchanged(name,OUT)
        if time.monotonic()-started>180:raise TimeoutError('039 runtime limit')
        write(OUT/'report.json',report)
        print(json.dumps({k:v for k,v in report.items() if k!='development_receipts'}),flush=True)
    except Exception as error:
        write(OUT/'terminal_failure.json',dict(error=type(error).__name__,message=str(error),
            elapsed_seconds=time.monotonic()-started,whole_signed_bound_proved=False,RH_proved=False))
        raise


if __name__=='__main__':main()
