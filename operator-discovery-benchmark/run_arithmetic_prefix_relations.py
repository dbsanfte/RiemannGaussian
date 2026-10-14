"""Install exact global source constraints into the next bound-search input."""
import json
from pathlib import Path
import resource
import time

import arithmetic_prefix_relations as P
import check_arithmetic_prefix_relations as C
import check_prime_cofactor_discovery as BASE
import prefix_relation_bridge as B

ROOT=Path(__file__).resolve().parent
SOURCE=ROOT/'prime-cofactor-bound-results/pilot-001'
PREVIOUS=ROOT/'coupled-scale-bound-results/pilot-001'
OUT=ROOT/'arithmetic-prefix-relation-results/pilot-001'
FILES=['arithmetic_prefix_relations.py','check_arithmetic_prefix_relations.py',
       'prefix_relation_bridge.py','run_arithmetic_prefix_relations.py',
       'test_arithmetic_prefix_relations.py','test_prefix_relation_bridge.py',
       'arithmetic_prefix_relations_development.json','prefix_relation_bridge_development.json',
       'ARITHMETIC_PREFIX_RELATIONS_DERIVATION.txt','arithmetic_prefix_relations_protocol.txt']


def read(path):return json.loads(path.read_text())


def write(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('x') as stream:
        json.dump(value,stream,indent=2,sort_keys=True);stream.write('\n')


def main():
    started=time.monotonic()
    resource.setrlimit(resource.RLIMIT_AS,(16*1024**3,resource.getrlimit(resource.RLIMIT_AS)[1]))
    if not read(SOURCE/'verification.json')['verified']:
        raise ValueError('verified complete source and generated basis required')
    if (ROOT/'check_prime_cofactor_discovery.py').read_bytes()!=(SOURCE/'source_snapshot/check_prime_cofactor_discovery.py').read_bytes():
        raise ValueError('unchanged source checker premise')
    if read(PREVIOUS/'report.json')['status']!='COUPLED_SCALE_PROGRAMS_AUDITED_UNIFORM_BOUND_OPEN':
        raise ValueError('complete037 source-bound search input required')
    OUT.mkdir(parents=True,exist_ok=False)
    try:
        for name in FILES:
            dest=OUT/'source_snapshot'/name;dest.parent.mkdir(parents=True,exist_ok=True)
            dest.write_bytes((ROOT/name).read_bytes())
        base=read(SOURCE/'search.json')['certificate']
        source_meter=BASE.Meter();admission=BASE.verify(base['source'],base,source_meter)
        if not admission['verified']:raise ValueError('independent source admission')
        producer_meter=P.Meter(cap=5_000_000,seconds=120)
        checker_meter=C.Meter(cap=5_000_000,seconds=120)
        certificate=P.generate(base['source'],producer_meter)
        C.verify_certificate(base['source'],certificate,checker_meter)
        write(OUT/'relations.json',certificate)
        inverse=B.inverse(base['basis'])
        B.verify_inverse(base['basis'],inverse)
        rows=[];converted=[]
        for N in (0,1,2,3,4,7,16,31):
            for row in P.prefix_rows(certificate,N,producer_meter):
                C.verify_prefix_row(base['source'],certificate,row,checker_meter)
                translated=B.convert_row(row,inverse)
                B.verify_conversion(row,inverse,translated)
                rows.append(row);converted.append(translated)
        write(OUT/'example_rows.json',rows)
        bridge=dict(source_binding=base['source'],state_programs=base['states'],basis=base['basis'],
            inverse=inverse,weighted_channel_coordinates='W=B^-1*V, where V_i is the complete h_i prefix',
            prime_profiles=[B.prime_profile_contract(i) for i in range(len(base['basis']))],
            full_prefix_unit=admission['unit'],full_prefix_below_one='0',
            exact_relation_scope='all integer N>=0',example_converted_rows=converted,
            finite_examples_are_not_the_all_scale_proof=True,uniform_bound_proved=False)
        write(OUT/'state_bridge.json',bridge)
        next_input=read(PREVIOUS/'next_search_input.json')
        lemmas=next_input['coupled_scale_search']['open_lemmas']
        for lemma in lemmas:
            if lemma['source_binding']!=certificate['source_binding'] or lemma['status']!='OPEN':
                raise ValueError('unmodified complete-source OPEN recurrence binding')
            for term in lemma['program']:
                if type(term['state']) is not int or not 0<=term['state']<len(base['basis']):
                    raise ValueError('exact generated-state helper linkage')
        packet=dict(schema='arithmetic-constraint-bound-frontier-v1',
            source_binding=base['source'],global_relations='relations.json',
            state_bridge='state_bridge.json',open_recurrences=lemmas,
            admitted_constraint_forms=[dict(channel=r['channel'],kernel=r['kernel'],rhs=r['rhs'],weight=r['weight'],
                zero_form='sum_(d<=N)D_j(d)*sum_i (B^-1)[j,i]*V_i(floor(N/d))-weight_j*prefix(rhs_j)(N)',
                valid_for='every integer N>=0; every unit and floor endpoint retained') for r in certificate['relations']],
            allowed_identity_use=dict(rule='multiply_exact_zero_relation',
                statement='for any defined real multiplier T, T*L(N)=0 when the admitted exact L(N)=0',
                requires_complete_inhomogeneous_rhs=True,requires_all_floor_terms=True,
                permits_silent_prime_profile_substitution=False),
            proposed_quadratic_proof_goal='paid_forcing-defect = PSD_form + sum complete exact_relation*multiplier',
            multiplier_synthesis_implemented=False,successful_signed_defect_certificate=None,
            generic_envelope_countermodels_are_not_admissible_actual_source_models=True,
            source_identity_discovery_is_not_a_bound=True,
            whole_signed_bound_proved=False,RH_proved=False)
        write(OUT/'bound_search_frontier.json',packet)
        next_input['global_arithmetic_constraints']=dict(
            relations=str(OUT.relative_to(ROOT)/'relations.json'),
            full_state_bridge=str(OUT.relative_to(ROOT)/'state_bridge.json'),
            bound_frontier=str(OUT.relative_to(ROOT)/'bound_search_frontier.json'),
            all_prime_all_valuation_identity_verified=True,
            all_integer_prefix_identity_verified=True,
            source_generation_uses_numerical_values=False,
            next_required_capability='search multiplier/storage programs modulo the admitted complete arithmetic relations',
            exact_source_constraints_are_available_not_yet_a_signed_bound=True,
            whole_signed_bound_proved=False)
        write(OUT/'next_search_input.json',next_input)
        report=dict(status='GLOBAL_ARITHMETIC_PREFIX_CONSTRAINTS_VERIFIED_BOUND_OPEN',
            source_channels=len(certificate['relations']),exact_all_scale_relation_templates=len(certificate['relations']),
            finite_compiler_example_rows=len(rows),converted_rows=len(converted),
            bound_lemma_inputs=len(lemmas),source_observations_performed=False,
            supplied_winning_kernels=False,identities_generated_from_source_atoms=True,
            source_checker_operations=source_meter.operations,producer=producer_meter.counts(),
            relation_checker_operations=checker_meter.operations,
            coordinate_checks_metering='bounded exact4x4 matrix/row checks wall-time accounted',
            development_receipts={name:read(ROOT/name) for name in FILES if name.endswith('_development.json')},
            elapsed_seconds=time.monotonic()-started,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            successful_uniform_recurrences=0,whole_signed_bound_proved=False,RH_proved=False)
        for name in FILES:
            if (ROOT/name).read_bytes()!=(OUT/'source_snapshot'/name).read_bytes():
                raise ValueError('frozen038 source changed: '+name)
        if time.monotonic()-started>120:raise TimeoutError('038 runtime limit')
        write(OUT/'report.json',report)
        print(json.dumps({k:v for k,v in report.items() if k!='development_receipts'}),flush=True)
    except Exception as error:
        write(OUT/'terminal_failure.json',dict(error=type(error).__name__,message=str(error),
            elapsed_seconds=time.monotonic()-started,whole_signed_bound_proved=False,RH_proved=False))
        raise


if __name__=='__main__':main()
