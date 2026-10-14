"""Freeze, proof-filter, discover and independently audit moving profiles."""
import os
os.environ['OPENBLAS_NUM_THREADS']='2'
os.environ['OMP_NUM_THREADS']='2'
from copy import deepcopy
from fractions import Fraction as Q
import json
import multiprocessing as mp
from pathlib import Path
import resource
import time

import floor_residual_search_045 as S
import floor_residual_drift_arguments_045 as ARG
import check_floor_residual_arguments_044 as CHECK
import run_floor_residual_044 as AUDIT
from publish_floor_residual_followup_044 import passing_receipt

ROOT=Path(__file__).resolve().parent
PARENT=ROOT/'floor-residual-results/pilot-002/analytical_followup_001'
LEGACY=PARENT.parent
OUT=ROOT/'floor-residual-results/pilot-003'
RECEIPTS=['floor_residual_drift_045_development.json','check_floor_residual_drift_045_development.json',
          'floor_residual_drift_arguments_045_development_receipt.json',
          'floor_residual_search_045_development.json','floor_residual_runner_045_development.json']
FILES=['floor_residual_drift_045.py','check_floor_residual_drift_045.py','floor_residual_drift_arguments_045.py',
       'floor_residual_search_045.py','run_floor_residual_045.py',
       'test_floor_residual_drift_045.py','test_check_floor_residual_drift_045.py',
       'test_floor_residual_drift_arguments_045.py','test_floor_residual_search_045.py','test_floor_residual_runner_045.py',
       'FLOOR_RESIDUAL_DRIFT_045.txt','FLOOR_RESIDUAL_DRIFT_SCOPE_045.txt','FLOOR_RESIDUAL_DRIFT_ARGUMENTS_045.txt',
       'floor_residual_protocol_045.txt']+RECEIPTS


read=AUDIT.read
write=AUDIT.write
emit=AUDIT.emit


def validate_parent():
    if read(PARENT/'report.json')['status']!='FLOOR_AUXILIARY_BOUND_CLAIMS_ANALYTICALLY_REVIEWED':
        raise ValueError('current analytic parent required')
    counts=[]
    for directory in (LEGACY/'source_snapshot',PARENT/'source_snapshot'):
        snapshots=list(directory.iterdir())
        if not all((ROOT/p.name).read_bytes()==p.read_bytes() for p in snapshots):
            raise ValueError('preserve frozen prior sources')
        counts.append(len(snapshots))
    return counts


def replay_drift_sources(compiler,recipe,N,program,cache,meter):
    """Independent drift powers and mu; old exact weight primitives are reused."""
    def weight_values(weight):
        key=(S.OLD.ast_key(weight),N)
        if key in cache:return cache[key]
        kind=weight['kind']
        if kind=='drift_mixture':
            context=compiler.drift.context(weight,N)
            values=[]
            for n in range(2,N+1):
                proposal=context.compile(n)
                checked=S.DRIFT_CHECK.verify_compilation(weight,n,N,proposal,meter=meter)
                values.append(Q(checked['value']))
        elif kind=='product' and S.has_drift(weight):
            values=[a*b for a,b in zip(weight_values(weight['left']),weight_values(weight['right']))]
        else:
            # These unchanged exact-root and certified-log primitives are
            # frozen044 dependencies, not a newly independent root checker.
            values=compiler.weights_at(weight,N)
        cache[key]=values
        return values
    if not S.has_drift(recipe['base']):
        return dict(status='legacy_exact_compiler_reused',independent_new_drift_atoms=0)
    if recipe['auxiliary'] is not None:raise ValueError('external drift auxiliary unsupported')
    values=weight_values(recipe['base'])
    expected={n:-S.DRIFT_CHECK.mobius(n,meter)*v for n,v in enumerate(values,2) if v}
    expected={n:v for n,v in expected.items() if v}
    actual={r['n']:Q(r['value']) for r in program['coefficients']}
    if actual!=expected or program['constant']!='1' or program['steps']:
        raise ValueError('source-bound drift program mismatch')
    return dict(status='verified_actual_mu_and_exact_drift',independent_new_drift_atoms=(N-1)*len(S.drift_nodes(recipe['base'])),
                old_weight_primitives='frozen exact compiler reused')


def compile_batch(search,parents):
    if tuple(parents)!=S.FINAL_PARENTS:raise ValueError('registered final support partition')
    compiler=S.Compiler(max(parents)*max(S.MULTIPLIERS))
    recipes={r['id']:r for r in search['selected_recipes']}
    programs,seen,cases,rules,identities=[],{},[],[],[]
    source_meter=S.DRIFT_CHECK.Meter(cap=20_000_000_000)
    meter=CHECK.Meter(cap=1_000_000_000)
    source_cache,source_checks={},[]
    def register(p):
        key=S.OLD.semantic_key(p)
        if key not in seen:seen[key]=p['id'];programs.append(p)
        return seen[key]
    for index,selection in enumerate(search['selections'],1):
        recipe,q,b=recipes[selection['family']],selection['q'],selection['b']
        bound=selection['audit_log_bound']
        gate=CHECK.verify_log_forcing_gate(q,b,bound['A'],bound['eta'],meter=meter)
        base=S.baseline_recipe(recipe)
        rule=dict(id='rule_%02d'%index,**selection,recipe=recipe,baseline_recipe=base,conditional_gate=gate)
        rules.append(rule)
        for N in parents:
            parent,child=compiler.compile(recipe,N),compiler.compile(recipe,q*N)
            bp,bc=compiler.compile(base,N),compiler.compile(base,q*N)
            for formula,support,p in ((recipe,N,parent),(recipe,q*N,child),(base,N,bp),(base,q*N,bc)):
                source_checks.append(dict(program=p['id'],**replay_drift_sources(compiler,formula,support,p,source_cache,source_meter)))
            h=S.OLD.forcing_program(parent,child,q,b,rule['id']+'_N'+str(N)+'_forcing')
            h0=S.OLD.forcing_program(bp,bc,q,b,rule['id']+'_N'+str(N)+'_baseline')
            v=S.OLD.difference_program(h,h0,rule['id']+'_N'+str(N)+'_signed_auxiliary')
            identity=CHECK.verify_family_refinement(parent,child,q,b,meter=meter)
            base_identity=CHECK.verify_family_refinement(bp,bc,q,b,meter=meter)
            if S.OLD.semantic_key(identity['forcing_program'])!=S.OLD.semantic_key(h) or S.OLD.semantic_key(base_identity['forcing_program'])!=S.OLD.semantic_key(h0):
                raise ValueError('independent refinement identity disagrees')
            if S.OLD.semantic_key(S.OLD.difference_program(h,v,'replay'))!=S.OLD.semantic_key(h0):
                raise ValueError('signed auxiliary identity disagrees')
            cases.append(dict(rule=rule['id'],N=N,q=q,b=b,has_auxiliary=S.has_signed_auxiliary(recipe),
                log_bound=AUDIT.log_bound_interval(N,bound['A'],bound['eta'],compiler.meter),
                parent=register(parent),child=register(child),forcing=register(h),baseline_forcing=register(h0),auxiliary_forcing=register(v)))
            identities.append(dict(rule=rule['id'],N=N,refinement=identity,baseline_refinement=base_identity,
                                   signed_auxiliary_identity='h=h0+v',auxiliary_program=v))
    for p in programs:CHECK.verify_program(p,target=p['constant']=='1' and not p['steps'],meter=meter)
    return dict(programs=programs,cases=cases,rules=rules,identities=identities,source_checks=source_checks,
        compiler_counts=compiler.meter.counts(),drift_counts=compiler.drift_meter.counts(),
        source_replay_operations=source_meter.operations,argument_operations=meter.operations,
        all_compiled_before_norms=True,uniform_bound_proved=False,RH_proved=False)


def argument_queue(rules):
    meter=ARG.Meter(cap=20_000_000,seconds=600)
    checker=ARG.Meter(cap=20_000_000,seconds=600)
    rows=[]
    allocations=ARG.enumerate_allocations(6)
    for rule in rules:
        request=dict(recipe=rule['recipe'],q=rule['q'],b=rule['b'],
            domain=dict(kind='all_integer',minimum=min(S.FINAL_PARENTS)),rounding=deepcopy(ARG.ROUNDING))
        certificate=ARG.build_arguments(request,meter=meter)
        if certificate['status']=='UNSUPPORTED':
            rows.append(dict(rule=rule['id'],request=request,certificate=certificate,verification=None,
                             bound_arguments=[],uniform_bound_proved=False))
            continue
        verification=ARG.verify_arguments(request,certificate,meter=checker)
        bound=rule['audit_log_bound']
        arguments=[ARG.instantiate_bound(certificate,bound['A'],bound['eta'],allocation,meter=meter) for allocation in allocations]
        rows.append(dict(rule=rule['id'],request=request,certificate=certificate,verification=verification,
                         bound_arguments=arguments,uniform_bound_proved=False))
    return dict(schema='drift-global-bound-search-input-v1',rows=rows,allocation_count=len(allocations),
        operations=meter.operations,replay_operations=checker.operations,
        new_arguments_generated_without_numeric_data=True,all_joint_bound_leaves_remain_open=True,RH_proved=False)


def main():
    started=time.monotonic()
    if OUT.exists():raise FileExistsError('preserve existing045 run')
    parent_counts=validate_parent()
    for name in RECEIPTS:
        if not passing_receipt(read(ROOT/name)):raise ValueError('missing passing owned receipt: '+name)
    snapshots={name:(ROOT/name).read_bytes() for name in FILES}
    legacy_spec=read(LEGACY/'run_spec.json')
    frozen=S.grammar(legacy_spec['grammar']['recipes'])
    OUT.mkdir();(OUT/'source_snapshot').mkdir()
    for name,data in snapshots.items():(OUT/'source_snapshot'/name).write_bytes(data)
    try:
        spec=dict(schema='drift-floor-protocol-v1',grammar=frozen,
            authoritative_parent=str((PARENT/'next_search_input.json').relative_to(ROOT)),
            prior_goal_turn_classification='progress: numerical044 and analytic obstruction feedback completed',
            legacy_training_source=str((LEGACY/'search.json').relative_to(ROOT)),
            legacy_training_norms_recomputed=0,training_parents=list(S.TRAIN_PARENTS),final_parents=list(S.FINAL_PARENTS),
            training_H=S.TRAIN_H,final_H=S.FINAL_H,workers=2,training_BLAS_threads=2,aggregate_memory_limit_bytes=16*1024**3,
            proof_gates_before_new_scores=True,proof_gate_scope='necessary only; all-integer bound and exact exponent/constant',
            ranking='admitted numerical match; stronger eta; signed auxiliary/refinement necessity; observed slopes; proxy; stable ordinal',
            final_domain='every integer N>=607; geometric chain distinguished',
            source_replay='independent drift powers and mu; frozen old exact taper/log primitives reused',
            all_terms_priced_jointly_before_magnitude_replacement=True,hashing_used=False,per_N_fitting=False,RH_proved=False)
        write(OUT/'run_spec.json',spec)
        emit('protocol_frozen',families=len(frozen['recipes']),new_families=frozen['new_family_count'])
        gates=S.proof_gates(frozen,emit)
        write(OUT/'presearch_proofs.json',gates)
        emit('proof_gates_complete',refuted_rules=gates['entirely_refuted_rules'],rejected_bound_pairs=gates['rejected_bound_pairs'])
        search=S.search(frozen,gates,read(LEGACY/'search.json'),emit)
        write(OUT/'search.json',search)
        write(OUT/'selected_families.json',dict(recipes=search['selected_recipes'],rules=search['selections']))
        emit('selection_frozen',rules=search['selections'],matches=search['finite_log_bound_matches'])
        batch=compile_batch(search,S.FINAL_PARENTS)
        write(OUT/'final_program_batch.json',batch)
        queue=argument_queue(batch['rules'])
        write(OUT/'global_bound_arguments.json',queue)
        aggregate=AUDIT.memory_preflight(batch['programs'])
        tasks=[dict(program=p,H=0 if p['constant']=='0' and not p['coefficients'] and not p['steps'] else S.FINAL_H)
               for p in batch['programs']]
        emit('whole_domain_audit_started',programs=len(tasks),aggregate_memory_reserve_bytes=aggregate)
        rows=[]
        with mp.get_context('fork').Pool(2) as pool:
            for row in pool.imap_unordered(AUDIT.audit_one,tasks):
                artifact='norm_%03d.json'%(len(rows)+1)
                write(OUT/artifact,row);rows.append(dict(**row,artifact=artifact))
                emit('norm_verified',completed=len(rows),total=len(tasks),id=row['id'],
                     interval=[float(v) for v in AUDIT.interval(row)])
        by_id={r['id']:r for r in rows}
        if len(by_id)!=len(rows) or set(by_id)!={p['id'] for p in batch['programs']}:raise ValueError('complete norm coverage')
        cases=[AUDIT.analyze_case(case,by_id) for case in batch['cases']]
        write(OUT/'assessment.json',dict(cases=cases,uniform_bound_proved=False,RH_proved=False))
        feedback=dict(schema='moving-profile-bound-feedback-v1',
            authoritative_parent=str((PARENT/'next_search_input.json').relative_to(ROOT)),
            current_results=str(OUT.relative_to(ROOT)),global_arguments=str((OUT/'global_bound_arguments.json').relative_to(ROOT)),
            generated_signed_moment_mixtures=True,proof_obstructions_applied_before_scores=True,
            candidates=[dict(rule=r,finite_cases=[c for c in cases if c['rule']==r['id']]) for r in batch['rules']],
            next_target='bound joint critical-line transfer and truncation while preserving their crosses; discharge exact uniform budgets',
            forbidden_providers=['RH','RH-equivalent Mertens bound without independent proof','finite trends','coefficient control alone'],
            harmonic_component='explicit unconditional envelopes and sufficient level thresholds in supported argument certificates',
            separate_bias_and_truncation_integrability='OPEN; introduced poles may cancel only jointly',
            original_F_and_centered_mobius_obligations='OPEN',uniform_signed_control_proved=False,RH_proved=False,RH_refuted=False)
        write(OUT/'next_search_input.json',feedback)
        report=dict(status='MOVING_SIGNED_PROFILES_AUDITED_JOINT_BOUND_OPEN',
            families=len(frozen['recipes']),new_families=frozen['new_family_count'],signed_profile_count=frozen['profile_count'],
            gated_rules=gates['rule_count'],refuted_rules_before_scores=gates['entirely_refuted_rules'],
            rejected_bound_pairs_before_scores=gates['rejected_bound_pairs'],legacy_training_rows_reused=search['legacy_training_rows_reused'],
            old_training_norms_recomputed=0,training_matches=search['finite_log_bound_matches'],
            exact_vector_price_cache_hits=search['exact_vector_price_cache_hits'],
            distinct_new_training_vectors=search['distinct_new_training_vectors'],
            proof_gate_operations={key:gates[key] for key in ('producer_operations','checker_operations',
                'drift_certificate_operations','cutoff_operations','cutoff_replay_operations')},
            selected_rules=batch['rules'],whole_domain_certificates=len(rows),final_cases=len(cases),
            final_bound_status_counts={label:sum(c['logarithmic_forcing_status']==label for c in cases)
                for label in ('verified_at_this_support','refuted_at_this_support','unresolved_interval')},
            signed_mechanism_counts={kind:{label:sum(c[kind]['mechanism']==label for c in cases)
                for label in sorted({c[kind]['mechanism'] for c in cases})} for kind in ('auxiliary','refinement')},
            global_argument_supported_rules=sum(r['verification'] is not None for r in queue['rows']),
            bound_argument_allocations=queue['allocation_count'],global_bound_proved=False,
            generation_counts=frozen['generation_counts'],search_counts=search['counts'],search_drift_counts=search['drift_counts'],
            compiler_counts=batch['compiler_counts'],compiler_drift_counts=batch['drift_counts'],
            source_replay_operations=batch['source_replay_operations'],finite_argument_operations=batch['argument_operations'],
            global_argument_operations=queue['operations']+queue['replay_operations'],
            norm_producer_operations=sum(r['producer_counts']['operations'] for r in rows),
            norm_checker_operations=sum(r['checker_operations'] for r in rows),
            aggregate_memory_reserve_bytes=aggregate,parent_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            largest_individual_worker_rss_kib=max(r['worker_peak_rss_kib'] for r in rows),
            parent_frozen_file_counts=parent_counts,new_frozen_file_count=len(FILES),
            elapsed_seconds=time.monotonic()-started,development_receipts={n:read(ROOT/n) for n in RECEIPTS},
            RH_proved=False,RH_refuted=False)
        validate_parent()
        if any((ROOT/n).read_bytes()!=data for n,data in snapshots.items()):raise ValueError('frozen045 source changed')
        write(OUT/'report.json',report)
        emit('completed',status=report['status'],elapsed_seconds=report['elapsed_seconds'],
             final_bound_status_counts=report['final_bound_status_counts'],signed_mechanism_counts=report['signed_mechanism_counts'])
    except Exception as error:
        write(OUT/'failure.json',dict(type=type(error).__name__,message=str(error),elapsed_seconds=time.monotonic()-started))
        raise


if __name__=='__main__':main()
