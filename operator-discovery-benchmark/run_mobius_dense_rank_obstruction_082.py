"""Bind exact all-scale grammar obstructions to the frozen complete-drift run."""
import json
import resource
import time
from copy import deepcopy

import run_mobius_dense_completion_082 as RUN
import mobius_dense_rank_obstruction_082 as DISCOVER
import check_mobius_dense_rank_obstruction_082 as CHECK
from run_fractional_prime_kernel_051 import write,emit

FILES=['mobius_dense_rank_obstruction_082.py','test_mobius_dense_rank_obstruction_082.py',
       'mobius_dense_rank_obstruction_082_development.json',
       'check_mobius_dense_rank_obstruction_082.py','test_check_mobius_dense_rank_obstruction_082.py',
       'mobius_dense_rank_obstruction_checker_082_development.json',
       'MOBIUS_DENSE_RANK_OBSTRUCTION_CHECK_SCOPE_082.txt',
       'audit_mobius_dense_rank_obstruction_082.py','mobius_dense_rank_obstruction_independent_audit_082.json',
       'run_mobius_dense_rank_obstruction_082.py']


def main():
    started=time.monotonic();out=RUN.OUT
    if (out/'rank_obstruction_results.json').exists() or (out/'rank_source_snapshot').exists():
        raise FileExistsError('preserve rank followup attempt')
    assert sum(RUN.validate_parent())==566
    for name in RUN.FILES:
        if (RUN.ROOT/name).read_bytes()!=(out/'source_snapshot'/name).read_bytes():
            raise ValueError('preserve main082 '+name)
    snapshot=out/'rank_source_snapshot';snapshot.mkdir()
    for name in FILES:
        (snapshot/name).write_bytes((RUN.ROOT/name).read_bytes())
    roster=json.loads((out/'frozen_task_roster.json').read_text())
    audited=json.loads((RUN.ROOT/'mobius_dense_rank_obstruction_independent_audit_082.json').read_text())
    if audited['status']!='PASS' or audited['case_count']!=24:
        raise ValueError('complete independent rank integration required')
    indexed={(r['source'],r['memory'],r['family']):r for r in audited['cases']}
    sources=RUN.SPEC['source_ids'];family_index={r['id']:i for i,r in enumerate(RUN.families())}
    rows=[]
    for task in roster['tasks']:
        search=json.loads((out/('search_'+task['id']+'.json')).read_text())
        program=search['program'] if search['status']=='LP_PROPOSAL' else task['program']
        cert=indexed[(sources.index(task['source_id']),program['memory'],family_index[task['family_id']])]['certificate']
        admission=RUN.require(CHECK.verify_obstruction(program,cert),'VERIFIED_UNIFORM_DENSE_GRAMMAR_PRICE_OBSTRUCTION')
        rows.append(dict(id=task['id'],source_id=task['source_id'],program=program,certificate=cert,
                         admission=admission,origin='retained independent geometry-discovery integration, rebound to exact frozen LP program',
                         constructor_operations=0,checker_operations=admission['ops']))
    for i,task in enumerate(roster['sublinear_obstructions']):
        program=task['program'];proposal=DISCOVER.discover(program)
        if proposal['status']!='PROPOSED_UNIFORM_RANK_OBSTRUCTION':
            raise ValueError('sublinear witness discovery '+str(proposal))
        admission=RUN.require(CHECK.verify_obstruction(program,proposal['certificate']),
                              'VERIFIED_UNIFORM_DENSE_GRAMMAR_PRICE_OBSTRUCTION')
        rows.append(dict(id='sublinear_'+str(i).zfill(2),source_id=task['source_id'],program=program,
                         certificate=proposal['certificate'],admission=admission,
                         origin='new exact geometry-witness discovery after freezing rank grammar',
                         constructor_operations=proposal['ops'],checker_operations=admission['ops']))
    report=dict(status='VERIFIED_COMPLETE_PILOT_GRAMMAR_PRICE_OBSTRUCTIONS',rows=rows,
                finite_full_profile_programs=24,sublinear_programs=12,uniform_price_obstructions=len(rows),
                scope='For each exact fixed profile roster, B(u)>=c*u^2 beyond the certified threshold; c>0. Not a lower bound for actual Mobius drift.',
                independent_price_checks=sum(r['checker_operations'] for r in rows),
                new_constructor_operations=sum(r['constructor_operations'] for r in rows),
                retained_discovery_integration_reused=True,arithmetic_sign_queries=0,
                elapsed_seconds=time.monotonic()-started,peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024,
                formal_theorem_prover_checked=False,uniform_original_source_bound_proved=False,RH_proved=False)
    write(out/'rank_obstruction_results.json',report)
    feedback=deepcopy(json.loads((out/'next_search_input.json').read_text()))
    feedback.update(schema='dense-completion-certified-obstruction-feedback-v1',
        admitted_obstructions=[dict(id=r['id'],program=r['program'],certificate=r['certificate'],admission=r['admission']) for r in rows],
        all_fixed_pilot_profile_families_excluded_at_every_price_exponent_below_two=True,
        detector_must_reject_more_fixed_floor_moments_as_a_standalone_cure=True,
        why='Independent group boxes plus finitely many homogeneous floor moments admit exact artificial sign averages with order-u source mass. The detector constructs the witnesses and the checker proves their all-scale feasibility.',
        next_language_priority='Search scale-growing or genuinely coupled arithmetic constraints and auxiliary bounds that eliminate these formal witnesses without assuming a Mertens or RH-strength estimate.',
        candidate_mechanisms=[
            dict(kind='multiplicative_cofactor_constraints',identity='mu(a*n)=mu(a)*mu(n) when a,n squarefree and gcd(a,n)=1; zero when squareful',
                 obligation='Control a growing joint family including primitive large-prime contributions; a fixed conditioned-prime list is insufficient unless independently proved otherwise.'),
            dict(kind='growing_divisor_moment_rosters',identity='complete mu*1 divisor identities at a scale-dependent set of K',
                 obligation='Discover a uniform norm/increment bound, with full geometry and cost paid. Reconstructing mu from all K without proving growth is not a closure.'),
            dict(kind='nonseparable_cross_constraints',identity='relations between physical prime/composite pairs, with shared indices and signed cross terms retained',
                 obligation='Build an independent complete-target certificate; prove the auxiliary control rather than fit its constant.'),
        ],
        rejected_standalone_steps=['increase theta box','more fixed floor moments','larger fixed delayed energy','more positive Gram features','fit larger finite C'],
        original_signed_bound_still_unpaid=True,uniform_growth_proved=False,RH_proved=False)
    write(out/'postrun_next_search_input.json',feedback)
    for name in FILES:
        if (RUN.ROOT/name).read_bytes()!=(snapshot/name).read_bytes():
            raise ValueError('rank source changed during run '+name)
    RUN.stage_check(started,[__import__('os').getpid()])
    emit({k:v for k,v in report.items() if k!='rows'})


if __name__=='__main__':
    main()
