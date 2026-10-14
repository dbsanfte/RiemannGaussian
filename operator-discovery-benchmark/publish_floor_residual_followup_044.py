"""Apply two independently checked analytic obstruction languages to044.

No norms, performance search or source arrays are evaluated here. The completed
numerical study is retained unchanged, including its true finite inequalities.
"""
import json
from pathlib import Path
import time

import floor_residual_rate_review_044 as RATE
import check_floor_residual_rates_044 as RATE_CHECK
import floor_residual_cutoff_guard_044 as CUTOFF

ROOT = Path(__file__).resolve().parent
PARENT = ROOT/'floor-residual-results/pilot-002'
OUT = PARENT/'analytical_followup_001'
RECEIPTS = ['floor_residual_rate_review_044_development.json',
            'check_floor_residual_rates_044_development.json',
            'floor_residual_cutoff_guard_044_development_receipt.json',
            'floor_residual_followup_044_development.json']
FILES = ['floor_residual_rate_review_044.py', 'check_floor_residual_rates_044.py',
         'floor_residual_cutoff_guard_044.py', 'floor_residual_recovery_review_043.py',
         'publish_floor_residual_followup_044.py', 'test_floor_residual_rate_review_044.py',
         'test_check_floor_residual_rates_044.py', 'test_floor_residual_cutoff_guard_044.py',
         'test_floor_residual_followup_044.py', 'FLOOR_RESIDUAL_RATE_REVIEW_044.txt',
         'FLOOR_RESIDUAL_RATE_SCOPE_044.txt', 'FLOOR_RESIDUAL_CUTOFF_ARGUMENT_REVIEW_044.txt',
         'floor_residual_proof_followup_044.txt']+RECEIPTS


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('x') as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write('\n')


def request_for(recipe, q, b):
    return dict(recipe=recipe, q=q, b=b, domain=dict(kind='all_integer',minimum=257),
                rounding=dict(kind='dyadic_power_floor',bits_multiplier=4,scale='ceil_log2_N'))


def passing_receipt(receipt):
    runs = receipt.get('invocations', receipt.get('runs'))
    if type(runs) is list:
        return bool(runs) and type(runs[-1]) is dict and type(runs[-1].get('returncode')) is int and runs[-1]['returncode']==0
    # The cutoff guard's one-shot native runner records unittest outcomes.
    return (type(runs) is int and runs > 0
            and type(receipt.get('tests_run')) is int and receipt['tests_run'] > 0
            and type(receipt.get('failures')) is int and receipt['failures']==0
            and type(receipt.get('errors')) is int and receipt['errors']==0)


def cutoff_review(request, producer_meter, checker_meter):
    certificate = CUTOFF.build_guard(request, meter=producer_meter)
    if certificate['status']==CUTOFF.REFUTED:
        verification = CUTOFF.verify_guard(request, certificate, meter=checker_meter)
        if verification.get('verified') is not True:
            raise ValueError('cutoff proof replay failed')
    elif certificate['status']==CUTOFF.UNSUPPORTED:
        verification = dict(verified=False, status=CUTOFF.UNSUPPORTED,
                            uniform_vanishing_forcing_impossible=False,
                            scope='no theorem admitted for this unsupported AST')
    else:
        raise ValueError('unknown cutoff result')
    return dict(request=request, certificate=certificate, verification=verification)


def _same(a, b):
    return json.dumps(a,sort_keys=True,allow_nan=False)==json.dumps(b,sort_keys=True,allow_nan=False)


def merge_rules(selected, rate_review, rate_verification, cutoff_rows):
    if rate_verification.get('verified') is not True:
        raise ValueError('independent rate replay is required')
    recipes = {r['id']:r for r in selected['recipes']}
    rate_by_key = {}
    for family in rate_review['reviews']:
        for row in family['rule_reviews']:
            rule = row['rule']
            key = rule['family'], rule['q'], rule['b'], rule['stratum']
            if key in rate_by_key:
                raise ValueError('duplicate analytic rate rule')
            rate_by_key[key] = row
    cutoff_by_key = {tuple(row['rule_key']):row for row in cutoff_rows}
    expected = [(r['family'],r['q'],r['b'],r['stratum']) for r in selected['rules']]
    if set(expected)!=set(rate_by_key) or set(expected)!=set(cutoff_by_key) or len(cutoff_rows)!=len(expected):
        raise ValueError('complete independent analytic rule coverage')
    result = []
    for rule, key in zip(selected['rules'],expected):
        rate, cutoff = rate_by_key[key], cutoff_by_key[key]
        if not _same(rate['rule'],rule) or not _same(cutoff['request'],request_for(recipes[rule['family']],rule['q'],rule['b'])):
            raise ValueError('analytic result does not bind the complete selected rule/recipe')
        if rate['status'] not in ('analytically_refuted','OPEN'):
            raise ValueError('unknown rate proof status')
        rate_refuted = rate['status']=='analytically_refuted'
        cutoff_refuted = cutoff['certificate']['status']=='REFUTED_ALL_INTEGER_VANISHING_FORCING'
        if cutoff_refuted:
            if cutoff['verification'].get('verified') is not True or cutoff['verification'].get('status')!=CUTOFF.REFUTED:
                raise ValueError('independent cutoff proof replay is required')
        elif cutoff['certificate']['status']!=CUTOFF.UNSUPPORTED or cutoff['verification'].get('verified') is not False:
            raise ValueError('unsupported cutoff AST cannot carry a proof')
        result.append(dict(rule=rule,
            advertised_all_integer_bound='analytically_refuted' if rate_refuted or cutoff_refuted else 'OPEN',
            logarithmic_rate_gate=rate['status'], cutoff_shape_gate=cutoff['certificate']['status'],
            rate_witness=rate['strongest_rejection'],
            uniform_vanishing_forcing_all_integers='analytically_refuted' if cutoff_refuted else 'OPEN',
            geometric_subsequence_convergence='OPEN',
            selected_eta_on_any_unbounded_subsequence='analytically_refuted' if rate_refuted else 'OPEN',
            lower_eta_is_proved=False, all_other_operators_refuted=False,
            finite_norm_inequalities_remain_true=True, RH_proved=False, RH_refuted=False))
    return result


def validate_parent():
    report = read(PARENT/'report.json')
    if report.get('status')!='COMPATIBLE_AUXILIARIES_AUDITED_UNIFORM_BOUND_OPEN' or report.get('RH_proved') is not False:
        raise ValueError('frozen044 parent scope changed')
    snapshots = list((PARENT/'source_snapshot').iterdir())
    if not all((ROOT/p.name).read_bytes()==p.read_bytes() for p in snapshots):
        raise ValueError('frozen044 source snapshot changed')
    return report, len(snapshots)


def main():
    started=time.monotonic()
    if OUT.exists():
        raise FileExistsError('preserve existing analytic followup')
    parent_report,parent_files=validate_parent()
    for name in RECEIPTS:
        receipt=read(ROOT/name)
        if not passing_receipt(receipt):
            raise ValueError('missing passing focused receipt: '+name)
    selected=read(PARENT/'selected_families.json')
    grammar=read(PARENT/'run_spec.json')['grammar']
    OUT.mkdir()
    (OUT/'source_snapshot').mkdir()
    for name in FILES:
        (OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
    try:
        write(OUT/'protocol.json',dict(schema='floor-analytic-feedback-protocol-v1',
            parent=str(PARENT.relative_to(ROOT)), max_index=16, precision=192,
            selected_rate_work_cap=10_000_000, frontier_rate_work_cap=100_000_000,
            rate_replay_work_cap=100_000_000, cutoff_scope='all integers N>=257 only',
            cutoff_frontier_parameters=dict(q=2,b='1/2'),
            candidate_identifiers_whitelisted=False, data_used='formula ASTs and frozen q,b,A,eta only',
            numerical_norms_evaluated=0, numerical_trends_used_as_proofs=False,
            subsection_domains_kept_distinct=True, hashing_used=False))
        selected_meter=RATE.Meter(cap=10_000_000)
        rate_review=RATE.audit_selected(selected,max_index=16,precision=192,meter=selected_meter)
        replay_meter=RATE_CHECK.Meter(cap=100_000_000)
        rate_verified=RATE_CHECK.verify(selected,rate_review,meter=replay_meter)
        if rate_verified.get('verified') is not True:
            raise ValueError('selected rate replay failed')
        write(OUT/'selected_rate_review.json',rate_review)
        write(OUT/'selected_rate_verification.json',rate_verified)
        frontier_meter=RATE.Meter(cap=100_000_000)
        rate_frontier=RATE.review_frontier(grammar['recipes'],grammar['log_etas'],max_index=16,precision=192,meter=frontier_meter)
        frontier_verified=RATE_CHECK.verify_frontier(grammar['recipes'],grammar['log_etas'],rate_frontier,
                                                     max_index=16,precision=192,meter=replay_meter)
        if frontier_verified.get('verified') is not True:
            raise ValueError('frontier rate replay failed')
        write(OUT/'rate_frontier.json',rate_frontier)
        write(OUT/'rate_frontier_verification.json',frontier_verified)
        cutoff_meter,cutoff_replay=CUTOFF.Meter(),CUTOFF.Meter()
        recipes={r['id']:r for r in selected['recipes']}
        cutoff_rows=[]
        for rule in selected['rules']:
            request=request_for(recipes[rule['family']],rule['q'],rule['b'])
            cutoff_rows.append(dict(rule_key=[rule['family'],rule['q'],rule['b'],rule['stratum']],
                                    **cutoff_review(request,cutoff_meter,cutoff_replay)))
        write(OUT/'selected_cutoff_review.json',dict(rows=cutoff_rows))
        cutoff_frontier=[]
        for recipe in grammar['recipes']:
            request=request_for(recipe,2,'1/2')
            cutoff_frontier.append(dict(family=recipe['id'],**cutoff_review(request,cutoff_meter,cutoff_replay)))
        write(OUT/'cutoff_frontier.json',dict(rows=cutoff_frontier,scope='registered q2,b1/2 all-integer forcing; unsupported is not refuted'))
        merged=merge_rules(selected,rate_review,rate_verified,cutoff_rows)
        write(OUT/'proof_filtered_rules.json',dict(rules=merged,finite_certificates_unchanged=True,RH_proved=False))
        feedback=dict(schema='floor-two-obstruction-feedback-v1',
            authoritative_parent=str((PARENT/'next_search_input.json').relative_to(ROOT)),
            numerical_parent=str(PARENT.relative_to(ROOT)),
            current_proof_results=str(OUT.relative_to(ROOT)),selected_rules=merged,
            obstruction_languages_implemented=['fixed-index logarithmic rate', 'convex mu fixed-cutoff Mellin transfer'],
            next_search_requirements=[
                'apply typed rate and cutoff guards before numerical ranking',
                'coefficient compatibility must include the rate needed by the proposed estimate',
                'admit explicit auxiliary cancellations of compiled leading terms, with next term proved or marked unresolved',
                'search scale-dependent profiles whose transfer suppresses critical-line contributions',
                'keep log-coordinate weights, moving indices, mixed arithmetic and arbitrary rational exponents available',
                'keep the all-integer estimate distinct from a specified geometric-subsequence estimate',
                'uniform bound arguments still need actual all-prime arithmetic, not numerical trends'],
            possible_next_production=dict(status='PROPOSED_NOT_IMPLEMENTED',
                kind='slower_vanishing_rational_twist',
                exponent='beta_N=ceil(a*L(N)^theta)/L(N), rational a>0,0<theta<1',
                reason='beta_N->0 while beta_N*logN->infinity; both local rate and global bound need proof',
                bound_proved=False),
            no_operator_class_blacklisted_beyond_proved_scope=True,
            additional_norms_evaluated=0, original_F_and_centered_mobius_bounds='OPEN',
            whole_signed_bound_proved=False,RH_proved=False,RH_refuted=False)
        write(OUT/'grammar_feedback.json',feedback)
        write(OUT/'next_search_input.json',feedback)
        rate_caps=sum(r['strongest_target_rate_obstruction'] is not None for r in rate_frontier['rows'])
        cutoff_refuted=sum(r['certificate']['status']=='REFUTED_ALL_INTEGER_VANISHING_FORCING' for r in cutoff_frontier)
        report=dict(status='FLOOR_AUXILIARY_BOUND_CLAIMS_ANALYTICALLY_REVIEWED',
            selected_rule_count=len(merged),advertised_bounds_refuted=sum(r['advertised_all_integer_bound']=='analytically_refuted' for r in merged),
            selected_rate_refutations=sum(r['logarithmic_rate_gate']=='analytically_refuted' for r in merged),
            selected_uniform_cutoff_refutations=sum(r['cutoff_shape_gate']=='REFUTED_ALL_INTEGER_VANISHING_FORCING' for r in merged),
            frontier_family_count=len(grammar['recipes']),families_with_licensed_target_rate_caps=rate_caps,
            frontier_cutoff_refutations=cutoff_refuted,
            target_rate_refutations_by_eta={eta:sum(eta in r['refuted_etas'] for r in rate_frontier['rows']) for eta in grammar['log_etas']},
            prior_finite_bounds_verified=parent_report['final_bound_status_counts']['verified_at_this_support'],
            additional_norms_evaluated=0,source_arrays_read=False,old_studies_rerun=0,
            selected_rate_operations=selected_meter.operations,frontier_rate_operations=frontier_meter.operations,
            independent_rate_operations=replay_meter.operations,cutoff_operations=cutoff_meter.operations,
            cutoff_replay_operations=cutoff_replay.operations,
            parent_frozen_files=parent_files,followup_frozen_files=len(FILES),
            elapsed_seconds=time.monotonic()-started,
            development_receipts={name:read(ROOT/name) for name in RECEIPTS},
            whole_signed_bound_proved=False,RH_proved=False,RH_refuted=False)
        validate_parent()
        if not all((ROOT/name).read_bytes()==(OUT/'source_snapshot'/name).read_bytes() for name in FILES):
            raise ValueError('frozen proof followup source changed')
        write(OUT/'report.json',report)
        print(json.dumps({k:v for k,v in report.items() if k!='development_receipts'}),flush=True)
    except Exception as error:
        write(OUT/'failure.json',dict(type=type(error).__name__,message=str(error),elapsed_seconds=time.monotonic()-started))
        raise


if __name__=='__main__':
    main()
