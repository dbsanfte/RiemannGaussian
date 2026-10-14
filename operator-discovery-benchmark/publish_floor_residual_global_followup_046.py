"""Apply a reviewed global rate obstruction to saved 045 evidence only."""
from copy import deepcopy
from fractions import Fraction as Q
from pathlib import Path
import time

import floor_residual_global_rate_guard_046 as G
import check_floor_residual_global_rate_guard_046 as CHECK
import run_floor_residual_045_recovery as NUM

ROOT = Path(__file__).resolve().parent
PILOT = NUM.FAILED
PARENT = NUM.OUT
OUT = PILOT / 'analytical_followup_001'
RECEIPTS = ['floor_residual_global_rate_guard_046_development_receipt.json',
            'check_floor_residual_global_rate_guard_046_development.json',
            'floor_residual_global_followup_046_development.json']
FILES = ['floor_residual_global_rate_guard_046.py', 'check_floor_residual_global_rate_guard_046.py',
         'test_floor_residual_global_rate_guard_046.py', 'test_check_floor_residual_global_rate_guard_046.py',
         'MOVING_PROFILE_GLOBAL_RATE_REVIEW_046.txt', 'MOVING_PROFILE_GLOBAL_RATE_SCOPE_046.txt',
         'MOVING_PROFILE_PRIME_DILATION_REVIEW_046.txt',
         'publish_floor_residual_global_followup_046.py', 'test_floor_residual_global_followup_046.py',
         'floor_residual_global_followup_protocol_046.txt'] + RECEIPTS
read, write, emit = NUM.read, NUM.write, NUM.emit


def request(recipe, q, b, bound, minimum=607):
    return dict(recipe=deepcopy(recipe), q=q, b=b, bound=deepcopy(bound),
                domain=dict(kind='all_integer', minimum=minimum), rounding=deepcopy(G.ROUNDING))


def review_rule(rule, cases, meter, checker, minimum=607):
    if any(c['rule'] != rule['id'] for c in cases):
        raise ValueError('finite evidence must belong to this rule')
    statuses = {'verified_at_this_support', 'refuted_at_this_support', 'unresolved_interval'}
    if any(c['logarithmic_forcing_status'] not in statuses for c in cases):
        raise ValueError('typed finite bound status')
    req = request(rule['recipe'], rule['q'], rule['b'], rule['audit_log_bound'], minimum)
    certificate = G.build_guard(req, meter=meter)
    checked = CHECK.verify_guard(req, certificate, meter=checker)
    verified = checked if certificate['status'] == G.REFUTED else None
    if not checked['verified']:
        raise ValueError('independent global rate replay required')
    counterexamples = [deepcopy(c) for c in cases if c['logarithmic_forcing_status']=='refuted_at_this_support']
    reason = ('finite_counterexample' if counterexamples else
              'global_rate_obstruction' if verified is not None else 'OPEN')
    return dict(rule=deepcopy(rule), request=req, certificate=certificate, verification=verified,
        scope_independently_verified=True, finite_cases=deepcopy(cases), finite_counterexamples=counterexamples,
        advertised_all_integer_bound='refuted' if reason!='OPEN' else 'OPEN', rejection_reason=reason,
        all_unbounded_geometric_chains_at_this_rate='refuted' if verified is not None else 'OPEN',
        lower_rates_proved=False, convergence_of_profile='OPEN', RH_proved=False, RH_refuted=False)


def frontier(recipes, meter, checker):
    """One declared rule per bare profile; not a rerun of numerical selection."""
    rows=[]
    for recipe in recipes:
        if recipe['base']['kind'] != 'drift_mixture' or recipe['auxiliary'] is not None:
            continue
        req=request(recipe, 2, '-1', dict(A='1', eta='1'))
        certificate=G.build_guard(req, meter=meter)
        checked=CHECK.verify_guard(req, certificate, meter=checker)
        verification=checked if certificate['status']==G.REFUTED else None
        if not checked['verified']:
            raise ValueError('frontier obstruction must be independently verified')
        rows.append(dict(request=req, certificate=certificate, verification=verification, scope_independently_verified=True,
                         future_rate_ceiling=str(1-Q(recipe['base']['theta'])) if verification else None,
                         any_upper_bound_proved=False))
    return rows


def validate_parent():
    counts=NUM.validate_frozen()
    if read(PARENT/'report.json')['status']!='MOVING_SIGNED_PROFILES_AUDITED_JOINT_BOUND_OPEN':
        raise ValueError('completed finite norm parent required')
    files=list((PARENT/'source_snapshot').iterdir())
    if len(files)!=len(NUM.FILES) or any((ROOT/p.name).read_bytes()!=p.read_bytes() for p in files):
        raise ValueError('preserve frozen recovery sources')
    if G.ROUNDING != NUM.R.ARG.ROUNDING:
        raise ValueError('global proof must bind the actual finite rounding')
    return counts+[len(files)]


def main():
    started=time.monotonic()
    if OUT.exists():
        raise FileExistsError('preserve existing global proof application')
    parent_counts=validate_parent()
    for name in RECEIPTS:
        if not NUM.R.passing_receipt(read(ROOT/name)):
            raise ValueError('passing owned proof/integration receipt required: '+name)
    snapshots={name:(ROOT/name).read_bytes() for name in FILES}
    batch=read(PARENT/'final_program_batch.json')
    cases=read(PARENT/'assessment.json')['cases']
    recipes=read(PILOT/'run_spec.json')['grammar']['recipes']
    OUT.mkdir()
    (OUT/'source_snapshot').mkdir()
    for name, data in snapshots.items():
        (OUT/'source_snapshot'/name).write_bytes(data)
    try:
        write(OUT/'protocol.json', dict(schema='global-moving-rate-followup-v1',
            parent=str(PARENT.relative_to(ROOT)), selected_claims=len(batch['rules']),
            canonical_frontier_rule=dict(q=2,b='-1',A='1',eta='1',domain_minimum=607),
            frontier_scope='each saved bare drift profile; no product/taper extrapolation',
            new_norms=0, new_source_arrays=0, training_or_selection_rerun=False,
            imported_theorem='https://arxiv.org/pdf/0705.0723 Theorem1',
            mathematical_proof_review_and_typed_certificate_replay=True,
            formal_proof_assistant_used=False, hashing_used=False, RH_proved=False))
        meter=G.Meter(cap=100_000_000, seconds=600)
        checker=CHECK.Meter(cap=100_000_000)
        selected=[review_rule(rule,[c for c in cases if c['rule']==rule['id']],meter,checker)
                  for rule in batch['rules']]
        write(OUT/'selected_claims.json', dict(rows=selected,RH_proved=False,RH_refuted=False))
        catalog=frontier(recipes,meter,checker)
        write(OUT/'profile_frontier.json', dict(rows=catalog, new_norms=0, uniform_upper_bound_proved=False))
        next_targets=[]
        for row in selected:
            if row['verification'] is not None:
                theta=Q(row['rule']['recipe']['base']['theta'])
                next_targets.append(dict(family=row['rule']['family'],
                    exact_energy='||e_(qN)-b D_q e_N||^2', q=row['rule']['q'],b=row['rule']['b'],
                    necessary_eta_ceiling=str(1-theta),
                    target='prove a fixed finite C and some eta>0 at or below this ceiling, uniformly for sufficiently large N',
                    admissible_rate_is_not_a_proof=True,
                    auxiliary_target='joint critical-line transfer plus finite truncation; preserve their cross terms',
                    harmonic_component='unconditional separate envelope already available; does not close this target'))
        feedback=dict(schema='global-rate-aware-moving-bound-feedback-v1',
            authoritative_parent=str((PARENT/'next_search_input.json').relative_to(ROOT)),
            current_proof_results=str(OUT.relative_to(ROOT)), selected_claims=selected,
            retired_claims_only='the exact selected A/eta/domain bounds; the profile classes and slower rates remain OPEN',
            next_missing_estimates=next_targets,
            before_next_numerical_ranking='apply fixed-index, cutoff and046 global rate guards to each proposed bound',
            next_constructions=[
                dict(kind='prime_matched_dilation',status='derived_in_memo_not_implemented',
                     obligation='retain coprime and prime-square channels and bound the parent-profile conversion auxiliary'),
                dict(kind='joint_prime_divisor_product_discrepancy',status='derived_in_memo_not_implemented',
                     obligation='bound joint signed child/parent prefix discrepancies and the truncated-divisor tail'),
                dict(kind='two_sided_moment_synthesis',status='derived_in_memo_not_implemented',
                     obligation='negative moments do not remove the proved beta-width rate barrier')],
            reference='MOVING_PROFILE_PRIME_DILATION_REVIEW_046.txt',
            no_operator_class_blacklisted_beyond_proved_scope=True,
            theta_at_most_half='global046 guard unsupported; no promised escape',
            newly_discovered_uniform_upper_bound=False, original_F_and_centered_mobius_bounds='OPEN',
            whole_signed_bound_proved=False, RH_proved=False, RH_refuted=False)
        write(OUT/'next_search_input.json',feedback)
        report=dict(status='MOVING_PROFILE_BOUNDS_REVIEWED_GLOBAL_RATE_GUARD_ACTIVE',
            selected_claim_count=len(selected),
            selected_bound_rejection_counts={reason:sum(r['rejection_reason']==reason for r in selected)
                for reason in ('global_rate_obstruction','finite_counterexample','OPEN')},
            canonical_frontier_profiles=len(catalog),
            canonical_eta1_refuted_profiles=sum(r['verification'] is not None for r in catalog),
            canonical_frontier_unsupported_profiles=sum(r['verification'] is None for r in catalog),
            producer_operations=meter.operations,checker_operations=checker.operations,
            elapsed_seconds=time.monotonic()-started, additional_norms_evaluated=0,
            prior_frozen_source_counts=parent_counts,new_frozen_source_count=len(FILES),
            development_receipts={n:read(ROOT/n) for n in RECEIPTS},
            uniform_signed_upper_bound_proved=False,RH_proved=False,RH_refuted=False)
        validate_parent()
        if any((ROOT/name).read_bytes()!=data for name,data in snapshots.items()):
            raise ValueError('frozen046 source changed')
        write(OUT/'report.json',report)
        emit('completed',**{k:v for k,v in report.items() if k!='development_receipts'})
    except Exception as error:
        write(OUT/'failure.json',dict(type=type(error).__name__,message=str(error),
                                     elapsed_seconds=time.monotonic()-started))
        raise


if __name__=='__main__':
    main()
