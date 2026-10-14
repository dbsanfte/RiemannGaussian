"""Publish post-selection exact obstructions without changing the frozen pilot."""
from copy import deepcopy
from fractions import Fraction as Q
import json
from pathlib import Path
import time

import floor_residual_recovery_review_043 as REVIEW


ROOT = Path(__file__).resolve().parent
PILOT = ROOT/'floor-residual-results/pilot-001'
OUT = PILOT/'analytical_followup_001'
FILES = ['floor_residual_recovery_review_043.py', 'test_floor_residual_recovery_review_043.py',
         'floor_residual_recovery_review_043_development.json', 'FLOOR_RESIDUAL_RECOVERY_REVIEW_043.txt',
         'publish_floor_residual_review_043.py']


def read(path):
    return json.loads(path.read_text())


def write(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('x') as stream:
        json.dump(obj, stream, indent=2, sort_keys=True)
        stream.write('\n')


def check_cell_witness(witness):
    """Direct identity checks independent of the Gaussian witness generator."""
    n = witness['index']
    entries = [(row['k'], Q(row['alpha'])) for row in witness['cells']]
    if sum(k*a for k, a in entries) != 0:
        raise ValueError('infinite higher-index tail is not annihilated')
    for j in range(2, n+1):
        if sum(a*Q(k % j, j) for k, a in entries) != -int(j == n):
            raise ValueError('finite coefficient elimination failed')
    if sum(a for _, a in entries) != Q(witness['constant']):
        raise ValueError('unit coefficient is not preserved')
    if sum(a*a*k*(k+1) for k, a in entries) != Q(witness['denominator']):
        raise ValueError('wrong Cauchy price')


def replay_obstruction(row, field, replay_meter):
    if row is None:
        return
    check_cell_witness(row['witness'])
    REVIEW.verify_witness(row['witness'], replay_meter)
    lo, hi = map(Q, row['gap'])
    distance = lo if lo > 0 else -hi if hi < 0 else Q(0)
    if distance <= 0 or distance*distance/Q(row['witness']['denominator']) != Q(row[field]):
        raise ValueError('positive liminf inequality failed')
    for key in ('coefficient_limit', 'child_coefficient_limit', 'parent_coefficient_limit'):
        if row.get(key) is not None:
            REVIEW.verify_root_bracket(row[key]['root_bracket'], replay_meter)


def main():
    started = time.monotonic()
    pilot = read(PILOT/'report.json')
    if pilot['status'] != 'FLOOR_RESIDUAL_GLOBAL_NORMS_VERIFIED_FAMILY_CONVERGENCE_OPEN':
        raise ValueError('completed unmodified043 norm study required')
    selected = read(PILOT/'selected_families.json')
    spec = read(PILOT/'run_spec.json')
    recipes = spec['grammar']['recipes']
    by_id = {recipe['id']:recipe for recipe in recipes}
    if any(by_id.get(recipe['id']) != recipe for recipe in selected['recipes']):
        raise ValueError('selected recipes must be exact frozen grammar members')
    OUT.mkdir(parents=True, exist_ok=False)
    try:
        for name in FILES:
            dest = OUT/'source_snapshot'/name
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes((ROOT/name).read_bytes())
        write(OUT/'run_spec.json', dict(schema='floor-recovery-review-run-v1',
            purpose='post-selection proof filtering, no candidate reselection or new norm data',
            witness_indices=[2,16], root_bracket_bits=24,
            selected_input=str((PILOT/'selected_families.json').relative_to(ROOT)),
            full_grammar_input=str((PILOT/'run_spec.json').relative_to(ROOT)),
            scope='these fixed recipes only; all-N local necessary conditions are not sufficient for convergence',
            original_F_and_centered_mobius_bounds='OPEN', memory_limit_gib=16,
            source_arrays_read=False, new_norms_evaluated=False, hashes_created=False))
        selected_meter = REVIEW.Meter(cap=50_000_000)
        reviewed = REVIEW.review_selected(selected, max_index=16, bits=24, meter=selected_meter)
        replay_meter = REVIEW.Meter(cap=50_000_000)
        for review in reviewed['reviews']:
            replay_obstruction(review['strongest_target_witness'], 'liminf_energy_lower', replay_meter)
            replay_obstruction(review['strongest_forcing_witness'], 'liminf_forcing_energy_lower', replay_meter)
        write(OUT/'selected_obstructions.json', reviewed)
        frontier_meter = REVIEW.Meter(cap=100_000_000)
        witnesses, frontier = {}, []
        for recipe in recipes:
            review = REVIEW.review_recipe(recipe, max_index=16, bits=24, meter=frontier_meter, witnesses=witnesses)
            witness = review['strongest_target_witness']
            replay_obstruction(witness, 'liminf_energy_lower', replay_meter)
            frontier.append(dict(recipe=recipe, status=review['target_convergence_status'],
                                 strongest_target_witness=witness,
                                 all_scanned_indices=list(range(2,17)),
                                 open_does_not_mean_viable_or_convergent=True))
        refuted = [row for row in frontier if row['status'] == 'analytically_refuted']
        remaining = [row for row in frontier if row['status'] == 'OPEN']
        write(OUT/'proof_filtered_frontier.json', dict(schema='floor-recovery-frontier-v1',
            recipes=frontier, refuted_count=len(refuted), remaining_open_count=len(remaining),
            observations_after_pilot=0, candidate_selection_replayed=False,
            next_run_must_freeze_new_selection_and_fresh_final_supports=True, RH_proved=False))
        feedback = dict(schema='floor-recovery-grammar-feedback-v1',
            necessary_condition='every fixed coefficient c_n(N) must tend to -mu(n) when target norm tends to0',
            witness_mechanism='solve finite rational cell equations, annihilate all higher-index slopes, apply weighted Cauchy',
            selected_obstructions=[dict(family=r['recipe']['id'], q=r['rule']['q'], b=r['rule']['b'],
                target_status=r['target_convergence_status'], forcing_status=r['forcing_bound_status'],
                target_liminf_lower=None if r['strongest_target_witness'] is None else r['strongest_target_witness']['liminf_energy_lower'],
                forcing_liminf_lower=None if r['strongest_forcing_witness'] is None else r['strongest_forcing_witness']['liminf_forcing_energy_lower'])
                for r in reviewed['reviews']],
            exact_fixed_recipe_failures_only=True, arithmetic_channels_not_globally_blacklisted=True,
            next_constructions_implemented=False,
            next_constructions=[
                dict(kind='taper_difference', formula='c_n=-mu(n)*W0(n/N)+a(n)*(W1(n/N)-W2(n/N))',
                     condition='W0(0)=W1(0)=W2(0)=1, continuity and exact rounding limits proved',
                     proved_scope='local coefficient compatibility only; no global norm upper bound'),
                dict(kind='vanishing_signed_amplitude', formula='c_n=-mu(n)*W0(n/N)+N^(-delta)*a(n)*W1(n/N)',
                     condition='fixed delta>0; finite limits of taper weights',
                     proved_scope='local coefficient compatibility only; all-scale signed tail remains unpaid'),
                dict(kind='growing_exact_head_repair', formula='replace c_n by -mu(n) for n<=floor(N^theta)',
                     condition='fixed theta>0; preserve finite pure-floor program',
                     proved_scope='necessary local constraints only; neither global convergence nor forcing decay established')],
            numerical_diagnostic=dict(signed_mechanism_counts=pilot['signed_mechanism_counts'],
                                      scope='observed finite bounds only; no all-scale mechanism is inferred'),
            imported_rate_guard='geometric-in-log-support energy contraction excluded; eta>1 logarithmic norm decay excluded',
            next_proof_goal='find and uniformly bound the signed tail/forcing of a locally compatible growing recipe',
            circularity_guard='neither RH nor target norm convergence may discharge the forcing estimate',
            existing_signed_core_bound_proved=False, RH_proved=False)
        write(OUT/'grammar_feedback.json', feedback)
        continuation = deepcopy(read(PILOT/'next_search_input.json'))
        continuation['authoritative_parent'] = str((PILOT/'next_search_input.json').relative_to(ROOT))
        continuation['floor_residual_route'].update(
            proof_search_input=str((OUT/'grammar_feedback.json').relative_to(ROOT)),
            post_selection_status='SELECTED_FIXED_FAMILIES_REFUTED_BY_EXACT_COEFFICIENT_LIMITS',
            proof_filtered_frontier=str((OUT/'proof_filtered_frontier.json').relative_to(ROOT)),
            necessary_condition_survivors=len(remaining),
            uniform_family_convergence_proved=False, original_target_replaced=False)
        write(OUT/'next_search_input.json', continuation)
        report = dict(status='FLOOR_RESIDUAL_SELECTED_FAMILIES_REFUTED_LOCAL_RECOVERY_GATE_VERIFIED',
            selected_rules_reviewed=len(reviewed['reviews']),
            selected_targets_refuted=sum(r['target_convergence_status'] == 'analytically_refuted' for r in reviewed['reviews']),
            selected_forcing_claims_refuted=sum(r['forcing_bound_status'] == 'analytically_refuted' for r in reviewed['reviews']),
            total_frozen_recipes=len(recipes), recipes_refuted=len(refuted), recipes_remaining_open=len(remaining),
            selected_review_counts=selected_meter.counts(), frontier_review_counts=frontier_meter.counts(),
            certificate_replay_counts=replay_meter.counts(),
            prior_norm_evaluations_rerun=0, new_norms_evaluated=0,
            full_signed_core_bound_proved=False, family_convergence_proved=False, RH_proved=False, RH_refuted=False,
            elapsed_seconds=time.monotonic()-started,
            development_receipt=read(ROOT/'floor_residual_recovery_review_043_development.json'))
        for name in FILES:
            if (ROOT/name).read_bytes() != (OUT/'source_snapshot'/name).read_bytes():
                raise ValueError('review source changed: '+name)
        write(OUT/'report.json', report)
        print(json.dumps({key:value for key,value in report.items() if key != 'development_receipt'}), flush=True)
    except Exception as error:
        write(OUT/'failure.json', dict(type=type(error).__name__, message=str(error), elapsed_seconds=time.monotonic()-started))
        raise


if __name__ == '__main__':
    main()
