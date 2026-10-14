"""Publish the actual080 evidence without elevating finite checks to theorems."""
import json
import re
import time
from fractions import Fraction as Q

import run_mobius_symbolic_cover_080 as RUN
import mobius_full_mode_gate_080 as GATE
import check_mobius_full_mode_gate_080 as CHECK
from run_fractional_prime_kernel_051 import write as write_new

POST_FILES = ['mobius_full_mode_gate_080.py', 'test_mobius_full_mode_gate_080.py',
    'mobius_full_mode_gate_search_080_development.json', 'check_mobius_full_mode_gate_080.py',
    'test_check_mobius_full_mode_gate_080.py', 'mobius_full_mode_gate_checker_080_development.json',
    'MOBIUS_FULL_MODE_GATE_CHECK_SCOPE_080.txt', 'MOBIUS_FULL_CHANNEL_MODE_REVIEW_080.txt',
    'audit_mobius_symbolic_cover_postrun_080.py', 'mobius_symbolic_cover_postrun_audit_080.json',
    'mobius_symbolic_cover_independent_full_mode_audit_080.json',
    'MOBIUS_SYMBOLIC_COVER_POSTREVIEW_080.txt', 'publish_mobius_symbolic_cover_080.py']


def write(path, value):
    if path.exists():
        if json.loads(path.read_text()) != value:
            raise ValueError('preserve differing publication artifact '+str(path))
    else:
        write_new(path, value)


def affine(pair):
    a, b = map(Q, pair)
    if not b:
        return str(a)
    term = 'L' if b == 1 else '-L' if b == -1 else str(b)+'*L'
    return (str(a)+'+' if a else '')+term


def formula(ray):
    return ' + '.join('('+affine(pair)+')*D'+str(i) for i, pair in enumerate(ray) if any(map(Q, pair)))


def receipt_totals(receipts):
    totals = dict(distinct_tests=0, test_executions=0, successful_test_executions=0, failed_attempts=0)
    for receipt in receipts:
        if receipt['status'] != 'PASS':
            raise ValueError('development incomplete')
        totals['distinct_tests'] += receipt['distinct_tests']
        for attempt in receipt['attempts']:
            status = attempt.get('status', attempt.get('outcome'))
            if status not in ('PASS', 'FAIL'):
                raise ValueError('unknown development attempt status')
            totals['test_executions'] += attempt['tests_run']
            totals['successful_test_executions'] += len(re.findall(r'\.\.\. ok\s*$', attempt['output'], re.M))
            totals['failed_attempts'] += status == 'FAIL'
    return totals


def checked_gate(meta, gamma, ray, logspec, rho):
    active = [i for i in range(10) if i not in meta['inactive_admissions'][gamma]['indices']]
    if active != [1, 7, 8, 9]:
        raise ValueError('full-mode gate requires admitted active channel domain')
    RUN.require(meta['source_binding'], 'VERIFIED_FIXED_KERNEL')
    RUN.require(meta['norm_admission'], 'VERIFIED_UNIFORM_COEFFICIENT_NORM')
    full = GATE.propose_full_mode(meta['fixed_kernel'], meta['primes'], gamma, ray, logspec, rho)
    full_admission = CHECK.verify_full_mode(meta['fixed_kernel'], meta['primes'], gamma, ray,
        logspec, rho, full['certificate'])
    if full_admission['status'] not in ('VERIFIED_FULL_MODE_OBSTRUCTION', 'UNPAID'):
        raise ValueError('postrun full-mode admission failed '+str(full_admission))
    second, second_admission = None, None
    if full_admission['status'] == 'UNPAID':
        second = GATE.propose_second_mode(meta['fixed_kernel'], meta['primes'], gamma, ray, logspec)
        if second['status'] == 'SECOND_MODE_OBSTRUCTION_PROPOSAL':
            second_admission = RUN.require(CHECK.verify_second_mode(meta['fixed_kernel'], meta['primes'],
                gamma, ray, logspec, second['certificate']), 'VERIFIED_SECOND_MODE_OBSTRUCTION')
    return dict(ray=ray, full_proposal=full, full_admission=full_admission,
        second_proposal=second, second_admission=second_admission,
        obstructed=full_admission['status'] == 'VERIFIED_FULL_MODE_OBSTRUCTION' or second_admission is not None,
        checker_operations=full_admission['ops']+(second_admission['ops'] if second_admission else 0))


def analytic_feedback(out, candidates, metadata):
    start = time.monotonic()
    rho = GATE.rho_envelope()
    rho_admission = RUN.require(CHECK.verify_rho_envelope(rho), 'VERIFIED_DICKMAN_ENVELOPE')
    selected, families = [], []
    for candidate in candidates:
        meta = metadata[candidate['source_id']]
        gates = [checked_gate(meta, candidate['gamma'], ray, candidate['logspec'], rho)
                 for ray in candidate['frame']['rays']]
        selected.append(dict(id=candidate['id'], source_id=candidate['source_id'], gamma=candidate['gamma'],
            leaves=gates, all_leaves_obstructed=all(x['obstructed'] for x in gates),
            arithmetic_residual_refuted=False))
    # Apply the new proof rules to the ALREADY SAVED generated grammar,
    # without generating candidates or querying an arithmetic source again.
    for path in sorted(out.glob('proposal_*_promoted.json')):
        RUN.check_stage(start)
        data = json.loads(path.read_text())
        meta, gamma = metadata[data['source_id']], data['gamma']
        logspec = GATE.S.log_spec(str((3-2*Q(gamma))/(2*Q(gamma))))
        frames = [dict(frame_index=frame['index'], gate=checked_gate(meta, gamma, frame['rays'][0], logspec, rho))
                  for frame in data['all_frames']]
        families.append(dict(source_id=data['source_id'], gamma=gamma, proposal_file=path.name,
            frames=frames, generated_frames=len(frames), obstructed_frames=sum(x['gate']['obstructed'] for x in frames),
            entire_generated_family_obstructed=all(x['gate']['obstructed'] for x in frames)))
    return dict(rho_certificate=rho, rho_admission=rho_admission, selected=selected, promoted_families=families,
        selected_leaves_obstructed=sum(x['obstructed'] for item in selected for x in item['leaves']),
        promoted_frames=sum(x['generated_frames'] for x in families),
        obstructed_promoted_frames=sum(x['obstructed_frames'] for x in families),
        first_mode_frame_obstructions=sum(x['gate']['full_admission']['status'] == 'VERIFIED_FULL_MODE_OBSTRUCTION'
            for family in families for x in family['frames']),
        second_mode_frame_obstructions=sum(x['gate']['second_admission'] is not None for family in families for x in family['frames']),
        checker_operations=rho_admission['ops']+sum(x['checker_operations'] for item in selected for x in item['leaves'])+
            sum(x['gate']['checker_operations'] for family in families for x in family['frames']),
        elapsed_seconds=time.monotonic()-start, scientific_mobius_queries=0,
        finite_threshold_supplied=False, arithmetic_residual_refuted=False,
        formal_analytic_theorem_prover_checked=False, RH_proved=False)


def main():
    root, out = RUN.ROOT, RUN.OUT
    counts = RUN.validate_parent()
    for name in RUN.FILES:
        if (root/name).read_bytes() != (out/'source_snapshot'/name).read_bytes():
            raise ValueError('preserve080 '+name)
    if (out/'failure.json').exists():
        raise ValueError('failed scientific attempt cannot be published as complete')
    report = json.loads((out/'report.json').read_text())
    if report['status'] != 'SYMBOLIC_COMPLEMENT_SEARCH_COMPLETE':
        raise ValueError('science is not complete')
    candidates = json.loads((out/'frozen_candidates.json').read_text())['candidates']
    draw = json.loads((out/'validation_draw.json').read_text())
    known = json.loads((out/'known_parent_inventory.json').read_text())
    if set(draw['parents']) & set(known['parents']):
        raise ValueError('fresh parent overlaps known inventory')
    details = []
    for candidate in candidates:
        if candidate != json.loads((out/('candidate_'+candidate['id']+'.json')).read_text()):
            raise ValueError('frozen candidate changed')
        result = next(x for x in report['results'] if x['id'] == candidate['id'])
        checks = json.loads((out/('validation_checks_'+candidate['id']+'.json')).read_text())
        for key, status in [('certified', 'CERTIFIED_FINITE'), ('refuted', 'REFUTED_FINITE'), ('unresolved', 'UNRESOLVED_INTERVAL')]:
            actual = sum(c['status'] == status for leaf in checks['leaves'] for c in leaf['checks'])
            if result[key] != actual or checks[key] != actual:
                raise ValueError('finite outcome count mismatch')
        if len(checks['leaves']) != 2 or any(sorted(c['u'] for c in leaf['checks']) != draw['parents'] for leaf in checks['leaves']):
            raise ValueError('incomplete validation leaf coverage')
        RUN.require(candidate['cover_admission'], 'VERIFIED_CONDITIONAL_COVER')
        for witness in candidate['noncircularity']:
            RUN.require(witness['admission'], 'VERIFIED_NONCIRCULARITY')
        if candidate['mode'] == 'promoted':
            RUN.require(candidate['promotion_admission'], 'VERIFIED_LEADING_MODE_ANNIHILATION')
        details.append(dict(id=candidate['id'], source_id=candidate['source_id'], mode=candidate['mode'],
            q=candidate['q'], gamma=candidate['gamma'], log_argument=candidate['logspec']['argument'],
            formulas=[formula(ray) for ray in candidate['frame']['rays']], kappas=candidate['kappas'],
            conditional_price=candidate['certificate']['price'], **{k: result[k] for k in ('certified', 'refuted', 'unresolved', 'finite_status')},
            promotion=candidate['promotion_admission'], uniform_signed_leaf_bounds_proved=False))
    post = {name: (root/name).read_bytes() for name in POST_FILES}
    receipts = [json.loads((out/'source_snapshot'/name).read_text()) for name in RUN.FILES if name.endswith('_development.json')]
    receipts += [json.loads(content) for name, content in post.items() if name.endswith('_development.json')]
    tests = receipt_totals(receipts)
    (out/'postrun_snapshot').mkdir(exist_ok=True)
    for name, content in post.items():
        target = out/'postrun_snapshot'/name
        if target.exists():
            if target.read_bytes() != content:
                raise ValueError('preserve differing postrun source '+name)
        else:
            with target.open('xb') as f:
                f.write(content)
    metadata = json.loads((out/'source_metadata.json').read_text())
    modes = analytic_feedback(out, candidates, metadata)
    if modes['selected_leaves_obstructed'] != 2*len(candidates):
        raise ValueError('selected complete-mode coverage disagrees with independent postreview')
    for item in details:
        item['both_uniform_signed_leaf_bounds_obstructed'] = True
    write(out/'postrun_full_modes.json', modes)
    next_input = json.loads((out/'next_search_input.json').read_text())
    next_input.update(schema='full-channel-remainder-bound-feedback-v1', proved_full_signature=dict(
        coordinates=[1, 7, 8, 9], signature=['-1', 'rho0', '1-L-rho0', 'L'],
        rho0='Dickman_rho(3/gamma-1)', log_symbol='L=log((3-2gamma)/(2gamma))', domain='1/2<gamma<=2/3',
        rho_certificate_file='postrun_full_modes.json', known_second_mode='pure L*D1+D9 has nonzero u/log(u)^2 coefficient for both fixed sources'),
        selected_method_obstructions=modes['selected'], excluded_promoted_families=[{k: v for k, v in family.items() if k != 'frames'}
            for family in modes['promoted_families']],
        priority='Search constructions controlling the complete coupled signed remainder, retaining cancellations between channels and scales.',
        unpaid='complete joint signed remainder/recurrence bound and original source/head/core/RH transfer; selected separate covariance leaves are ruled out',
        next_mechanisms=['scale-dependent coefficients with an exact transformation and remainder bound',
            'joint auxiliary recurrences retaining cross terms between complementary leaves',
            'least-prime recursions with paid signed child-correlation estimates'],
        first_mode_nullspace_is_necessary_not_sufficient=True,
        new_Dickman_symbol_alone_is_not_a_bound=True,
        analytic_rule_dependencies=['MOBIUS_FULL_CHANNEL_MODE_REVIEW_080.txt', 'MOBIUS_FULL_MODE_GATE_CHECK_SCOPE_080.txt'],
        exact_obligations=[dict(id=c['id'], source_id=c['source_id'], q=c['q'], gamma=c['gamma'],
            logspec=c['logspec'], rays=c['frame']['rays'], kappas=c['kappas'], target=c['frame']['target'],
            bound='(a.D)^2<=kappa*u^(q-1)*(a^T B a) for all integeru>=12600',
            original_complete_target_not_refuted=True) for c in candidates])
    write(out/'postrun_next_search_input.json', next_input)
    failed = sum(x['refuted'] > 0 for x in details)
    finite = sum(x['finite_status'] == 'FINITE_ONLY' for x in details)
    ambiguous = sum(x['finite_status'] == 'UNRESOLVED_INTERVAL' for x in details)
    outcomes = dict(status='PUBLISHED_SYMBOLIC_COMPLEMENT_RESULTS', details=details, tests=tests,
        candidates_with_refutations=failed, finite_only_candidates=finite, unresolved_candidates=ambiguous,
        selected_leaves_obstructed=modes['selected_leaves_obstructed'],
        promoted_frames_obstructed=modes['obstructed_promoted_frames'],
        uniform_correlation_proved=False, uniform_residual_bound_proved=False, RH_proved=False)
    write(out/'published_results.json', outcomes)
    result_lines = []
    for x in details:
        result_lines += [x['id']+': gamma='+x['gamma']+', L=log('+x['log_argument']+'), '+x['finite_status'],
            '  A = '+x['formulas'][0], '  B = '+x['formulas'][1],
            '  kappa='+', '.join(x['kappas'])+'; certified='+str(x['certified'])+', refuted='+str(x['refuted'])+', ambiguous='+str(x['unresolved'])]
    text = '''CURRENT CONTINUATION: SYMBOLIC COMPLEMENT CONSTRUCTION SEARCH080

The active objective remains all-scale signed arithmetic control with a valid
RH transfer. It is not achieved. See stage080 published_results.json,
postrun_next_search_input.json and the independent postreview for current evidence.

What changed
The detector reads079's exact failed covariance obligation and proved1/9
nuisance-mode signature as generation inputs. It enumerates rational rays
of support<=3 and symbolic promotions of support<=4, retaining other channels.
The second leaf is the exact affine complement of the full active target.
Both leaves require occupied-cell noncircularity witnesses and independent
finite inequality checks. The complete generated bank and all exclusions
are saved. This searches arithmetic constructions and conditional arguments,
not merely a larger fitted constant for the same obstructed leaf.

The shared logarithm has an exact32-term rational series/tail enclosure.
Promotion solves the supported signature(-1,L); it does NOT establish full
leading-mode cancellation when other channels are present. The new complete
mode and lower-logarithmic obstructions below rule out the selected separate
leaf bounds. The joint signed remainder remains uncontrolled. Structural
obstructions are applied only within their proved domain.

Sources and conditional scope
q1_p16=G andq1_p04=G+(3547/8192)G(u//3), with fixedP={2,3,5,7},
G(u)=M(u//8)-M(u//10)-M(u//4)+M(u//5). The vectorD is the change in
factor/least-prime category sums fromh=floor(u/2) tou, on shared physical
integer cells. The paid coefficient norm, inactive coordinates and complete
small-scale residual-energy base are inherited from079.
Every claimed cover price is conditional on both all-scale covariance
inequalities S_a^2<=kappa*u^(q-1)*Q_a. A fixedq>1 alone is not RH.
Original source/head/core/full-parameter/RH-transfer obligations are open.

Actual finite experiment
'''+f'''{report['generated_frames']} generated frames over{report['source_mode_gamma_jobs']} jobs;
{report['structurally_obstructed_frames']} frames excluded by proved full-leaf modes.
{report['discovery_parents']} reused079 discovery parents, with first4 admissible frames
per source/gamma/mode/q exactly checked; no global-optimum claim.
{len(details)} candidates frozen BEFORE validation draw; {failed} have finite
refutations, {finite} are finite-only survivors, {ambiguous} are interval-unresolved.
'''+f'''{report['fresh_validation_parents']} fresh parent cases exclude all3360 registered076/
078/079 parent rows. Both endpoint values may still lie in known arithmetic.
{report['independently_reconstructed_cell_rows']} new complete cell rows are independently
reconstructed AND each parent/half residual is bound to an independent mu
prefix and original unfolded source. Draws include irregular scales and
neighbors of first least-prime-cutoff prime-entry boundaries. The other two
cutoff boundaries are not exhaustively covered. The underlying mu horizon
remains1,310,720; maximum parent5,242,880. No new prime-prefix horizon.

'''+ '\n'.join(result_lines)+f'''

Postrun analytic feedback: complete modes, not only the1/9 projection
The reviewed least-prime recursion and quantitative Mertens theorem give
the FULL leading signature[-1,rho0,1-L-rho0,L], rho0=rho(3/gamma-1),
on coordinates[1,7,8,9]. Exact64-panel rational-log bounds certify
0<rho0<3/50 for this pilot domain. The total target has signature0.
All{modes['selected_leaves_obstructed']} selected leaves are independently ruled out as
uniform covariance bounds for EVERY finite kappa and EVERY1<=q<2.
For baseline e7 and its complement, strict Dickman positivity proves the
nonzero mode even though a closed numerical enclosure touches0.

Rechecking the saved generated promoted grammar, without mu queries, rules
out{modes['obstructed_promoted_frames']}/{modes['promoted_frames']} frames:
{modes['first_mode_frame_obstructions']} by their full first mode and
{modes['second_mode_frame_obstructions']} pure-pair cases by a nonzero SECOND logarithmic mode.
The latter uses quantitative PRIME PNT and the exact folded moment
 Tfold=delta*(sum b_d*(1+log(d/4))/d - mass*sum_p logp/(p-1)).
For L*D1+D9 the coefficient of u/log²u is-Tfold/[2*(1-2gamma/3)].
It is nonzero for both fixed sources. Lower-log terms are therefore a real
obstruction here, not merely a missing proof label. No effective finite
threshold or lower bound for the complete source residual follows.
These are reviewed analytic derivations plus independent exact certificate
arithmetic, with primary theorem imports explicitly linked in the review.
They are not a formal theorem-prover proof of those analytic imports.

Interpretation and next search
Finite failures refute these calibrated local inequalities, not the signed
residual or RH. The new all-constant mode obstructions additionally rule out
the current promoted grammar, including the pure leading-mode annihilator.
Next constructions must control the coupled signed remainder with an exact
scale-dependent transformation or joint auxiliary recurrence. Preserve
cross terms between complementary leaves. A new Dickman coefficient that
only annihilates the first mode would still leave the lower-order problem.
The saved numerical log²/log³ probes remain heuristic; the separate pure-pair
second-mode theorem is proved under its explicitly named analytic imports.

Resources and preservation
'''+f'''Three workers/native threads1, {report['elapsed_seconds']:.3f}s; sampled parallel
RSS{report['sampled_parallel_rss_peak_bytes']}B, conservative process-peak sum
{report['conservative_sum_process_peaks_bytes']}B; authorized16GiB and7200s.
Constructor work proxy{report['constructor_operations']}, checker counter
{report['checker_operations']}; these are not CPU-cycle measurements.
Postrun mode checks:{modes['elapsed_seconds']:.3f}s,{modes['checker_operations']} checkeroperations,
zero mu/source queries. Independent artifact audit reconstructs all3312
saved leaf S/Q polynomials and both-leaf source recombination from080 cells.
{tests['distinct_tests']} distinct new tests, {tests['test_executions']} executions,
{tests['successful_test_executions']} successful test executions. All current tests pass;
{tests['failed_attempts']} failed development attempt retained (corrected synthetic test
over-prescribed a winning formula). No old science/test suite replay or hashes.
Sol6.1 agents supplied independent checker and substantial proof/workflow
and postrun reviews. Preserve{sum(counts)} older +{len(RUN.FILES)} pre-run080
+{len(POST_FILES)} postrun080={sum(counts)+len(RUN.FILES)+len(POST_FILES)} frozen files by direct byte comparison.
Root continuation pointers advance; archived historical handoffs stay intact.
The RH goal remains ACTIVE and unfinished.
'''
    for path in (out/'HANDOFF.txt', root/'MOBIUS_SYMBOLIC_COVER_HANDOFF.txt'):
        if path.exists():
            if path.read_text() != text:
                raise ValueError('preserve differing handoff')
        else:
            with path.open('x') as f:
                f.write(text)
    previous = json.loads((RUN.PRIOR.OUT/'publication_integrity.json').read_text())
    pointers = previous['continuation_pointers_updated']+['MOBIUS_SCALE_FLUX_HANDOFF.txt']
    for name in pointers:
        (root/name).write_text('Latest continuation: MOBIUS_SYMBOLIC_COVER_HANDOFF.txt\n\n'
            '080 completed feedback-generated rational/logarithmic complement searches and fresh-parent validation.\n'
            'The selected separate-leaf bounds are ruled out; joint signed control and RH transfer remain open.\n'
            'Preserve historical artifacts; use the exact remaining bounds as further construction inputs.\n')
    integrity = dict(status='PUBLISHED_SYMBOLIC_COMPLEMENT_RESULTS', prior_frozen_counts=counts,
        pre_run_files=RUN.FILES, postrun_files=POST_FILES, total_frozen_files=sum(counts)+len(RUN.FILES)+len(POST_FILES),
        continuation_pointers_updated=pointers, tests=tests, historical_handoffs_unchanged=True,
        selected_leaves_obstructed=modes['selected_leaves_obstructed'], promoted_frames_obstructed=modes['obstructed_promoted_frames'],
        hashes_used=False, RH_proved=False)
    write(out/'publication_integrity.json', integrity)
    RUN.validate_parent()
    print(json.dumps(dict(status=integrity['status'], frozen_files=integrity['total_frozen_files'],
        candidates=len(details), refuted=failed, finite_only=finite, tests=tests), sort_keys=True))


if __name__ == '__main__': main()
