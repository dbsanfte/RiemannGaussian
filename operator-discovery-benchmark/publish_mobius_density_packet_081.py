"""Publish verified auxiliary progress and the still-unpaid dense frontier."""
import json
import re
from fractions import Fraction as Q

import run_mobius_density_packet_081 as RUN
from run_fractional_prime_kernel_051 import write as write_new

POST_FILES = ['mobius_density_coverage_081.py', 'test_mobius_density_coverage_081.py',
    'mobius_density_coverage_081_development.json', 'run_mobius_density_coverage_081.py',
    'check_mobius_density_coverage_081.py', 'test_check_mobius_density_coverage_081.py',
    'mobius_density_coverage_checker_081_development.json', 'MOBIUS_DENSITY_COVERAGE_CHECK_SCOPE_081.txt',
    'audit_mobius_density_packet_081.py', 'mobius_density_packet_independent_audit_081.json',
    'mobius_density_packet_independent_audit_081_attempt_1791720548144562564.json',
    'MOBIUS_DENSITY_PACKET_ARTIFACT_AUDIT_081.txt', 'MOBIUS_DENSITY_PACKET_POSTREVIEW_081.txt',
    'publish_mobius_density_packet_081.py']


def write(path, value):
    if path.exists():
        if json.loads(path.read_text()) != value:
            raise ValueError('preserve differing publication '+str(path))
    else:
        write_new(path, value)


def tests():
    totals = dict(distinct_tests=0, test_executions=0, successful_test_executions=0, failed_attempts=0)
    files = ['mobius_density_packet_search_081_development.json', 'mobius_density_packet_checker_081_development.json',
             'mobius_density_coverage_081_development.json', 'mobius_density_coverage_checker_081_development.json']
    for name in files:
        receipt = json.loads((RUN.ROOT/name).read_text())
        if 'test_attempts' in receipt:
            attempts = receipt['test_attempts']
            if not attempts or attempts[-1]['status'] != 'PASS':
                raise ValueError('incomplete independent coverage tests')
            totals['distinct_tests'] += max(a['tests_run'] for a in attempts)
            for attempt in attempts:
                count = attempt['tests_run']
                totals['test_executions'] += count
                totals['successful_test_executions'] += count if attempt['status'] == 'PASS' and attempt['exit_code'] == 0 else 0
                totals['failed_attempts'] += attempt['status'] != 'PASS'
            continue
        if receipt['status'] != 'PASS':
            raise ValueError('incomplete development '+name)
        totals['distinct_tests'] += receipt['distinct_tests']
        for attempt in receipt['attempts']:
            count = attempt.get('tests', attempt.get('tests_run'))
            if type(count) is not int:
                raise ValueError('test count missing '+name)
            totals['test_executions'] += count
            good = len(re.findall(r'\.\.\. ok\s*$', attempt['output'], re.M))
            totals['successful_test_executions'] += good
            totals['failed_attempts'] += good < count
    totals['additional_recorded_real_kernel_integration'] = True
    totals['readonly_audit_environment_failures_are_separately_retained'] = True
    return totals


def main():
    root, out = RUN.ROOT, RUN.OUT
    counts = RUN.validate_parent()
    for name in RUN.FILES:
        if (root/name).read_bytes() != (out/'source_snapshot'/name).read_bytes():
            raise ValueError('preserve081 '+name)
    frozen = {name: (root/name).read_bytes() for name in POST_FILES}
    report = json.loads((out/'report.json').read_text())
    audit = json.loads((root/'mobius_density_packet_independent_audit_081_attempt_1791720548144562564.json').read_text())
    if audit['status'] != 'PASS' or audit['prior_byte_preserved_files'] != sum(counts) or audit['stage_byte_preserved_files'] != len(RUN.FILES):
        raise ValueError('independent saved-artifact audit required')
    coverage = json.loads((out/'coverage_proposals_081.json').read_text())
    admissions = json.loads((out/'coverage_admissions_081.json').read_text())
    if admissions['status'] != 'VERIFIED_FINITE_DENSITY_COVERAGE':
        raise ValueError('independent physical coverage required')
    checks = {r['id']: r for r in admissions['rows']}
    candidates = json.loads((out/'frozen_candidates.json').read_text())['candidates']
    if set(checks) != {c['id'] for c in candidates} or set(checks) != {c['id'] for c in coverage['rows']}:
        raise ValueError('complete selected coverage admission')
    details = []
    feedback = json.loads((out/'next_search_input.json').read_text())
    for row in coverage['rows']:
        cert, check = row['certificate'], checks[row['id']]
        if (check['status'] != 'VERIFIED_FINITE_DENSITY_COVERAGE' or check['u'] != cert['u'] or check['D'] != cert['D']
                or check['absolute_mass'] != cert['absolute_offdiagonal_coefficient_mass']
                or check['removed_mass'] != cert['removed_absolute_coefficient_mass'] or not check['prime_block_verified']):
            raise ValueError('coverage binding '+row['id'])
        candidate = next(c for c in candidates if c['id'] == row['id'])
        if candidate['program'] != row['program']:
            raise ValueError('coverage changed frozen program')
        validation = json.loads((out/('validation_'+row['id']+'.json')).read_text())
        saved = next(r['certificate'] for r in validation['rows'] if r['u'] == cert['u'])
        primal = Q(cert['untouched_prime_block']['signed_contribution'])
        if row['saved_admitted_unlinked'] != saved['unlinked'] or Q(row['other_unlinked_contribution'])+primal != Q(saved['unlinked']):
            raise ValueError('joint frontier arithmetic binding')
        details.append(dict(id=row['id'], source_id=candidate['source_id'], selection_tracks=candidate['selection_tracks'],
            memory=candidate['program']['memory'], rays=candidate['program']['rays'], epsilon=candidate['program']['epsilon'],
            eta=candidate['program']['eta'], proved_packet_exponent=candidate['certificate']['exponent'],
            proved_packet_constant=candidate['certificate']['constant'],
            calibrated_unlinked_K=candidate['discovery_unlinked_kappa'],
            finite_unlinked_refutations=validation['finite_unlinked_refutations'],
            refutation_parents=sorted(r['u'] for r in validation['rows'] if not r['unlinked_calibrated_bound_holds']),
            finite_packet_positive=validation['positive_packet_rows'], finite_packet_negative=validation['negative_packet_rows'],
            physical_coverage=cert, coverage_admission=check,
            uniform_auxiliary_packet_bound_proved=True, uniform_unlinked_bound_proved=False, RH_proved=False))
        obligation = next(o for o in feedback['obligations'] if o['id'] == row['id'])
        obligation.update(frozen_K_finite_counterexamples=details[-1]['refutation_parents'],
            exact_current_radius_target=dict(identity='U(u)=H00*P_outer(u)*(P_outer(u)-1)+V(u)',
                P_outer='number of actual primes in(floor(u/5),floor(u/4)]',
                H00=str(Q(cert['untouched_prime_block']['per_pair_signed_coefficient'])/2),
                domain='integeru withfloor(u/5)>=floor(u^eta); outside this range use exact fullU target or a complete finite base',
                required_bound='V(u)<=K*u-H00*P_outer(u)*(P_outer(u)-1), K independentofu',
                all_actual_prime_prime_pairs_in_this_block_remain_unpaid=True,
                this_is_an_exact_reduction_not_a_new_bound=True),
            finite_diagnostic_parent=cert['u'], finite_removed_absolute_mass_fraction=cert['fraction_absolute_mass_removed'])
    feedback.update(schema='joint-density-packet-frontier-feedback-v1',
        priority='Search an exact joint control for dense primitive coprime pairs, retaining actual prime/composite cross cancellation.',
        why_current_packets_do_not_close_target='Their uniform bounds control extracted sparse graphs; U retains the diagonal, omitted graphs and fractions1-w. All six calibratedU bounds fail.',
        diagnostic_scope='Exact independently checked geometry at one declared saved parent; no uniform coverage percentage or fullU lower bound claimed.',
        next_mechanisms=['joint signed averaging of squarefree-count errors across ratio labels, rather than summing their absolute errors',
            'exact full drift decompositions into paid packets, diagonal controls and proved nonpositive terms',
            'cofactor recurrences with an explicitly controlled primitiveg=1 frontier'],
        insufficient_alone=['larger fittedK', 'better constant for the same sparsepacket', 'retention fraction among onlyeligible labels'],
        formal_theorem_prover_checked=False, uniform_original_source_bound_proved=False)
    totals = tests()
    results = dict(status='PUBLISHED_GROWING_SIGNED_PACKET_RESULTS', science=report, details=details,
        tests=totals, independent_artifact_audit=audit['status'],
        coverage_resources={k: coverage[k] for k in ('constructor_operations', 'elapsed_seconds', 'peak_rss_bytes', 'diagnostic_parent')},
        independent_coverage_resources={k: v for k, v in admissions.items() if k != 'rows'},
        proved_scope='Reviewed elementary all-scale auxiliary packet bound; independent exact certificate and finite source/compiler checks.',
        uniform_unlinked_bound_proved=False, uniform_original_source_bound_proved=False, RH_proved=False)
    write(out/'postrun_next_search_input.json', feedback)
    write(out/'published_results.json', results)
    lines = []
    for row in details:
        lines.append(row['id']+': epsilon='+row['epsilon']+', eta='+row['eta']+
            ', packet exponent='+row['proved_packet_exponent']+', C approximately'+format(float(Q(row['proved_packet_constant'])), '.8g')+
            '; calibratedU failures='+str(row['finite_unlinked_refutations'])+'/'+str(report['fresh_validation_parents'])+
            '; removedabsoluteoffdiagonalmass='+format(100*float(Q(row['physical_coverage']['fraction_absolute_mass_removed'])), '.8g')+'percent')
    handoff = '''CURRENT CONTINUATION: GROWING SIGNED DENSITY PACKETS081

The RH objective remains ACTIVE and unfinished. Authoritative machine input
is stage081/postrun_next_search_input.json, with exact programs, paid packet
prices, finite U counterexamples and the unclosed actual-prime frontier.

Actual advance
The detector now proposes constructions WITH an explicit uniform argument.
It searches joint delayed energies, canonical multiplicative ratio graphs,
exact rational density balancing, and proof-derived fractional growth rates.
Original kernels remainG=M(u//8)-M(u//10)-M(u//4)+M(u//5) and
G+(3547/8192)G(u//3), represented directly without excluded-prime folds.
E(u)=R(u)^2+sum lambda*(sum a_j R(u//2^j))^2,
DeltaE=E(u)-(3/2)E(floor(u/2)). Every shared physical cross term stays joint.

For each coprime squarefree a<b<=D=floor(u^eta), exact multiplicativity
rewrites mu(ag)mu(bg) asmu(a)mu(b)mu(g)^2 when gcd(g,ab)=1.
The detector weights complete ratio graphs so their squarefree density
terms cancel EXACTLY for everyD. Restricted squarefree counting pays
 |W(u)|<=J*(Cepsilon+2)*u^(1/2+eta*(3/2+2epsilon)),
 J=2||T||entrywise1*(sum|b_d|)^2,
 2^omega(n)<=Cepsilon*n^epsilon for everypositiveintegern.
Exceptional primes and constants have independent exact certificates.
The elementary analytic argument was independently reviewed; finite source,
compiler and balance computations use independent algorithms. This is not
a formal theorem-prover verification and is not a bound for the sourceR.

The pilot enumerated17 distinct energies and33 proof-derived rational
schedules across2 sources:1122 programs with independent price admission.
The language does not restrict exponents to square/cubic/sixth roots.
Six selected constructions includeeta2/7,1/5,9/52; the9/52 construction
has the stronger packet exponent7/8. All selected packets are nonzero
on admitted data and balance both density signs; empty constructions cannot
win selection. Baseline and all generated records are retained.

Honest remaining obstruction
The exact identity isDeltaE=W+U. U includes the diagonal, all omitted
ratios, and fractions1-w of selected ratios. Its uniformU(u)<=K*u bound
remains unpaid. If paid for allpositiveintegers, it would yield the fixed
source energy boundE(u)<=4*max(0,C_W+K)*u; the source-bound baseE(1)=0
is automatic for these kernels. The full head/core/parameter/RH transfer
still needs proof. No finite calibration is promoted to this theorem.

'''+f'''{report['discovery_parents']} declared reused080 parents were discovery data.
Candidates were independently checked and frozen before drawing
{report['fresh_validation_parents']} fresh parents excluding3619 registered parents/delays.
All{report['independently_checked_finite_rows']} selected discovery/validation rows had independent original
source, complete-label, squarefree-count and signed decomposition checks.
All six calibrated U bounds failed at1420914; q1_p04_packet_2 also
failed at583331. Those failures refute thoseK values, not everyfiniteK,
the auxiliary theorem, or RH. The known mu horizon remains1,310,720.

'''+ '\n'.join(lines)+'''

Where actual prime information is still missing
At the common declared diagnostic parentu=5,116,208, independently checked
packets remove only about0.000465%-0.003272% of the absolute OFFDIAGONAL
squarefree kernel coefficient mass. This is a finite geometric measurement,
not a theorem about arithmetic cancellation or every scale.
There are18,324 actualprimes in(floor(u/5),floor(u/4)]. Every pair of
distinct primes in this band has reduced labels>D and is untouched.
Their positive signed contribution isH00*P*(P-1), approximately82u or
131u for these energies. The much smaller signed total already shows
substantial cancellation with the complement at this particular scale;
no uniform bound for that joint cancellation has been supplied.

The next input therefore exports the exact prime-block decomposition
U=H00*P_outer*(P_outer-1)+V and requires a uniform bound for the jointV
that offsets this block. It retains actual prime/composite cross terms.
Do not separately absolute-bound the large pieces or just raise finiteK.
More sparse-packet constant tuning alone does not close this frontier.

Verification and resources
'''+f'''Search ran{report['elapsed_seconds']:.3f}s on3workers/native threads1,
sampled aggregate RSS{report['sampled_parallel_rss_peak_bytes']}B,
conservative process-peak sum{report['conservative_sum_process_peaks_bytes']}B.
Main constructor/checker workproxies{report['constructor_operations']}/{report['checker_operations']}.
Coverage construction{coverage['elapsed_seconds']:.3f}s; independentcoverage
{admissions['elapsed_seconds']:.3f}s,{admissions['operations']} countedoperations.
Authorized limits16GiB and7200seconds; no new arithmetic horizon.
{totals['distinct_tests']} distinct newtests,{totals['test_executions']} executions,
{totals['successful_test_executions']} successful;{totals['failed_attempts']} failed development attempt retained
(a cache-test expectation, corrected). Separate read-only system-Python
import failures are retained in audit provenance. All final tests pass.
Sol6.1 agents supplied substantial independent checker and proof/artifact
reviews. No old science/test replay or hashes. Preserve{sum(counts)}older+
{len(RUN.FILES)}pre-run081+{len(POST_FILES)}postrun081={sum(counts)+len(RUN.FILES)+len(POST_FILES)} frozenfiles bydirectbytecomparison.
Historical archived handoffs remain intact; root continuation pointers advance.
'''
    for path in (out/'HANDOFF.txt', root/'MOBIUS_DENSITY_PACKET_HANDOFF.txt'):
        if path.exists():
            if path.read_text() != handoff:
                raise ValueError('preserve differing handoff')
        else:
            with path.open('x') as f:
                f.write(handoff)
    previous = json.loads((RUN.PRIOR.OUT/'publication_integrity.json').read_text())
    pointers = previous['continuation_pointers_updated']+['MOBIUS_SYMBOLIC_COVER_HANDOFF.txt']
    for name in pointers:
        (root/name).write_text('Latest continuation: MOBIUS_DENSITY_PACKET_HANDOFF.txt\n\n'
            '081 searched and certified growing signed auxiliary packets with rational exponents.\n'
            'All six calibrated remainder bounds failed; dense prime/composite joint control remains unpaid.\n'
            'Use the exact remaining bounds and actual-prime frontier as construction inputs. Preserve archived evidence.\n')
    (out/'postrun_snapshot').mkdir(exist_ok=True)
    for name, content in frozen.items():
        target = out/'postrun_snapshot'/name
        if target.exists():
            if target.read_bytes() != content:
                raise ValueError('preserve differing postrun snapshot')
        else:
            with target.open('xb') as f:
                f.write(content)
        if (root/name).read_bytes() != content:
            raise ValueError('postrun source changed during publication')
    write(out/'publication_integrity.json', dict(status='PUBLISHED_GROWING_SIGNED_PACKET_RESULTS',
        prior_frozen_counts=counts, pre_run_files=RUN.FILES, postrun_files=POST_FILES,
        total_frozen_files=sum(counts)+len(RUN.FILES)+len(POST_FILES), tests=totals,
        continuation_pointers_updated=pointers, historical_handoffs_unchanged=True, hashes_used=False, RH_proved=False))
    RUN.validate_parent()
    print(json.dumps(dict(status=results['status'], candidates=len(details), uniform_auxiliary_prices=report['generated_programs'],
        uniform_unlinked_bound_proved=False, total_frozen_files=sum(counts)+len(RUN.FILES)+len(POST_FILES), tests=totals)))
    return results


if __name__ == '__main__':
    main()
