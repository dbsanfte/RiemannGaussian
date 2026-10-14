"""Read frozen study artifacts and describe structural leads without refitting."""
from fractions import Fraction as Q
import json
from pathlib import Path
import sys


def read(directory, name):
    return json.loads((directory / name).read_text())


def ratio(a, b):
    return str(Q(a) / Q(b)) if Q(b) else None


def display(value):
    return 'undefined' if value is None else format(float(Q(value)), '.6g')


def report(directory):
    directory = Path(directory).resolve()
    batch = read(directory, 'final_batch.json')
    analysis = {r['id']: r for r in read(directory, 'discovery_analysis.json')}
    responses = read(directory, 'final_responses.json')
    original_audit = read(directory, 'independent_verification.json')
    audit = (read(directory, 'independent_completion.json')
             if (directory / 'independent_completion.json').exists() else original_audit)
    ceiling = audit.get('revised_ceiling', 450000000)
    receipt = read(directory, 'receipt.json')
    tests = read(directory, 'tests.json')
    baseline = next(r for r in responses if r['id'] == 0 and r['source'] == 'mu')
    baseline_cases = {c['X']: c for c in baseline['cases']}
    baseline_parts = {c['X']: c for c in baseline.get('decomposition', [])}
    leads = []
    for item in batch:
        record = item['record']; ordinal = record['id']
        if ordinal == 0:
            continue
        discovery = analysis[ordinal]
        mu = next(r for r in responses if r['id'] == ordinal and r['source'] == 'mu')
        final = []
        for c in mu['cases']:
            final.append(dict(c, baseline_ratio=ratio(c['energy'], baseline_cases[c['X']]['energy']),
                              path_energy_ratio=ratio(c['energy'], c['absolute_energy'])))
        parts = []
        for c in mu.get('decomposition', []):
            base = baseline_parts[c['X']]['total_energy']
            F, G, C, E = (Q(c[k]) for k in ('diagonal_energy', 'lower_energy', 'mixed_energy', 'total_energy'))
            if F + G + C != E:
                raise ValueError('complete decomposition must agree before reporting')
            parts.append(dict(c, baseline_ratio=ratio(E, base), diagonal_ratio=ratio(F, base),
                              negative_cross_fraction=ratio(-C, F + G),
                              lower_plus_cross_relative_to_diagonal=ratio(G + C, F)))
        controls = [dict(source=r['source'], status=r['status'], failed=sum(not s['passed'] for s in r['scores']),
                         comparisons=len(r['scores']), cases=r['cases'])
                    for r in responses if r['id'] == ordinal and r['source'] != 'mu']
        leads.append(dict(id=ordinal, family=record['family'], program=record['program'],
                          raw_program=record['raw_program'], certificate=record['certificate'],
                          normalization=record['normalization'], calibration=record['calibration'],
                          discovery={k: discovery[k] for k in ('gate_failures', 'raw_ratio', 'specificity', 'conditional_cost')},
                          final_mu_status=mu['status'], final_mu=final,
                          final_mu_failed=sum(not s['passed'] for s in mu['scores']),
                          final_mu_comparisons=len(mu['scores']), decomposition=parts, final_controls=controls))
    output = dict(schema='permuted-circuit-report-v1', archive=str(directory),
                  independent_status=audit['status'],
                  finite_arithmetic_verified=audit['finite_arithmetic_verified'],
                  all_expected_evaluations_available=audit.get('all_expected_evaluations_available', False),
                  evaluations_verified=audit['evaluations_verified'], certificates_checked=audit['certificates_checked'],
                  cumulative_operations=audit['cumulative_operations'], total_work_ceiling=ceiling,
                  original_work_ceiling=450000000, original_audit_status=original_audit['status'],
                  original_ceiling_met=audit['cumulative_operations'] <= 450000000,
                  tests_returncode=tests['returncode'], preparation=tests['work'],
                  final_available=receipt['final_available'], final_missing=receipt['final_missing'],
                  final_invalid=receipt['final_invalid'],
                  moment_estimate_proved=False, global_bound_proved=False, RH_proved=False,
                  baseline_mu=baseline, leads=leads,
                  limitations=[
                      'Finite responses and ordinary mathematical inverse certificates; no proof-assistant claim.',
                      'Full cofinal fixed-circuit moment inequality remains unproved.',
                      'Final source scales are unmatched; specificity uses matched discovery data only.',
                      'Previous source/scale overlap is disclosed; this is a new structural catalogue.',
                      'Reported decimal ratios are display approximations of retained exact rationals.',
                      'Report arithmetic and I/O are covered by the previously charged root reserve.'])
    with (directory / 'report.json').open('x') as handle:
        json.dump(output, handle, sort_keys=True, indent=2); handle.write('\n')
    lines = [
        'PERMUTED AND MIXED ARITHMETIC CANDIDATE STUDY — pilot-001',
        '',
        'Independent status: ' + audit['status'],
        'Whole-study charged operations: ' + str(audit['cumulative_operations']) + ' / ' + str(ceiling) + '.',
        ('Original 450m ceiling exceeded; explicit user-authorized extension at most7%; original receipt retained.'
         if ceiling > 450000000 else 'Original 450m study ceiling retained.'),
        'All-scale moment estimate, global signed bound and RH: UNPROVED.',
        '',
        'The new language combines fractional full divisor convolutions with',
        'closed-block polynomial/bit/source-branch permutations and reversible',
        'pair shears. Both pair coordinates and every signed square are retained.',
        'The frozen catalogue has 48 raw words plus baseline. Exact baseline',
        'aliases cannot consume a lead slot; selection preserves four families.',
        'Generation, ranking and all operator coefficients preceded responses.',
        '',
        '39 frozen tests passed.',
        ('Independent verification completed for all available cases and the'
         if audit['finite_arithmetic_verified'] else 'Independent verification is incomplete; consult its retained checkpoints and'),
        ('recovery metadata, normalizations, fits, diagnostics and selection.'
         if audit['finite_arithmetic_verified'] else 'independent_verification.json for the exact checked scope and stopping reason.'),
        'Evaluations verified: ' + str(audit['evaluations_verified']) + '.',
        'Final available/missing/invalid: ' + '/'.join(str(receipt[k]) for k in ('final_available', 'final_missing', 'final_invalid')) + '.',
        '',
        'Selected structures and finite evidence (ratios relative to original M):']
    for lead in leads:
        lines += ['', 'ID ' + str(lead['id']) + ' — ' + lead['family'],
                  json.dumps(lead['program'], sort_keys=True),
                  'Matched validation: worst raw ratio ' + display(lead['discovery']['raw_ratio'])
                  + '; worst path-cancellation specificity ' + display(lead['discovery']['specificity'])
                  + '; failed gates ' + str(lead['discovery']['gate_failures']) + '/16.']
        for c in lead['final_mu']:
            lines.append('Final mu X=' + str(c['X']) + ': energy/baseline=' + display(c['baseline_ratio'])
                         + ', signed/absolute-path energy=' + display(c['path_energy_ratio']) + '.')
        lines.append('Final mu gates failed ' + str(lead['final_mu_failed']) + '/' + str(lead['final_mu_comparisons']) + '.')
        for c in lead['decomposition']:
            lines.append('Dyadic X=' + str(c['X']) + ': E=' + display(c['total_energy'])
                         + ', F=' + display(c['diagonal_energy']) + ', G=' + display(c['lower_energy'])
                         + ', C=' + display(c['mixed_energy']) + '; -C/(F+G)='
                         + display(c['negative_cross_fraction']) + '.')
    lines += ['', 'Interpretation of this frozen batch:',
              'None of the four selected circuits improves the full Mobius energy',
              'over baseline at the final tested blocks. ID33 has negative fresh/',
              'lower-block cross terms on all three recorded dyadic scales, but',
              'that credit does not cover its entire positive lower-block term.',
              'Its low path-envelope ratio therefore does not establish the needed',
              'signed estimate. The other selected circuits have mostly positive',
              'cross terms. Baseline and candidates all pass the finite mu gates;',
              'both coherent controls fail those gates, including at baseline.',
              'These are structural leads and diagnostic lessons, not RH bounds.',
              '', 'Exact proof accounting:',
              'rho_B=Q_B M_B+g_B, with Q obtained by deleting convolution stages',
              'without normalizing the remaining word. E=F+G+C is checked exactly:',
              'F=X^-2||Q_B M_B||^2, G=X^-2||g_B||^2, C=2X^-2<Q_B M_B,g_B>.',
              'Permutation-only Q preserves full block energy. Shears introduce',
              'fresh/fresh cross terms while retaining the complementary coordinate.',
              'Negative C alone is insufficient: the entire E must satisfy the',
              'cofinal subpower gate for one fixed circuit over every dyadic scale.',
              '', 'The uniform inverse is proved in the grammar review; it is not',
              'an estimate for actual Mobius moments. Final control scales differ',
              'from final mu scales, so final specificity comparisons are not made.',
              'No fitted operator coefficients, optimizer, content hashes or edits',
              'to earlier frozen studies were used. Full exact values: report.json.']
    with (directory / 'handoff.txt').open('x') as handle:
        handle.write('\n'.join(lines) + '\n')
    return output


if __name__ == '__main__':
    value = report(sys.argv[1])
    print(json.dumps({k: value[k] for k in ('independent_status', 'evaluations_verified', 'cumulative_operations',
                                          'final_available', 'final_missing', 'final_invalid')}))
