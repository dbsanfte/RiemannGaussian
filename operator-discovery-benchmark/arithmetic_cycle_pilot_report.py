"""Posthoc summary of an independently verified finite certificate pilot."""
import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def build_report(run):
    run = Path(run)
    receipt_path = run / 'independent_verification.json'
    receipt_hash = sha(receipt_path)
    receipt = json.loads(receipt_path.read_text())
    if receipt.get('all_passed') is not True:
        raise ValueError('independent audit required')

    def bindings():
        for name, value in receipt['input_sha256'].items():
            if sha(run / name) != value:
                raise ValueError('verified input changed: ' + name)
        for name, value in receipt['code_sha256'].items():
            if sha(run / 'frozen_source' / name) != value:
                raise ValueError('frozen source changed: ' + name)
        if sha(receipt_path) != receipt_hash:
            raise ValueError('verification receipt changed')

    bindings()
    rows = receipt['actual_post_synthesis_diagnostics']
    counts = Counter()
    for row in rows:
        key = ('certified_true' if row['synthesis_status'] == 'finite_certificate'
               else 'true_without_certificate' if row['bound_true']
               else 'false_stored_bound')
        counts[key] += 1
    unique_bounds = {(r['target'], r['X'], r['D']) for r in rows}
    unique_instances = {(r['target'], r['X'], r['D'], r['mode']) for r in rows}
    development = json.loads((run / 'development.json').read_text())
    calibration = development['calibration']
    result = dict(
        schema=1,
        independent_verification_sha256=receipt_hash,
        verified_input_sha256=receipt['input_sha256'],
        attempts=len(rows),
        distinct_finite_inequalities=len(unique_bounds),
        distinct_finite_inequality_and_mode_instances=len(unique_instances),
        synthesis_counts=receipt['counts'],
        actual_truth_counts=dict(counts),
        diagnostics=rows,
        grouped_counts=receipt['grouped_actual_truth_counts'],
        calibration_status=calibration['synthesis']['status'],
        calibration_certificate=calibration['synthesis'].get('certificate'),
        calibration_is_supplied=True,
        counterfeit_energies=development['controls']['energies'],
        limitations=[
            'All eight successful attempts are at X=1 for mu; q choices duplicate some finite bounds.',
            'The independent evaluator computes actual arithmetic only after synthesis; no response table enters certificate search.',
            'The supplied cycle positivity target tests recovery within a declared basis; it is not a newly discovered estimate.',
            'Final cases resynthesize coefficients. They test finite feasibility, not transfer of a learned operator.',
            'Atomic local coefficients can encode a known finite arithmetic vector. Grouped relation coefficients still allow index-specific square weights.',
            'The available coprime relations have ab<=N; the complete original target is retained, but the complete N-squared cycle domain is not materialized.',
            'No-certificate results alone prove neither cone infeasibility nor failure of the actual inequality.',
            'False stored bounds are finite arithmetic counterexamples, not refutations of existential all-scale constants or RH.',
            'An all-scale claim requires a proved symbolic or recursive template and every cofinal exponent; no such template has been obtained.',
        ],
        global_bound_proved=False,
        RH_proved=False,
    )
    bindings()
    result['bindings_rechecked_at_end'] = True
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('run')
    run = Path(parser.parse_args().run)
    if any((run / n).exists() for n in ('analysis-report.json', 'analysis-report.txt')):
        raise FileExistsError('fresh posthoc report paths required')
    report = build_report(run)
    with (run / 'analysis-report.json').open('x') as f:
        json.dump(report, f, indent=2, sort_keys=True)
        f.write('\n')
    with (run / 'analysis-report.txt').open('x') as f:
        f.write('INDEPENDENTLY VERIFIED FINITE ARITHMETIC CERTIFICATE PILOT\n\n')
        f.write(f"Attempts: {report['attempts']}; distinct finite inequalities: {report['distinct_finite_inequalities']}; inequality/mode instances: {report['distinct_finite_inequality_and_mode_instances']}.\n")
        f.write('Synthesis: ' + json.dumps(report['synthesis_counts'], sort_keys=True) + '\n')
        f.write('Independent actual arithmetic: ' + json.dumps(report['actual_truth_counts'], sort_keys=True) + '\n\n')
        for item in report['limitations']:
            f.write(item + '\n')


if __name__ == '__main__':
    main()
