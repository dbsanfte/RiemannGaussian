"""Render a separately scoped account of a verified convolution experiment.

This is reporting code, outside the frozen search. It makes no theorem admission.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path


def read(path):
    return json.loads(path.read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def report(directory):
    d = Path(directory).resolve()
    verification = read(d / 'verification.json')
    if verification.get('all_passed') is not True:
        raise ValueError('independent verification required')
    for name, expected in verification['input_sha256'].items():
        if sha(d / name) != expected:
            raise ValueError('verified input changed: ' + name)
    protocol = read(d / 'protocol.json')
    for name, expected in protocol['code_sha256'].items():
        if sha(d / 'frozen_source' / name) != expected:
            raise ValueError('frozen source changed: ' + name)
    factory = read(d / 'candidate_batch.json')['factory']
    queue = read(d / 'proof_queue.json')['queue']
    final = read(d / 'final_evaluation.json')
    cases = read(d / 'final_cases.json')
    scores = {row['program_id']: row['score'] for row in final['results']}
    features = {f['feature_id']: f for f in protocol['feature_dictionary']}
    rows = []
    for candidate in queue:
        pid = candidate['program_id']
        score = scores[pid]
        failures = []
        for observation in score['observations']:
            if observation['finite_pass'] is not False:
                continue
            x = observation['X']
            failures.append(dict(observation,
                in_dyadic_claim_domain=x > 0 and x & (x - 1) == 0,
                refutes_existential_global_claim=False,
                scope='stored fitted constant only'))
        terms = [dict(weight=t['weight'], feature=features[t['feature_id']])
                 for t in candidate['exact_program']['terms']]
        rows.append(dict(program_id=pid, selected_for=candidate['selection_origins'],
                         terms=terms, constants=candidate['exact_program']['constants'],
                         final_score=score, failures=failures,
                         global_claim_status='unresolved'))
    totals = {key: sum(s[key] for s in scores.values()) for key in
              ('finite_passes', 'finite_failures', 'missing_cases', 'finite_cases')}
    summary = dict(schema=1, verification_sha256=sha(d / 'verification.json'),
                   feature_count=len(features), proposal_count=len(factory['proposal_archive']),
                   candidate_count=len(factory['candidates']), selected_count=len(queue),
                   alias_count=sum(p.get('alias_of') is not None for p in factory['proposal_archive']),
                   unavailable_proposals=sum('program_id' not in p for p in factory['proposal_archive']),
                   final_base_scales=cases['base_scales'], final_levels=cases['levels'],
                   final_totals=totals, candidates=rows,
                   actual_all_scale_signed_bound_proved=False, RH_proved=False,
                   scope='separate research stage; no legacy theorem-registry promotion',
                   provenance=protocol['provenance'])
    lines = [
        'COMPLETE CONVOLUTION CANCELLATION: VERIFIED FINITE PILOT', '',
        f"{len(features)} nonnegative features; {summary['proposal_count']} proposals; "
        f"{summary['candidate_count']} distinct exact programs; {len(queue)} selected.",
        f"Aliases retained: {summary['alias_count']}; unavailable proposals: {summary['unavailable_proposals']}.",
        f"Final base scales: {cases['base_scales']}; exponent levels: {cases['levels']}.",
        f"Final observations: {totals['finite_passes']} passes, {totals['finite_failures']} failures, "
        f"{totals['missing_cases']} missing constants or computations.", '',
        'Each stored bound concerns the innovation of E+V, where E=A_C/X^2,',
        'C is the complete prefix of actual c=mu*lambda, and V is nonnegative.',
        'An all-dyadic bound at every sufficiently large integer q would telescope',
        'to critical ordinary energy and imply RH. That premise is unproved.',
        'A failure below refutes a stored constant only. Unknown q constants stay',
        'missing. Odd-scale failures are diagnostics outside the dyadic claim.', '',
        'Selected programs (exact expressions and every observation in report.json):'
    ]
    for row in rows:
        s = row['final_score']
        lines.append(f"  {row['program_id'][:12]}: {','.join(row['selected_for'])}; "
                     f"{len(row['terms'])} terms; passes={s['finite_passes']}, "
                     f"failures={s['finite_failures']}, missing={s['missing_cases']}")
        for failure in row['failures']:
            lines.append(f"    X={failure['X']}, q={failure['level']}, margin={failure['margin']}, "
                         f"dyadic={failure['in_dyadic_claim_domain']}")
    lines += ['',
        'Arithmetic is produced with a complete prime sieve and generic convolutions.',
        'Prior arithmetic prefixes overlap. This is not an unseen-prime holdout.',
        'The isolated worker uses a Python file-access guard, not OS isolation.',
        'LP output proposes weights; rational weights, refits, full profiles and',
        'available final scores are independently checked. LP optimality is not certified.',
        'All complete divisor channels and child-scale selectors are retained.',
        'No full signed arithmetic bound, new prime-distribution bound, or RH proof.', '']
    return summary, '\n'.join(lines)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    args = parser.parse_args()
    summary, prose = report(args.directory)
    for name, content in [('report.json', json.dumps(summary, indent=2, sort_keys=True) + '\n'),
                          ('report.txt', prose)]:
        with (args.directory / name).open('x') as stream:
            stream.write(content)
    print(prose)
