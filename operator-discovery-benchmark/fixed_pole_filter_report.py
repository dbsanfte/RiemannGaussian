"""Separate report of the verified finite fixed-filter experiment; no admission."""
import argparse
import hashlib
import json
from pathlib import Path


def read(path): return json.loads(path.read_text())
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()


def report(directory):
    d = Path(directory).resolve()
    verified = read(d / 'verification.json')
    if verified.get('all_passed') is not True:
        raise ValueError('independent verification required')
    for name, expected in verified['input_sha256'].items():
        if sha(d / name) != expected:
            raise ValueError('verified input changed: ' + name)
    for name, expected in verified['code_sha256'].items():
        if sha(d / 'frozen_source' / name) != expected:
            raise ValueError('frozen source changed: ' + name)
    factory = read(d / 'candidate_batch.json')['factory']
    queue = read(d / 'proof_queue.json')['queue']
    final = read(d / 'final_evaluation.json')
    cases = read(d / 'final_cases.json')
    scores = {r['program_id']: r['score'] for r in final['results']}
    candidates = []
    for candidate in queue:
        program = candidate['exact_program']
        failures = []
        for mode, score in scores[candidate['program_id']]['modes'].items():
            for observation in score['observations']:
                if observation['finite_pass'] is False:
                    x = observation['X']
                    failures.append(dict(observation, mode=mode, in_dyadic_domain=x & (x - 1) == 0,
                                         existential_global_claim_refuted=False,
                                         scope='stored fitted constant only'))
        candidates.append(dict(program_id=candidate['program_id'], exact_program=program,
                               selection_origins=candidate['selection_origins'],
                               conditional_admission=candidate['conditional_admission'],
                               final_score=scores[candidate['program_id']], failures=failures,
                               original_global_claim_disposition='unresolved'))
    archive = factory['proposal_archive']
    summary = dict(schema=1, verification_sha256=sha(d / 'verification.json'),
                   proposal_count=len(archive), candidate_count=len(factory['candidates']),
                   selected_count=len(queue), aliases=sum(p.get('alias_of') is not None for p in archive),
                   missing_proposals=sum('program_id' not in p for p in archive),
                   final_cases=cases, final_counts=verified['final_counts'], candidates=candidates,
                   actual_all_scale_signed_bound_proved=False, RH_proved=False,
                   scope='finite complete signed arithmetic; separately reviewed conditional RH bridges; no global estimate')
    lines = ['FIXED FILTERS WITH CONDITIONAL ORDINARY-ZETA POLE PRESERVATION', '',
             f"{len(archive)} proposals, {summary['candidate_count']} distinct exact programs, "
             f"{summary['aliases']} aliases, {summary['missing_proposals']} missing proposals.",
             f"Selected {len(queue)} distinct programs; final base scales {cases['base_scales']}.",
             f"Exponent levels {cases['levels']}; unknown constants remain missing.", '']
    for mode, counts in verified['final_counts'].items():
        lines.append(f"{mode}: {counts['passes']} passes, {counts['failures']} failures, "
                     f"{counts['missing']} missing; {counts['dyadic_stored_constant_failures']} "
                     f"failures in the dyadic claim domain.")
    lines += ['', 'Programs (A is the complete prefix of the specified actual target):']
    for candidate in candidates:
        program = candidate['exact_program']; target = program['target']
        expression = ' + '.join(f"({t['weight']})A(floor(x/{t['divisor']}))" for t in program['filter'])
        lines += [f"  {candidate['program_id'][:12]}: mu arity {target['r']}, lambda arity {target['l']}",
                  '    G(x) = ' + expression]
        for mode, score in candidate['final_score']['modes'].items():
            lines.append(f"    {mode}: pass {score['finite_passes']}, fail {score['finite_failures']}, missing {score['missing_cases']}")
    lines += ['',
        'Every admitted fixed filter has nonzero support m<=r+l. Its multiplier',
        'has zero order at most m-1, whereas an ordinary off-critical zeta zero',
        'contributes pole order at least r+l. A complete cofinal critical-energy',
        'estimate would therefore imply RH. No such estimate is proved here.',
        'Fitted-constant failures do not refute an existential claim allowing other',
        'constants or another initial exponent level. Odd-scale tests are diagnostics.',
        'All coefficients and matrix cross terms were independently reconstructed.',
        'The search used actual prime sieving; prior coefficient prefixes overlap.',
        'The generator had a Python file-access guard, not OS isolation.',
        'Exact box-quadratic fitting is independently checked; finite minimization',
        'does not prove a global arithmetic inequality.',
        'The separate pairing proof excludes sublinear UNSIGNED remainders for',
        'same-core exponent matching: every such remainder is at least X/8 for',
        'X>=256. It gives no lower bound on the SIGNED prefix.', '']
    return summary, '\n'.join(lines)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    args = parser.parse_args()
    summary, prose = report(args.directory)
    for name, content in [('report.json', json.dumps(summary, indent=2, sort_keys=True) + '\n'), ('report.txt', prose)]:
        with (args.directory / name).open('x') as stream:
            stream.write(content)
    print(prose)
