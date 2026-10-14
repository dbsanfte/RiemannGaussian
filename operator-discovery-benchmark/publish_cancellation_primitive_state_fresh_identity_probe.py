"""Publish checked formal probe rows and their exact affine consequences."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
BASE = ROOT / 'cancellation-arithmetic-results'
RUN = BASE / 'primitive-state-fresh-identity-probe-001'
OUT = BASE / 'publication-027'
NOTE = 'PRIMITIVE_STATE_FRESH_IDENTITY_PROBE_HANDOFF.txt'
FLAGS = dict(global_bound_proved=False, RH_proved=False,
             universal_identity_proved=False, candidate_admitted=False,
             exact_admission=False, infeasibility_proved=False,
             identity_refuted=False, arithmetic_sign_values_substituted=False,
             scalar_budget_obligation_verified=False)
ASSIGNMENTS = [[2*n+1 for n in range(1, 36)],
               [(-1)**n*(n*n+1) for n in range(1, 36)]]


def require(value, message):
    if not value:
        raise ValueError(message)


def read(path, cap=8388608):
    with Path(path).open('rb') as handle:
        raw = handle.read(cap+1)
    require(len(raw) <= cap, 'bounded result input')
    return json.loads(raw)


def write_new(path, value, cap=8388608):
    raw = json.dumps(value, sort_keys=True, separators=(',', ':'),
                     allow_nan=False).encode() + b'\n'
    require(len(raw) <= cap, 'bounded publication output')
    with Path(path).open('xb') as handle:
        handle.write(raw)


def false_flags(value):
    require(type(value) is dict, 'explicit checked record')
    for name in FLAGS:
        require(value.get(name) is False, 'finite probe cannot authorize '+name)


def checked_outcome(review, probes):
    """Interpret one completed audit; perform no source evaluation or new search."""
    require(review.get('schema') == 'primitive-state-fresh-identity-probe-independent-review-v1',
            'fresh independent review schema')
    false_flags(review)
    joint = review.get('joint_work', {})
    require(joint.get('max_work') == 450000000
            and joint.get('total_work_reserve') == 450000000,
            'one fixed combined work reservation')
    status = review.get('status')
    require(status in ('REFUTED', 'NOT_REFUTED_BY_THIS_PROBE', 'UNKNOWN'),
            'explicit finite formal-probe outcome')
    if status == 'UNKNOWN':
        require(review.get('all_passed') is False
                and review.get('nonconstant_formal_identity_refuted') is False
                and review.get('necessary_formal_identity_constraints') == []
                and review.get('affine_extension') is None,
                'incomplete audit cannot publish a constraint or rank result')
        return [], [], None
    require(review.get('all_passed') is True
            and review.get('resource_failure') is None,
            'completed independent audit without resource failure')
    checks = review.get('case_checks')
    require(type(checks) is list and len(checks) == 2
            and type(probes) is list and len(probes) == 2,
            'both predetermined cases checked')
    rows, residues = [], []
    for index, (item, probe) in enumerate(zip(checks, probes)):
        require(type(item) is dict and type(item.get('index')) is int
                and item['index'] == index, 'ordered fixed case checks')
        check = item.get('independent_probe_check')
        false_flags(check)
        require(check.get('verified') is True and check.get('complete') is True
                and check.get('complete_grammar_independently_evaluated') is True
                and check.get('complete_coefficient_row_verified') is True
                and check.get('symbolic_source_constructed') is False,
                'every case needs complete independent source evaluation')
        residue = check.get('nonconstant_difference')
        require(type(residue) is int and 0 <= residue < 65537
                and check.get('modular_prime') == 65537, 'fixed-prime exact residual')
        refuted = residue != 0
        require(check.get('status') == ('REFUTED' if refuted else 'NOT_REFUTED_BY_THIS_PROBE')
                and check.get('nonconstant_formal_identity_refuted') is refuted,
                'case rejection requires a checked nonzero residual')
        row = check.get('necessary_formal_identity_constraint')
        require(type(row) is dict
                and row.get('schema') == 'primitive-state-formal-identity-necessary-row-v1'
                and row.get('width') == 1957 and row.get('X') == 9
                and row.get('assignment') == ASSIGNMENTS[index]
                and type(row.get('entries')) is list
                and type(probe) is dict and probe.get('complete') is True
                and probe.get('feedback_row') == row
                and probe.get('nonconstant_difference') == residue,
                'matching full necessary row for the actual fixed assignment')
        rows.append(row)
        residues.append(residue)
    require(review.get('necessary_formal_identity_constraints') == rows,
            'review retains both exact constraints')
    refuted = any(residues)
    require(status == ('REFUTED' if refuted else 'NOT_REFUTED_BY_THIS_PROBE')
            and review.get('nonconstant_formal_identity_refuted') is refuted,
            'aggregate disposition follows checked case residues')
    extension = review.get('affine_extension')
    require(type(extension) is dict and extension.get('complete') is True
            and extension.get('old_rank') == 780,
            'complete sequential reduction against the licensed old chart')
    false_flags(extension)
    require(extension.get('formal_family_only') is True,
            'rank conclusions concern the specified formal family')
    reductions = extension.get('reductions')
    appended = extension.get('appended_rows')
    require(type(reductions) is list and len(reductions) == 2
            and type(appended) is list, 'both exact reduction records')
    classes = [item.get('classification') for item in reductions]
    require(all(c in ('independent', 'redundant', 'inconsistent') for c in classes),
            'exact coefficient versus augmented-row classifications')
    rank = 780 + classes.count('independent')
    inconsistent = 'inconsistent' in classes
    require(extension.get('coefficient_rank') == rank
            and extension.get('augmented_rank') == rank + int(inconsistent)
            and extension.get('free_count') == (None if inconsistent else 1224-rank)
            and len(appended) == classes.count('independent'),
            'coefficient rank, augmented rank and free dimension agree')
    return rows, residues, extension


def publish(run=RUN, destination=OUT):
    run, destination = Path(run).resolve(), Path(destination).resolve()
    require(not destination.exists(), 'fresh publication destination')
    latest = read(BASE / 'latest.json', 65536)
    require(latest.get('publication') == 'publication-026', 'expected predecessor publication')
    review = read(run / 'independent_verification.json')
    probes, jobs = [], []
    for index in range(2):
        directory = run / 'jobs' / ('case-%02d' % index)
        probes.append(read(directory / 'probe.json', 1048576)
                      if (directory / 'probe.json').exists() else None)
        jobs.append(read(directory / 'probe-job.json', 65536)
                    if (directory / 'probe-job.json').exists() else {})
    rows, residues, extension = checked_outcome(review, probes)
    cases = [dict(index=i, scale=9, horizon=35,
                  formal_assignment='u_n=2n+1' if i == 0 else 'u_n=(-1)^n*(n^2+1)',
                  nonconstant_difference=residues[i] if residues else None,
                  constraint_file='constraint-%02d.json' % i if rows else None,
                  nonzero_coordinates=len(rows[i]['entries']) if rows else None,
                  rhs=rows[i]['rhs'] if rows else None,
                  producer_status=jobs[i].get('status'), producer_failure=jobs[i].get('reason'),
                  producer_counts=jobs[i].get('evaluation_counts'), producer_cost=jobs[i].get('cost'))
             for i in range(2)]
    report = dict(
        schema=27, title='Fresh formal assignments and exact affine constraints',
        previous_publication='publication-026', candidate_origin='publication-026',
        prior_chart_origin='publication-024', run=str(run.relative_to(ROOT)),
        status=review['status'], nonconstant_formal_identity_refuted=bool(any(residues)),
        modular_prime=65537, cases=cases,
        candidate_vector_path=str((run / 'candidate.json').relative_to(ROOT)),
        independent_review_path=str((run / 'independent_verification.json').relative_to(ROOT)),
        independent_audit_complete=review['all_passed'],
        independent_resource_failure=review.get('resource_failure'),
        feedback_constraint_count=len(rows), feedback_is_discovery_data=bool(rows),
        affine_extension_file='affine-extension.json' if extension is not None else None,
        old_coefficient_rank=780,
        coefficient_rank=extension['coefficient_rank'] if extension else None,
        augmented_rank=extension['augmented_rank'] if extension else None,
        free_count=extension['free_count'] if extension else None,
        reduction_classifications=[r['classification'] for r in extension['reductions']] if extension else [],
        no_candidate_repair_or_optimization=True, symbolic_source_constructed=False,
        joint_work=review['joint_work'], independent_cost=review.get('cost'),
        tests_passed=review.get('tests_passed'),
        remaining_obligations=['finite cone feasibility', 'universal nonconstant formal identity',
                               'uniform scalar budget and initial storage cost',
                               'cofinal parameter family and ordinary-zeta bridge'],
        interpretation='Checked nonzero residues reject this fixed formal identity. '
                       'The rows are necessary constraints for the same formal operator family. '
                       'They do not decide an arithmetic-only inequality or RH.',
        **FLAGS)
    destination.mkdir()
    for index, row in enumerate(rows):
        write_new(destination / ('constraint-%02d.json' % index), row, 1048576)
    if extension is not None:
        write_new(destination / 'affine-extension.json', extension)
    write_new(destination / 'report.json', report, 1048576)
    note = ROOT / NOTE
    if note.exists():
        (destination / NOTE).write_bytes(note.read_bytes())
    require(read(BASE / 'latest.json', 65536) == latest, 'no intervening publication')
    pointer = BASE / 'latest-027.tmp'
    write_new(pointer, dict(publication=destination.name, report='report.json',
                            status=review['status'], **FLAGS), 65536)
    pointer.replace(BASE / 'latest.json')
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    print(json.dumps(publish(), sort_keys=True))
