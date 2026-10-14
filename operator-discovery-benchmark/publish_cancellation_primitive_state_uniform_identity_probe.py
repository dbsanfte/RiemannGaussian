"""Save a checked fresh-scale result and its exact feedback row, without hashes."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
BASE = ROOT / 'cancellation-arithmetic-results'
RUN = BASE / 'primitive-state-uniform-identity-probe-001'
OUT = BASE / 'publication-022'
NOTE = 'PRIMITIVE_STATE_UNIFORM_IDENTITY_PROBE_HANDOFF.txt'
FLAGS = dict(global_bound_proved=False, RH_proved=False,
             universal_identity_proved=False, candidate_admitted=False,
             exact_admission=False, infeasibility_proved=False,
             scalar_budget_obligation_verified=False)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read(path):
    path = Path(path)
    require(path.stat().st_size <= 1048576, 'bounded result JSON')
    return json.loads(path.read_text())


def write_new(path, value):
    data = json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False)
    require(len(data.encode()) <= 1048576, 'bounded publication result')
    with Path(path).open('x') as handle:
        handle.write(data + '\n')


def checked_outcome(review, probe):
    """Interpret the completed independent check; never rerun the source build."""
    require(review.get('schema') == 'primitive-state-uniform-identity-probe-independent-review-v1',
            'independent review record')
    for name in FLAGS:
        require(review.get(name) is False, 'finite probe cannot authorize ' + name)
    joint = review.get('joint_work', {})
    total = joint.get('total_work_reserve')
    require(joint.get('max_work') == 450000000 and type(total) is int
            and 0 < total <= 450000000, 'one bounded joint research job')
    status = review.get('status')
    require(status in ('REFUTED', 'NOT_REFUTED_BY_THIS_PROBE', 'UNKNOWN'),
            'explicit finite probe outcome')
    require(review.get('all_passed') is True or
            (status == 'UNKNOWN' and review.get('all_passed') is False
             and type(review.get('independent_resource_failure')) is dict
             and review.get('necessary_formal_identity_constraint') is None),
            'completed review or explicit bounded audit failure')
    check = review.get('independent_probe_check')
    if status == 'UNKNOWN':
        require(review.get('nonconstant_formal_identity_refuted') is False,
                'incomplete run cannot reject the candidate')
        return None, None
    require(type(check) is dict and check.get('verified') is True
            and check.get('complete') is True
            and check.get('source_semantics_independently_verified') is True
            and check.get('source_rebuilds') == 1,
            'complete independent source and mathematical replay')
    for name in FLAGS:
        require(check.get(name) is False, 'finite check cannot authorize ' + name)
    residue = check.get('nonconstant_difference')
    require(type(residue) is int and 0 <= residue < 65537
            and check.get('modular_prime') == 65537, 'exact modular witness')
    refuted = residue != 0
    require(status == ('REFUTED' if refuted else 'NOT_REFUTED_BY_THIS_PROBE')
            and check.get('status') == status
            and check.get('nonconstant_formal_identity_refuted') is refuted
            and review.get('nonconstant_formal_identity_refuted') is refuted,
            'rejection follows a checked nonzero residual')
    row = check.get('necessary_formal_identity_constraint')
    require(type(row) is dict and row.get('width') == 1957 and row.get('X') == 7
            and review.get('necessary_formal_identity_constraint') == row
            and type(probe) is dict and probe.get('feedback_row') == row
            and probe.get('nonconstant_difference') == residue,
            'same complete exact feedback constraint')
    return row, residue


def publish(run=RUN, destination=OUT):
    run, destination = Path(run).resolve(), Path(destination).resolve()
    require(not destination.exists(), 'new publication destination')
    latest = read(BASE / 'latest.json')
    require(latest.get('publication') == 'publication-021', 'expected predecessor publication')
    review = read(run / 'independent_verification.json')
    probe_path = run / 'jobs/probe.json'
    probe = read(probe_path) if probe_path.exists() else None
    row, residue = checked_outcome(review, probe)
    record_path = run / 'jobs/probe-job.json'
    record = read(record_path) if record_path.exists() else {}
    report = dict(
        schema=22, title='Fresh-scale formal identity probe and exact feedback constraint',
        previous_publication='publication-021', run=str(run.relative_to(ROOT)),
        status=review['status'], nonconstant_formal_identity_refuted=residue is not None and residue != 0,
        scale=7, horizon=27, modular_prime=65537, nonconstant_difference=residue,
        formal_assignment='u_n=2n+1 for every n=1..27; baseline u_n=0 including u_1',
        candidate_vector_path=str((run / 'candidate.json').relative_to(ROOT)),
        independent_review_path=str((run / 'independent_verification.json').relative_to(ROOT)),
        independent_audit_complete=review['all_passed'],
        independent_resource_failure=review.get('independent_resource_failure'),
        feedback_constraint_available=row is not None,
        feedback_constraint_file='constraint.json' if row is not None else None,
        feedback_nonzero_coordinates=len(row['entries']) if row is not None else None,
        feedback_rhs=row['rhs'] if row is not None else None,
        source_metric='Python LINE_EVENTS; evaluation uses separate rational-work proxies',
        joint_work=review['joint_work'], producer_cost=record.get('cost'),
        independent_cost=review.get('cost'), tests_passed=review.get('tests_passed'),
        remaining_obligations=['finite cone feasibility', 'universal formal nonconstant identity',
                               'uniform scalar bound and ordinary-zeta bridge'],
        interpretation='A nonzero residue rejects only this fixed formal identity. The exact row is a necessary constraint for a future search.',
        **FLAGS)
    destination.mkdir()
    if row is not None:
        write_new(destination / 'constraint.json', row)
    write_new(destination / 'report.json', report)
    note = ROOT / NOTE
    if note.exists():
        (destination / NOTE).write_text(note.read_text())
    # Updating the one mutable pointer does not rewrite any earlier publication.
    require(read(BASE / 'latest.json') == latest, 'no intervening publication')
    pointer = BASE / 'latest-022.tmp'
    write_new(pointer, dict(publication=destination.name, report='report.json',
                            status=review['status'], **FLAGS))
    pointer.replace(BASE / 'latest.json')
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    print(json.dumps(publish(), sort_keys=True))
