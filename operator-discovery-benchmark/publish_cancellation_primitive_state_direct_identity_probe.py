"""Publish direct exact column evaluation and its checked necessary constraint."""
import argparse
import json
from pathlib import Path
from publish_cancellation_primitive_state_uniform_identity_probe import FLAGS, require, read, write_new

ROOT = Path(__file__).resolve().parent
BASE = ROOT / 'cancellation-arithmetic-results'
RUN = BASE / 'primitive-state-direct-identity-probe-001'
OUT = BASE / 'publication-023'
NOTE = 'PRIMITIVE_STATE_DIRECT_IDENTITY_PROBE_HANDOFF.txt'


def checked_outcome(review, probe):
    require(review.get('schema') == 'primitive-state-direct-identity-probe-independent-review-v1',
            'direct-evaluation independent review')
    for name in FLAGS:
        require(review.get(name) is False, 'finite evaluation cannot authorize ' + name)
    joint = review.get('joint_work', {})
    total = joint.get('total_work_reserve')
    require(joint.get('max_work') == 450000000 and type(total) is int
            and 0 < total <= 450000000, 'one bounded joint research job')
    status = review.get('status')
    require(status in ('REFUTED', 'NOT_REFUTED_BY_THIS_PROBE', 'UNKNOWN'), 'finite probe outcome')
    require(review.get('all_passed') is True or
            (status == 'UNKNOWN' and review.get('all_passed') is False
             and type(review.get('resource_failure')) is dict
             and review.get('necessary_formal_identity_constraint') is None),
            'completed review or explicit bounded audit failure')
    if status == 'UNKNOWN':
        require(review.get('nonconstant_formal_identity_refuted') is False,
                'incomplete evaluation cannot reject the candidate')
        return None, None
    check = review.get('independent_probe_check')
    require(type(check) is dict and check.get('verified') is True and check.get('complete') is True
            and check.get('complete_grammar_independently_evaluated') is True
            and check.get('complete_coefficient_row_verified') is True
            and check.get('symbolic_source_constructed') is False,
            'complete independent direct arithmetic replay')
    for name in FLAGS:
        require(check.get(name) is False, 'finite check cannot authorize ' + name)
    residue = check.get('nonconstant_difference')
    require(type(residue) is int and 0 <= residue < 65537 and check.get('modular_prime') == 65537,
            'exact fixed-prime residual')
    refuted = residue != 0
    require(status == ('REFUTED' if refuted else 'NOT_REFUTED_BY_THIS_PROBE')
            and check.get('status') == status
            and check.get('nonconstant_formal_identity_refuted') is refuted
            and review.get('nonconstant_formal_identity_refuted') is refuted,
            'checked nonzero residual is required for rejection')
    row = check.get('necessary_formal_identity_constraint')
    require(type(row) is dict and row.get('width') == 1957 and row.get('X') == 7
            and review.get('necessary_formal_identity_constraint') == row
            and type(probe) is dict and probe.get('feedback_row') == row
            and probe.get('nonconstant_difference') == residue,
            'same complete exact necessary constraint')
    return row, residue


def publish(run=RUN, destination=OUT):
    run, destination = Path(run).resolve(), Path(destination).resolve()
    require(not destination.exists(), 'new publication destination')
    latest = read(BASE / 'latest.json')
    require(latest.get('publication') == 'publication-022', 'expected predecessor publication')
    review = read(run / 'independent_verification.json')
    probe_path, record_path = run / 'jobs/probe.json', run / 'jobs/probe-job.json'
    probe = read(probe_path) if probe_path.exists() else None
    record = read(record_path) if record_path.exists() else {}
    row, residue = checked_outcome(review, probe)
    report = dict(
        schema=23, title='Direct exact formal identity probe and feedback constraint',
        previous_publication='publication-022', candidate_origin='publication-021',
        run=str(run.relative_to(ROOT)), status=review['status'],
        nonconstant_formal_identity_refuted=residue is not None and residue != 0,
        scale=7, horizon=27, modular_prime=65537, nonconstant_difference=residue,
        candidate_vector_path=str((run / 'candidate.json').relative_to(ROOT)),
        independent_review_path=str((run / 'independent_verification.json').relative_to(ROOT)),
        independent_audit_complete=review['all_passed'],
        independent_resource_failure=review.get('resource_failure'),
        producer_status=record.get('status'), producer_failure=record.get('reason'),
        feedback_constraint_available=row is not None,
        feedback_constraint_file='constraint.json' if row is not None else None,
        feedback_nonzero_coordinates=len(row['entries']) if row is not None else None,
        feedback_rhs=row['rhs'] if row is not None else None,
        symbolic_source_constructed=False,
        method='Complete operator columns evaluated exactly at u_n=2n+1 and at all-zero formal variables; fixed candidate dot reduced modulo65537',
        work_metric='Explicit rational arithmetic and integer-domain loop proxies, with separate preparation allowance',
        joint_work=review['joint_work'], producer_cost=record.get('cost'),
        independent_cost=review.get('cost'), tests_passed=review.get('tests_passed'),
        remaining_obligations=['finite cone feasibility', 'universal formal nonconstant identity',
                               'uniform scalar bound and ordinary-zeta bridge'],
        interpretation='A verified nonzero residual rejects this fixed formal identity only. The exact row supplies a necessary constraint for future search.',
        **FLAGS)
    destination.mkdir()
    if row is not None:
        write_new(destination / 'constraint.json', row)
    write_new(destination / 'report.json', report)
    if (ROOT / NOTE).exists():
        (destination / NOTE).write_text((ROOT / NOTE).read_text())
    require(read(BASE / 'latest.json') == latest, 'no intervening publication')
    pointer = BASE / 'latest-023.tmp'
    write_new(pointer, dict(publication=destination.name, report='report.json', status=review['status'], **FLAGS))
    pointer.replace(BASE / 'latest.json')
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    print(json.dumps(publish(), sort_keys=True))
