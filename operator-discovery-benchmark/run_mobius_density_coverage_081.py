"""Postrun coverage proposals; no change or refit to frozen search candidates."""
import json
import resource
import time
from fractions import Fraction as Q

import mobius_density_coverage_081 as COVER
import run_mobius_density_packet_081 as RUN
from run_fractional_prime_kernel_051 import write


def main():
    path = RUN.OUT/'coverage_proposals_081.json'
    if path.exists():
        raise FileExistsError('preserve081 postrun coverage attempt')
    start = time.monotonic()
    RUN.validate_parent()
    for name in RUN.FILES:
        if (RUN.ROOT/name).read_bytes() != (RUN.OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('preserve081 '+name)
    files = ['mobius_density_coverage_081.py', 'test_mobius_density_coverage_081.py',
             'mobius_density_coverage_081_development.json', 'run_mobius_density_coverage_081.py']
    frozen = {name: (RUN.ROOT/name).read_bytes() for name in files}
    if json.loads(frozen['mobius_density_coverage_081_development.json'])['status'] != 'PASS':
        raise ValueError('coverage development incomplete')
    u = max(json.loads((RUN.OUT/'validation_draw.json').read_text())['parents'])
    source = COVER.S.Arithmetic(u//4)
    candidates = json.loads((RUN.OUT/'frozen_candidates.json').read_text())['candidates']
    rows = []
    for candidate in candidates:
        RUN.check_stage(start)
        data = COVER.coverage(candidate['program'], u, source)
        validation = json.loads((RUN.OUT/('validation_'+candidate['id']+'.json')).read_text())
        admitted = next(row for row in validation['rows'] if row['u'] == u)
        primal = Q(data['untouched_prime_block']['signed_contribution'])
        remainder = Q(admitted['certificate']['unlinked'])
        rows.append(dict(id=candidate['id'], program=candidate['program'], certificate=data,
            saved_admitted_unlinked=str(remainder), other_unlinked_contribution=str(remainder-primal),
            exact_frontier_identity='U(u)=B_outer_primes(u)+V(u)',
            next_joint_target='V(u)<=K*u-B_outer_primes(u), uniformly, without separately discarding signed cross terms',
            independent_coverage_admission_pending=True, RH_proved=False))
    for name, content in frozen.items():
        if (RUN.ROOT/name).read_bytes() != content:
            raise ValueError('coverage source changed '+name)
    RUN.check_stage(start)
    result = dict(status='EXACT_COVERAGE_PROPOSALS', diagnostic_parent=u,
        selection_rule='largest already-frozen fresh081 validation parent, same for every candidate',
        rows=rows, constructor_operations=source.meter.ops, elapsed_seconds=time.monotonic()-start,
        peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024,
        independent_admission_pending=True, finite_geometry_is_not_a_cancellation_bound=True,
        frozen_search_unchanged=True, uniform_unlinked_bound_proved=False, RH_proved=False)
    write(path, result)
    RUN.check_stage(start)
    print(json.dumps({k: v for k, v in result.items() if k != 'rows'}))
    return result


if __name__ == '__main__':
    main()
