"""Exact physical coefficient coverage and an untouched actual-prime block.

These finite diagnostics measure kernel geometry, not a bound on its signed
arithmetic sum. They are deliberately separate from the frozen081 search.
"""
from fractions import Fraction as Q
import numpy as np
import mobius_density_packet_081 as S


def dot(left, T, right):
    return sum((left[i]*T[i][j]*right[j] for i in range(len(T)) for j in range(len(T))), Q(0))


def coverage(program, u, arithmetic=None):
    p = S.parse(program)
    horizon = u//min(p['kernel'])
    D = S.OLD.floor_power(u, program['eta'])
    arithmetic = arithmetic or S.Arithmetic(max(horizon, D))
    bank = S.PairBank(program, D, arithmetic)
    mu, least = arithmetic.source.mu, arithmetic.source.least
    sf = np.cumsum(mu[:horizon+1] != 0, dtype=np.int64)
    prime = np.cumsum(least[:horizon+1] == np.arange(horizon+1), dtype=np.int64)
    # least[0]=0, so remove its artificial equality from the prime prefix.
    prime -= 1
    dimension = len(bank.T)
    cuts = sorted({0} | {u//(2**i*d) for i in range(dimension) for d in p['kernel']})
    bands = []
    for left, right in zip(cuts, cuts[1:]):
        vector = [sum((v for d, v in p['kernel'].items() if right <= u//(2**i*d)), Q(0))
                  for i in range(dimension)]
        bands.append(dict(left=left, right=right, vector=vector,
            squarefree=int(sf[right]-sf[left]), primes=int(prime[right]-prime[left])))
    dense_mass, dense_edges, diagonal_mass = Q(0), 0, Q(0)
    for i, left in enumerate(bands):
        n = left['squarefree']
        diagonal = dot(left['vector'], bank.T, left['vector'])
        diagonal_mass += n*abs(diagonal)
        dense_mass += n*(n-1)*abs(diagonal)
        dense_edges += n*(n-1)//2*int(diagonal != 0)
        for right in bands[i+1:]:
            value = dot(left['vector'], bank.T, right['vector'])
            dense_mass += 2*n*right['squarefree']*abs(value)
            dense_edges += n*right['squarefree']*int(value != 0)
    P, N, label_count, nonzero_labels, pc, nc, zc = bank.stats[D]
    wp = min(Q(1), N/P) if P else Q(0)
    wn = min(Q(1), P/N) if N else Q(0)
    removed_mass, weighted_edges, touched_edges = Q(0), Q(0), 0
    for b in range(2, D+1):
        for row in bank.rows[b]:
            w = wp if row['density'] > 0 else wn if row['density'] < 0 else Q(1)
            if not w or not row['kernel']:
                continue
            counts = arithmetic.counts(row['primes'], [u//d for d, _ in row['kernel']])+[0]
            value = Q(0)
            for i, (_, jump) in enumerate(row['kernel']):
                value += jump
                if value:
                    edges = counts[i]-counts[i+1]
                    touched_edges += edges
                    weighted_edges += w*edges
                    removed_mass += w*abs(value)*edges
    if not 0 <= removed_mass <= dense_mass or not 0 <= weighted_edges <= touched_edges <= dense_edges:
        raise ArithmeticError('disjoint weighted graph geometry violated')
    lo, hi = u//5, u//4
    first = [sum((v for d, v in p['kernel'].items() if lo+1 <= u//(2**i*d)), Q(0)) for i in range(dimension)]
    last = [sum((v for d, v in p['kernel'].items() if hi <= u//(2**i*d)), Q(0)) for i in range(dimension)]
    frontier = dict(admitted=False)
    if lo < hi <= horizon and lo >= D and first == last == [Q(-1)]+[Q(0)]*(dimension-1):
        count = int(prime[hi]-prime[lo])
        frontier = dict(admitted=True, lower_exclusive=lo, upper_inclusive=hi,
            prime_count=count, unordered_prime_pairs=count*(count-1)//2,
            per_pair_signed_coefficient=str(2*bank.T[0][0]),
            signed_contribution=str(bank.T[0][0]*count*(count-1)),
            all_pairs_have_gcd_one=True, all_reduced_labels_exceed_D=True,
            packet_removes_none_of_these_pairs=True,
            interpretation='positive actual-prime block remains insideU and must cancel jointly with its complement')
    arithmetic.meter.charge(100*(horizon+1)+1000*len(bands)**2)
    return dict(u=u, D=D, bands=[dict(b, vector=list(map(str, b['vector']))) for b in bands],
        complete_ratio_labels=label_count, nonzero_ratio_labels=nonzero_labels,
        retained_nonzero_ratio_labels=int(wp > 0)*pc+int(wn > 0)*nc+zc,
        weighted_label_count=str(wp*pc+wn*nc+zc),
        unordered_nonzero_offdiagonal_pairs=dense_edges,
        absolute_offdiagonal_coefficient_mass=str(dense_mass), absolute_diagonal_coefficient_mass=str(diagonal_mass),
        retained_nonzero_physical_pairs=touched_edges, weighted_physical_pairs=str(weighted_edges),
        removed_absolute_coefficient_mass=str(removed_mass),
        remaining_absolute_coefficient_mass=str(dense_mass-removed_mass),
        fraction_absolute_mass_removed=str(removed_mass/dense_mass if dense_mass else Q(0)),
        fraction_nonzero_edges_touched=str(Q(touched_edges, dense_edges) if dense_edges else Q(0)),
        untouched_prime_block=frontier, arithmetic_cancellation_bound_proved=False,
        uniform_unlinked_bound_proved=False, RH_proved=False)
