#!/usr/bin/env python3
"""Exact resonant first-transition-moment regression, never proof input.

Native integer unit extraction precedes all joins. No floating estimates,
prime-index residue or asymptotic conclusion is inferred from these rows.
"""
from fractions import Fraction
import json
from pathlib import Path

from probe_arithmetic_operator_pfree_structure import binomial_row, legendre


def main() -> None:
    source = Path('.lake/arithmetic-operator-pfree-structure/probe.json')
    rows = json.loads(source.read_text())['rows']
    records = []
    positive_carry_cells = 0
    for row in rows:
        p, q, D = row['p'], row['q'], row['D']
        if p == 2:
            up, vp, _ = binomial_row(D - 1, p)
            cp = [1] * D
            sp = 1
        else:
            up, vp, cp = binomial_row(D - 1, p)
            sp = legendre(-1, p)
        uq, vq, cq = binomial_row(D - 1, q)
        sq = legendre(-1, q)
        sigma = sp * sq
        atoms = [a * b for a, b in zip(cp, cq)]
        assert atoms[0] == atoms[-1] == 1
        zeroth = first = 0
        crossings = 0
        for k in range(D - 1):
            delta = atoms[k + 1] - sigma * atoms[k]
            if (k + 1) % p and (k + 1) % q:
                assert delta == 0
            else:
                crossings += 1
                jump = sigma ** (k + 1) * delta
                zeroth += jump
                first += (k + 1) * jump
        total = sum(sigma ** k * atom for k, atom in enumerate(atoms))
        boundary = sigma ** (D - 1)
        assert zeroth == boundary - 1
        assert total == D * boundary - first
        assert total == row['resonant_trace']
        assert sum(abs(a) for a in atoms) == D
        positive_carry_cells += sum(a > 0 or b > 0 for a, b in zip(vp, vq))
        records.append({'p': p, 'q': q, 'r': row['r'], 's': row['s'], 'D': D,
                        'boundary': boundary, 'zerothMoment': zeroth,
                        'firstMoment': first, 'trace': total, 'crossings': crossings,
                        'exactNormalizedTrace': [Fraction(total, D).numerator,
                                                 Fraction(total, D).denominator]})
    target = Path('.lake/arithmetic-operator-pfree-resonance')
    target.mkdir(parents=True, exist_ok=True)
    result = {'scope': 'exact finite weighted-jump identity; all probes diagnostic only',
              'nativeRows': len(records), 'positiveCarryCellsRetained': positive_carry_cells,
              'properPowerRows': sum(a['r'] + a['s'] > 2 for a in records),
              'evenRowsWithExplicitBoundary': sum(a['D'] % 2 == 0 for a in records),
              'normalization': 'trace/D=boundary-firstMoment/D; zerothMoment=boundary-1',
              'zeroSourceInferred': False, 'independentArithmeticEstimateInferred': False,
              'rows': records}
    (target / 'probe.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'rows'}, indent=2))


if __name__ == '__main__':
    main()
