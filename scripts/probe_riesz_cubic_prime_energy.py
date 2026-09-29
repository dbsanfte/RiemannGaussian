#!/usr/bin/env python3
"""Optional enlarged-population cubic-moment diagnostic, never a certificate.

Keep all labels, prime counts, coordinates, exact arithmetic moment signs,
allocation and product phase. Every profile includes its entire exterior.
Widths omit the UNEVALUATED sqrt(E); signed centers do not. Both displayed
endpoints at nominal E=1 are diagnostic only. The population omits earlier
nested core deletions. Do not infer an eventual or zero-free bound.
"""
import argparse
import json
import math
import numpy as np
from probe_riesz_quadratic_prime_energy import probe
from probe_riesz_order10_coordinates import rational_from_identity


def audit_cubic(*, A, D, Q, gram, end, log_moments, **_):
    stop = D.shape[1]
    k = np.arange(1, end, dtype=float)
    logk, lognext = np.log(k)/math.log(end), np.log(k+1)/math.log(end)
    moments = log_moments/math.log(end)**np.arange(1, 4)
    directions, moment_directions = [], []
    gram_residual = D@D.T
    center_vector = np.zeros(len(Q))
    weight_gram = A.T@A
    ev, U = np.linalg.eigh(weight_gram/np.trace(weight_gram))
    regular = np.maximum(ev, 1e-10)
    half = (U*np.sqrt(regular))@U.T
    invhalf = (U*(1/np.sqrt(regular)))@U.T
    results = {}
    for degree in range(1, 4):
        direction = np.sqrt(k)*(logk**degree-lognext**degree)
        moment = moments[:, degree-1].copy()
        for previous, previous_moment in zip(directions, moment_directions):
            projection = float(direction@previous)
            direction -= projection*previous
            moment -= projection*previous_moment
        norm = float(np.linalg.norm(direction))
        direction /= norm
        moment /= norm
        directions.append(direction)
        moment_directions.append(moment)
        cross = D@direction[:stop]
        center_vector += (moment@A)*cross
        gram_residual -= np.outer(cross, cross)
        if degree == 1:
            continue
        normalized = (gram_residual+gram_residual.T)/(2*np.trace(gram_residual))
        middle = half@normalized@half
        ev2, U2 = np.linalg.eigh((middle+middle.T)/2)
        transform = invhalf@((U2*np.sqrt(np.maximum(ev2, 0.)))@U2.T)@invhalf
        candidate = np.linalg.eigh((transform+transform.T)/2)[1]
        rational, steps = rational_from_identity(candidate)
        candidates = dict(previousProfile=Q, balanced=candidate, rationalIdentity=rational)
        scores = {}
        for name, basis in candidates.items():
            orthogonality = float(np.max(np.abs(basis@basis.T-np.eye(len(Q)))))
            assert orthogonality < 1e-10
            transformed = A@basis
            weight_energy = np.sum(transformed**2, axis=0)
            raw = basis.T@D
            residual = raw.copy()
            projections = []
            center = 0.
            for v, m in zip(directions, moment_directions):
                a = raw@v[:stop]
                projections.append(a)
                residual -= a[:, None]*v[None, :stop]
                center += float(m@(transformed@a))
            profile_energy = np.sum(residual**2, axis=1)
            for i, v in enumerate(directions):
                for j, other in enumerate(directions):
                    profile_energy += projections[i]*projections[j]*float(v[stop:]@other[stop:])
            assert float(profile_energy.min()) > -1e-10
            cost = float(math.sqrt(end)*np.sqrt(weight_energy*np.maximum(profile_energy, 0.)).sum())
            assert abs(center-float(center_vector.sum())) < 1e-12
            scores[name] = dict(cost=cost, signedCenter=center,
                                maximumOrthogonalityError=orthogonality)
        results[str(degree)] = dict(scores=scores, rationalRecipe=steps,
                                   allCoordinateColumnsRetained=True)
    # A fixed basis must satisfy the proved cubic width comparison.
    assert results['3']['scores']['previousProfile']['cost'] <= results['2']['scores']['previousProfile']['cost']+1e-10
    print(json.dumps(dict(upper=end, moments={d:r['scores'] for d,r in results.items()})), flush=True)
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', type=int, default=10, choices=[6, 8, 10])
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    cap = math.floor(math.exp(2.03*args.order)/(args.order**2+1))
    result = probe(args.order, cap, False, 54., 10001/20000,
                   coordinate_audit=audit_cubic, log_moment_order=3)
    result['momentTotals'] = {
        d: {name: {k: sum(row['coordinateAudit'][d]['scores'][name][k]
                         for row in result['shells']) for k in ['cost', 'signedCenter']}
            for name in ['previousProfile', 'balanced', 'rationalIdentity']}
        for d in ['2', '3']}
    result['scope'] = __doc__.strip()
    with open(args.output, 'w', encoding='utf-8') as stream:
        json.dump(result, stream, indent=2)
        stream.write('\n')
    print(json.dumps(dict(labels=result['selectedLabels'], moments=result['momentTotals'])))


if __name__ == '__main__':
    main()
