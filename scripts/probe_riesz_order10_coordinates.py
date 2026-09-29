#!/usr/bin/env python3
"""Optional coordinate audit of the enlarged order-ten arithmetic cost.

No integer, prime direction or count class is removed. Every candidate is
rescored against the original full arrays, including the exterior profile
cross terms. Costs omit the UNEVALUATED sqrt(E). The floating coordinates
and costs are exploratory, NOT certificates. Rational rotations preserve
exact admissibility in Lean. A separate recipe starts at the exact identity
matrix and approximates the floating balanced candidate using only rational
rotations. The test population also omits earlier nested core deletions.
Nothing here establishes an eventual whole-carrier estimate or zero bound.

Keep outside ordinary CI. Run with OPENBLAS_NUM_THREADS=4 and the repository
NumPy environment. --order 6 or 8 allows a smaller regression run.
"""
import argparse
import json
import math
import numpy as np
from probe_riesz_quadratic_prime_energy import probe


def rational_from_identity(target):
    """Approximate the target by an explicit exact-rational rotation recipe.

    The input is only used to CHOOSE rational parameters. The returned map
    is recomputed as a product of those rotations starting at identity.
    Near-zero entries may be left uneliminated; no coordinate is dropped.
    """
    work = target.copy()
    basis = np.eye(len(target))
    steps = []
    denominator = 2**24
    for i in range(len(target)):
        for j in range(i+1, len(target)):
            x, y = work[i, i], work[j, i]
            if abs(y) < 1e-14:
                continue
            magnitude = math.hypot(x, y)
            parameter = y/(magnitude+x) if x >= 0 else (magnitude-x)/y
            numerator = round(parameter*denominator)
            if numerator == 0:
                continue
            t = numerator/denominator
            c, s = (1-t*t)/(1+t*t), 2*t/(1+t*t)
            rows = work[[i, j], :].copy()
            work[i, :], work[j, :] = c*rows[0]+s*rows[1], -s*rows[0]+c*rows[1]
            cols = basis[:, [i, j]].copy()
            basis[:, i], basis[:, j] = c*cols[:, 0]+s*cols[:, 1], -s*cols[:, 0]+c*cols[:, 1]
            steps.append([i, j, numerator, denominator])
    assert np.max(np.abs(work-np.diag(np.diag(work)))) < 1e-4
    return basis, steps


def audit_coordinates(*, A, D, Q, cross, cross2, lognorm, logdir, v2, norm2,
                      tailnorm, tail2, mixed, gram, end, moments, counts):
    """Choose coordinates, then recompute each cost without discarding modes."""
    stop = D.shape[1]
    gram2 = gram-np.outer(cross2, cross2)/norm2
    gram2 = (gram2+gram2.T)/2
    weight_gram = A.T@A
    wg = weight_gram/np.trace(weight_gram)
    bg = gram2/np.trace(gram2)

    def score(basis):
        orthogonality = float(np.max(np.abs(basis@basis.T-np.eye(len(basis)))))
        assert orthogonality < 1e-10
        transformed = A@basis
        weights = np.sum(transformed**2, axis=0)
        slope = (basis.T@cross)/lognorm
        alpha = (basis.T@cross2)/norm2
        residual = (basis.T@D-slope[:, None]*logdir[None, :]
                    -alpha[:, None]*v2[None, :stop])
        exterior = (slope*slope*tailnorm+alpha*alpha*tail2
                    +2*slope*alpha*mixed)
        profile = np.sum(residual**2, axis=1)+exterior
        assert float(np.min(profile)) > -1e-8
        cost = math.sqrt(end)*np.sqrt(weights*np.maximum(profile, 0.))
        center = float(moments@(transformed@alpha))/math.log(end)**2
        attribution = {
            int(k): float(np.sum(cost*np.divide(
                np.sum(transformed[counts == k]**2, axis=0), weights,
                out=np.zeros_like(weights), where=weights > 0)))
            for k in sorted(set(counts))}
        return dict(cost=float(cost.sum()), center=center,
                    maximumOrthogonalityError=orthogonality,
                    cofactorCountAttribution=attribution,
                    attributionIsNotACountSplitBound=True)

    # Regularization ONLY chooses a basis; no regularized energy is used in
    # the final score, and every eigenvector remains in that score.
    ev, U = np.linalg.eigh(wg)
    regular = np.maximum(ev, 1e-10)
    half = (U*np.sqrt(regular))@U.T
    invhalf = (U*(1/np.sqrt(regular)))@U.T
    middle = half@bg@half
    ev2, U2 = np.linalg.eigh((middle+middle.T)/2)
    middle = (U2*np.sqrt(np.maximum(ev2, 0.)))@U2.T
    transform = invhalf@middle@invhalf
    balanced = np.linalg.eigh((transform+transform.T)/2)[1]

    greedy = Q.copy()
    gg, bb = greedy.T@wg@greedy, greedy.T@bg@greedy
    chosen = np.argsort(np.sqrt(np.maximum(np.diag(gg)*np.diag(bb), 0.)))[-min(64, len(Q)):]
    steps = []
    parameters = [(sign, den) for den in [1, 2, 4, 8, 16, 32, 64] for sign in [-1, 1]]
    for _ in range(256):
        ga, ba = np.diag(gg)[chosen], np.diag(bb)[chosen]
        gc, bc = gg[np.ix_(chosen, chosen)], bb[np.ix_(chosen, chosen)]
        before = np.sqrt(np.maximum(ga*ba, 0.))
        best = (0., None)
        for num, den in parameters:
            t = num/den
            c, s = (1-t*t)/(1+t*t), 2*t/(1+t*t)
            g1 = c*c*ga[:, None]+s*s*ga[None, :]+2*c*s*gc
            g2 = s*s*ga[:, None]+c*c*ga[None, :]-2*c*s*gc
            b1 = c*c*ba[:, None]+s*s*ba[None, :]+2*c*s*bc
            b2 = s*s*ba[:, None]+c*c*ba[None, :]-2*c*s*bc
            gains = (before[:, None]+before[None, :]
                     -np.sqrt(np.maximum(g1*b1, 0.))-np.sqrt(np.maximum(g2*b2, 0.)))
            gains[np.tril_indices(len(chosen))] = -np.inf
            i, j = np.unravel_index(np.argmax(gains), gains.shape)
            if gains[i, j] > best[0]:
                best = (float(gains[i, j]), (int(chosen[i]), int(chosen[j]), num, den, c, s))
        if best[1] is None or best[0] < 1e-11:
            break
        i, j, num, den, c, s = best[1]
        for mat in [gg, bb]:
            rows = mat[[i, j], :].copy()
            mat[i, :], mat[j, :] = c*rows[0]+s*rows[1], -s*rows[0]+c*rows[1]
            cols = mat[:, [i, j]].copy()
            mat[:, i], mat[:, j] = c*cols[:, 0]+s*cols[:, 1], -s*cols[:, 0]+c*cols[:, 1]
        cols = greedy[:, [i, j]].copy()
        greedy[:, i], greedy[:, j] = c*cols[:, 0]+s*cols[:, 1], -s*cols[:, 0]+c*cols[:, 1]
        steps.append(dict(left=i, right=j, parameterNumerator=num, parameterDenominator=den))

    from_identity, identity_steps = rational_from_identity(balanced)
    scores = {name: score(basis) for name, basis in
              [('profile', Q), ('balanced', balanced), ('rationalPairs', greedy),
               ('rationalFromIdentity', from_identity)]}
    old = scores['profile']
    for candidate in scores.values():
        assert abs(candidate['center']-old['center']) < 1e-12
    assert scores['rationalPairs']['cost'] <= old['cost']+1e-10
    result = dict(scores=scores, rationalRotationSteps=steps,
                  identityRotationSteps=identity_steps,
                  identityRecipeColumns=['left', 'right', 'numerator', 'denominator'],
                  allCoordinateColumnsRetained=True, coordinateColumns=len(Q),
                  numericalOrthogonalityIsNotACertificate=True)
    print(json.dumps(dict(upper=end, scores=scores, rotations=len(steps))), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', type=int, default=10, choices=[6, 8, 10])
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    population = math.floor(math.exp(2.03*args.order)/(args.order**2+1))
    result = probe(args.order, population, False, 54., 10001/20000,
                   coordinate_audit=audit_coordinates)
    result['coordinateTotals'] = {
        name: sum(row['coordinateAudit']['scores'][name]['cost'] for row in result['shells'])
        for name in ['profile', 'balanced', 'rationalPairs', 'rationalFromIdentity']}
    result['scope'] = __doc__.strip()
    with open(args.output, 'w', encoding='utf-8') as stream:
        json.dump(result, stream, indent=2)
        stream.write('\n')
    print(json.dumps(dict(selectedLabels=result['selectedLabels'], totals=result['coordinateTotals'])))


if __name__ == '__main__':
    main()
