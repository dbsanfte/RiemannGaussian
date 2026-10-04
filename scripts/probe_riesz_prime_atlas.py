#!/usr/bin/env python3
"""Optional arithmetic/phase atlas of the literal unpaid prime-pair sample.

This enriches ACTUAL primes, not a continuous density or a zero-mode model.
The graph is built without phase or carrier outcome. All signed node charges
are obtained by joining original weighted pair incidences first, with one
half assigned to each leg. Discovery and replication remain separate.

Partial p+-1 factorisation and sample spacing are labelled honestly. Proven
nearest-prime gaps are supplied only for the selected anchors. Permutations,
embeddings and regressions are diagnostics, not arithmetic bounds or proof.
Nothing is imported by Lean, ordinary builds or ordinary CI.
"""

import argparse
from collections import defaultdict
import hashlib
import json
import math
from pathlib import Path
import sys
import time

sys.dont_write_bytecode = True
import gmpy2
import numpy as np
from flint import acb, arb, ctx, fmpz
from scipy.cluster.vq import kmeans2
from scipy.sparse import csr_matrix, diags
from scipy.sparse.csgraph import connected_components, minimum_spanning_tree
from scipy.sparse.linalg import eigsh
from scipy.spatial.distance import cdist

import probe_riesz_pair_structure as pair


def digest(path):
    return dict(path=str(path), sha256=hashlib.sha256(Path(path).read_bytes()).hexdigest())


def small_primes(limit):
    return [p for p in range(2, limit+1)
            if all(p % q for q in range(2, math.isqrt(p)+1))]


SMALL = small_primes(257)
BASES = (2, 3, 5, 7, 11)
VALUATION_BASES = (2, 3, 5, 7, 11, 13)
MODULI = (8, 30, 210)


def factor_profile(n):
    """Exact small-prime valuations; the residual is NOT declared prime."""
    original, residual = n, n
    factors = []
    for p in SMALL:
        k = 0
        while residual % p == 0:
            residual //= p
            k += 1
        if k:
            factors.append([p, k])
    smooth = original//residual
    assert smooth*residual == original
    return dict(factors=factors, knownSmallPart=str(smooth),
        unfactoredResidual=str(residual), residualBitLength=residual.bit_length(),
        knownLogPart=math.log(smooth),
        knownLogFraction=math.log(smooth)/math.log(original) if original > 1 else 0.,
        distinctKnownFactors=len(factors), knownFactorMultiplicity=sum(k for _, k in factors),
        knownDivisorLog=math.fsum(math.log(k+1) for _, k in factors),
        smallPartSquarefulExcess=sum(k-1 for _, k in factors), trialLimit=257,
        completeFactorisation=(residual == 1), residualPrimalityAsserted=False)


def arithmetic_features(p):
    minus, plus = factor_profile(p-1), factor_profile(p+1)
    b = p.bit_length()
    legendre = []
    for a in BASES:
        v = pow(a, (p-1)//2, p)
        assert v in (0, 1, p-1)
        legendre.append(0 if v == 0 else (1 if v == 1 else -1))
    bits = dict(bitLength=b, hammingWeight=p.bit_count(),
        standardizedBitBalance=(p.bit_count()-b/2)/math.sqrt(b/4),
        leadingFraction=(p-(1 << (b-1)))/(1 << (b-1)))
    for lag in (1, 2, 4, 8):
        mask = (1 << max(b-lag, 0))-1
        bits[f'bitAgreementLag{lag}'] = (1-((p ^ (p >> lag)) & mask).bit_count()/(b-lag)
                                       if b > lag else None)
    return dict(minus=minus, plus=plus, residues={str(m): p % m for m in MODULI},
        legendre=dict(zip(map(str, BASES), legendre)),
        legendreColour=sum((v == 1) << i for i, v in enumerate(legendre)), bits=bits)


def neighbour(p, direction):
    """Every skipped candidate has a definite composite verdict.

    A probable-prime verdict alone is never accepted as a neighbour.
    """
    q, trials = p+2*direction, 0
    while q >= 3:
        trials += 1
        if gmpy2.is_probab_prime(q, 32) and fmpz(q).is_prime():
            return dict(prime=str(q), gap=abs(q-p), oddCandidatesExamined=trials,
                        provedByFLINT=True, provedInLean=False)
        q += 2*direction
    return dict(prime='2', gap=p-2, oddCandidatesExamined=trials,
                provedByFLINT=True, provedInLean=False)


def build_nodes(samples, heights):
    nodes, index = [], {}
    for row in samples['rows']:
        for side, role in (('left', 'largest'), ('right', 'smaller')):
            pp = [int(p) for p in row[side]['primes']]
            if len(set(pp)) != len(pp):
                raise ValueError('Repeated sample marks need incidence multiplicities, not merged nodes')
            ordered = sorted(pp)
            for position, p in enumerate(pp):
                # This dataset consists of disjoint boxes and no repeated
                # accepted integer. Do not silently merge dependent marks.
                if str(p) in index:
                    raise ValueError('Repeated prime across boxes; define incidence-aware reuse first')
                n = len(nodes)
                index[str(p)] = n
                ball = arb(p).log()
                lp = float(ball.mid())
                phases, err = {}, 0.
                for y in heights:
                    ph = acb(0, -arb(y)*ball).exp()
                    phases[str(y)] = pair.encode(complex(float(ph.real.mid()), float(ph.imag.mid())))
                    for radius in (ph.real.rad(), ph.imag.rad()):
                        # A 1200-bit Arb radius underflows binary64. Round
                        # its bound UP, never report a false zero enclosure.
                        upper = math.nextafter(float(radius.upper()), math.inf)
                        assert radius <= arb(upper)
                        err = max(err, upper)
                rank = ordered.index(p)
                spacing = dict(sortedSampleRank=rank,
                    lowerAcceptedSampleGap=str(p-ordered[rank-1]) if rank else None,
                    upperAcceptedSampleGap=str(ordered[rank+1]-p) if rank+1 < len(ordered) else None,
                    isConsecutivePrimeGap=False)
                nodes.append(dict(id=n, prime=str(p), N=row['N'], seed=row['seed'],
                    box=row['box'], role=role, targetShare=row['share'],
                    logLower=row[side]['logLower'], logPrime=lp,
                    logOffset=lp-row[side]['logLower'], position=position,
                    arithmetic=arithmetic_features(p), phases=phases,
                    phaseArbRadiusUpper=err, sampledSpacing=spacing,
                    phaseFloatRoundingIncludedInArbRadius=False,
                    nearestPrimes=None, charges={}, populationEstimatedCharges={},
                    parentSamplePrimalityProvedByFLINT=row[side]['provedByFLINT'],
                    primalityProvedInLean=False))
        print(json.dumps(dict(event='primeFeatures', N=row['N'], seed=row['seed'],
            box=row['box'], nodes=len(nodes))), flush=True)
    return nodes, index


def neighbour_anchors(nodes, budget, cache_path):
    cache = json.loads(cache_path.read_text()) if cache_path.exists() else {}
    groups = defaultdict(list)
    for n in nodes:
        groups[(n['N'], n['seed'], n['box'], n['role'])].append(n)
    # Spread anchors over all boxes/roles rather than selecting by a target.
    ordered = [v[0] for _, v in sorted(groups.items())]
    for n in ordered[:budget]:
        p = int(n['prime'])
        if n['prime'] not in cache:
            start = time.monotonic()
            cache[n['prime']] = dict(previous=neighbour(p, -1), next=neighbour(p, 1),
                                     elapsedSeconds=time.monotonic()-start)
            cache_path.write_text(json.dumps(cache, indent=2)+'\n')
        n['nearestPrimes'] = cache[n['prime']]
        for key, direction in (('previous', -1), ('next', 1)):
            entry = n['nearestPrimes'][key]
            q = int(entry['prime'])
            assert (q-p)*direction > 0 and abs(q-p) == entry['gap']
            assert entry['provedByFLINT'] and not entry['provedInLean']
        print(json.dumps(dict(event='provenPrimeNeighbours', id=n['id'],
            previousGap=n['nearestPrimes']['previous']['gap'],
            nextGap=n['nearestPrimes']['next']['gap'])), flush=True)
    return cache


def feature_table(nodes):
    features, arrays = [], []

    def add(name, family, values, kind='scalar', graph=True, interactions=False):
        features.append(dict(name=name, family=family, kind=kind,
                             usedInStructuralGraph=graph, interactionEligible=interactions))
        arrays.append(values)

    for sign in ('minus', 'plus'):
        for p in VALUATION_BASES:
            add(f'v{p}(p{("-" if sign == "minus" else "+")}1)', sign,
                [dict(n['arithmetic'][sign]['factors']).get(p, 0) for n in nodes], interactions=True)
        for key in ('knownLogPart', 'distinctKnownFactors', 'knownDivisorLog', 'smallPartSquarefulExcess'):
            add(f'{sign}.{key}', sign, [n['arithmetic'][sign][key] for n in nodes], interactions=True)
    for a in BASES:
        add(f'Legendre({a}/p)', 'quadratic', [n['arithmetic']['legendre'][str(a)] for n in nodes], interactions=True)
    for key in ('standardizedBitBalance', 'bitAgreementLag1', 'bitAgreementLag2',
                'bitAgreementLag4', 'bitAgreementLag8'):
        add(key, 'digits', [n['arithmetic']['bits'][key] for n in nodes], interactions=True)
    for m in MODULI:
        for residue in sorted({n['arithmetic']['residues'][str(m)] for n in nodes}):
            add(f'p mod {m} = {residue}', f'mod{m}',
                [int(n['arithmetic']['residues'][str(m)] == residue) for n in nodes], 'category')
    X = np.array(arrays, dtype=float).T
    nonconstant = X.std(axis=0) > 1e-14
    features = [f for f, keep in zip(features, nonconstant) if keep]
    X = X[:, nonconstant]
    scaled = (X-X.mean(axis=0))/X.std(axis=0)
    graph = scaled.copy()
    families = [f['family'] for f in features]
    for family in set(families):
        columns = [i for i, f in enumerate(families) if f == family]
        # Give each arithmetic family equal total squared-distance scale.
        graph[:, columns] /= math.sqrt(len(columns))
    return X, scaled, graph, features


def structural_topology(X, nodes, neighbours):
    distances = cdist(X, X)
    np.fill_diagonal(distances, np.inf)
    k = min(neighbours, len(nodes)-1)
    order = np.argsort(distances, axis=1)[:, :k]
    radius = np.median(np.take_along_axis(distances, order, axis=1)[:, -1])
    W = np.zeros_like(distances)
    for i, js in enumerate(order):
        W[i, js] = np.exp(-distances[i, js]**2/(2*radius**2))
    W = np.maximum(W, W.T)
    count, components = connected_components(csr_matrix(W))
    degree = W.sum(axis=1)
    L = diags(np.ones(len(nodes)))-diags(1/np.sqrt(degree))@csr_matrix(W)@diags(1/np.sqrt(degree))
    eigenvalues, eigenvectors = eigsh(L, k=min(8, len(nodes)-2), which='SM', tol=1e-8,
                                    v0=np.random.default_rng(731).normal(size=len(nodes)))
    sort = np.argsort(eigenvalues)
    eigenvalues, eigenvectors = eigenvalues[sort], eigenvectors[:, sort]
    for i in range(eigenvectors.shape[1]):
        if eigenvectors[np.argmax(abs(eigenvectors[:, i])), i] < 0:
            eigenvectors[:, i] *= -1
    positive = np.flatnonzero(eigenvalues > 1e-7)
    if len(positive) < 2:
        raise ValueError('Not enough nonconstant graph directions; do not invent an embedding')
    diffusion = eigenvectors[:, positive[:2]]/np.sqrt(degree[:, None])
    _, _, vt = np.linalg.svd(X, full_matrices=False)
    pca = (X-X.mean(axis=0))@vt[:2].T
    _, labels = kmeans2(pca, min(12, len(nodes)//8), minit='++', seed=731, iter=40)
    edges = [[int(i), int(j), float(W[i, j]), float(distances[i, j])]
             for i, j in zip(*np.where(np.triu(W, 1) > 0))]
    finite = distances.copy()
    np.fill_diagonal(finite, 0.)
    # Distinct feature vectors here have positive distances. An exact
    # duplicate would require a separately recorded zero-length merger.
    if np.any(np.triu(finite == 0, 1)):
        raise ValueError('Duplicate structural vectors need zero-length MST edges')
    tree = minimum_spanning_tree(csr_matrix(finite)).tocoo()
    merges = sorted([[float(d), int(i), int(j)] for i, j, d in zip(tree.row, tree.col, tree.data)])
    edge_lengths = np.array([e[3] for e in edges])
    levels = []
    for percentile in (0, 10, 25, 50, 75, 90, 100):
        cut = float(np.percentile(edge_lengths, percentile))
        A = csr_matrix(np.where((W > 0) & (distances <= cut), 1., 0.))
        c, _ = connected_components(A)
        e = A.nnz//2
        levels.append(dict(edgeDistanceThreshold=cut, vertices=len(nodes), edges=e,
                           components=c, graphCycleRank=e-len(nodes)+c))
    for i, n in enumerate(nodes):
        n.update(pca=pca[i].tolist(), diffusion=diffusion[i].tolist(),
                 community=int(labels[i]), component=int(components[i]))
    return dict(method='Phase/outcome-free, family-balanced structural k-nearest-neighbour graph',
        neighbourCount=k, vertices=len(nodes), edges=edges, components=count,
        laplacianEigenvalues=eigenvalues.tolist(), affinityRadius=float(radius),
        graphFiltration=levels, singleLinkageMST=merges,
        lowDimensionalCoordinatesAreProjections=True,
        graphCycleRankIsNotHigherPersistentHomology=True,
        graphContainsPhaseOrCarrierOutcome=False), W


def carrier_incidence(nodes, index, samples, heights, parent_report):
    pairs, cases = [], []
    for row in samples['rows']:
        pp = [int(p) for p in row['left']['primes']]
        qq = [int(q) for q in row['right']['primes']]
        reference = row['left']['logLower']+row['right']['logLower']+1
        c, weights, _, _ = pair.prepared_sample(row['N'], tuple(pp), tuple(qq), reference)
        denominator = np.abs(weights).sum()
        counts = [pair.stopped_count(row[s]) for s in ('left', 'right')]
        N = row['N']
        scale_log = ((N+1)*math.log(pair.U)+math.log(N)-1.5*reference+
            N*math.log(reference)-math.lgamma(N+1)+sum(v['logPrimeCountEstimate'] for v in counts))
        estimated_scale = math.exp(scale_log)/weights.size
        node_ids = [[index[str(p)] for p in pp], [index[str(q)] for q in qq]]
        for y in heights:
            pl = np.array([
                complex(nodes[i]['phases'][str(y)]['re'], nodes[i]['phases'][str(y)]['im'])
                for i in node_ids[0]])
            qr = np.array([complex(nodes[i]['phases'][str(y)]['re'], nodes[i]['phases'][str(y)]['im'])
                           for i in node_ids[1]])
            _, keep = pair.complete_periods(N, c['T'], y)
            keep &= c['central']
            atoms = np.where(keep, weights*pl[:, None]*qr[None, :], 0.)
            signed = atoms.sum()/denominator
            for ids, charges in ((node_ids[0], atoms.sum(axis=1)/2),
                                 (node_ids[1], atoms.sum(axis=0)/2)):
                for i, value in zip(ids, charges):
                    nodes[i]['charges'][str(y)] = pair.encode(value/denominator)
                    nodes[i]['populationEstimatedCharges'][str(y)] = pair.encode(value*estimated_scale)
            reconstructed = sum(complex(nodes[i]['charges'][str(y)]['re'],
                nodes[i]['charges'][str(y)]['im']) for ids in node_ids for i in ids)
            assert abs(reconstructed-signed) < 1e-12
            previous = next(v for v in parent_report['sampled'] if
                (v['N'], v['seed'], v['box'], v['height']) == (N, row['seed'], row['box'], y))
            assert abs(signed-complex(previous['relativeSigned']['re'], previous['relativeSigned']['im'])) < 1e-12
            cases.append(dict(N=N, seed=row['seed'], box=row['box'], height=y,
                relativeSigned=pair.encode(signed), weightedPairs=int(keep.sum()),
                chargeReplayDifference=float(abs(reconstructed-signed)),
                complexPhaseAndAllMasksRetained=True))
        for i, pid in enumerate(node_ids[0]):
            for j, qid in enumerate(node_ids[1]):
                pairs.append(dict(largest=pid, smaller=qid, N=N, seed=row['seed'], box=row['box'],
                    T=float(c['T'][i, j]), smallerShare=float(c['share'][i, j]),
                    coefficientOverN=float(c['defect'][i, j]/N), regime=int(c['regime'][i, j]),
                    allocation=float(c['allocated'][i, j]), relativeWeight=float(weights[i, j]/denominator),
                    populationEstimatedWeight=float(weights[i, j]*estimated_scale),
                    retainedAtHeight={str(y): bool(c['central'][i, j] and
                        pair.complete_periods(N, c['T'][i:i+1, j:j+1], y)[1][0, 0])
                        for y in heights}))
    return pairs, cases


def geometry_projectors(nodes):
    groups = defaultdict(list)
    for i, n in enumerate(nodes):
        groups[(n['N'], n['seed'], n['box'], n['role'])].append(i)
    projectors, permutation_blocks = [], []
    for key, ids in sorted(groups.items()):
        ids = np.array(ids)
        x = np.array([nodes[i]['logOffset'] for i in ids])
        x -= x.mean()
        Q, _ = np.linalg.qr(np.column_stack([np.ones(len(ids)), x, x*x]))
        projectors.append((ids, Q))
        # Conditioning on coarse position prevents an entire log interval
        # being permuted as though its phase were position-independent.
        permutation_blocks.extend(np.array_split(ids[np.argsort(x)], 4))
    return projectors, permutation_blocks


def project_geometry(values, projectors):
    result = values.copy()
    for ids, Q in projectors:
        result[ids] -= Q@(Q.T@result[ids])
    return result


def complex_field(nodes, key, y):
    return np.array([complex(n[key][str(y)]['re'], n[key][str(y)]['im']) for n in nodes])


def association_scan(nodes, scaled, features, W, heights, permutations):
    """Exploratory, within-prime-block tests; never independent pair tests.

    Phase is exactly determined by log p. Polynomial projection and quartile
    shuffles control coarse location only, NOT conditioning on exact log p.
    Ranks below are empirical diagnostic references, not certified p-values.
    """
    projectors, blocks = geometry_projectors(nodes)
    design, names = [scaled], [dict(f, interaction=False) for f in features]
    eligible = [i for i, f in enumerate(features) if f['interactionEligible']]
    products = []
    for i, a in enumerate(eligible):
        for b in eligible[i+1:]:
            product = scaled[:, a]*scaled[:, b]
            if product.std() > 1e-12:
                products.append(product)
                names.append(dict(name=f"{features[a]['name']} × {features[b]['name']}",
                    family='interaction', interaction=True,
                    parents=[features[a]['name'], features[b]['name']]))
    if products:
        design.append(np.array(products).T)
    X = project_geometry(np.column_stack(design), projectors)
    results, graph_results = [], []
    seeds = sorted({n['seed'] for n in nodes})
    for seed in seeds:
        ids = np.flatnonzero([n['seed'] == seed for n in nodes])
        remap = {i: j for j, i in enumerate(ids)}
        local_blocks = [np.array([remap[i] for i in b]) for b in blocks if b[0] in remap]
        local_projectors = [(np.array([remap[i] for i in v]), Q) for v, Q in projectors
                            if v[0] in remap]
        Xi = X[ids]
        nx = np.linalg.norm(Xi, axis=0)
        valid = nx > 1e-10
        Xi, nx = Xi[:, valid], nx[valid]
        local_names = [name for name, good in zip(names, valid) if good]
        Wi = W[np.ix_(ids, ids)]
        for height in heights:
            for target in ('phase', 'signedRealCharge'):
                raw = complex_field(nodes, 'phases' if target == 'phase' else 'charges', height)[ids]
                if target == 'signedRealCharge':
                    raw = raw.real
                observed = project_geometry(raw, local_projectors)
                norm = np.linalg.norm(observed)
                if norm <= 1e-18:
                    raise ValueError('Degenerate phase/charge field needs an explicit separate audit')
                corr = Xi.T@observed/(nx*norm)
                rng = np.random.default_rng(931+int(height)*7+seed)
                null_raw = np.repeat(raw[:, None], permutations, axis=1)
                for k in range(permutations):
                    order = np.arange(len(ids))
                    for block in local_blocks:
                        order[block] = rng.permutation(block)
                    null_raw[:, k] = raw[order]
                null = project_geometry(null_raw, local_projectors)
                null_norms = np.linalg.norm(null, axis=0)
                null_corr = Xi.T@null/(nx[:, None]*null_norms[None, :])
                maximum = np.max(np.abs(null_corr), axis=0)
                for j, feature in enumerate(local_names):
                    score = abs(corr[j])
                    results.append(dict(seed=seed, height=height, target=target,
                        feature=feature['name'], interaction=feature.get('interaction', False),
                        correlation=pair.encode(corr[j]), score=float(score),
                        individualRank=float((1+np.count_nonzero(np.abs(null_corr[j]) >= score))/(permutations+1)),
                        maxStatisticRank=float((1+np.count_nonzero(maximum >= score))/(permutations+1))))
                # Residual field agreement across the independently built
                # graph. This is not a large-sieve or spectral-gap estimate.
                def graph_score(v):
                    return (len(ids)*np.sum(np.conj(v)*(Wi@v), axis=0).real /
                            (Wi.sum()*np.sum(np.abs(v)**2, axis=0)))
                value, null_scores = float(graph_score(observed)), graph_score(null)
                graph_results.append(dict(seed=seed, height=height, target=target,
                    residualGraphAgreement=value,
                    twoSidedPermutationRank=float((1+np.count_nonzero(abs(null_scores) >= abs(value)))/(permutations+1)),
                    permutations=permutations))
            print(json.dumps(dict(event='associationScan', seed=seed, height=height,
                features=len(local_names), permutations=permutations)), flush=True)
    replicated = []
    by_key = defaultdict(list)
    for row in results:
        by_key[(row['height'], row['target'], row['feature'])].append(row)
    for key, rows in by_key.items():
        if len(rows) != len(seeds) or any(r['maxStatisticRank'] > .05 for r in rows):
            continue
        correlations = [complex(r['correlation']['re'], r['correlation']['im']) for r in rows]
        agreement = min((a*np.conj(b)).real/(abs(a)*abs(b)) for a in correlations for b in correlations)
        if agreement > math.sqrt(.5):
            replicated.append(dict(height=key[0], target=key[1], feature=key[2],
                sameHeightIndependentSeeds=seeds, orientationAgreement=float(agreement),
                maxStatisticRanks=[r['maxStatisticRank'] for r in rows],
                parameterRole='discovery' if key[0] in heights[:2] else 'held-out height'))
    discovery = {(r['target'], r['feature']) for r in replicated if r['height'] in heights[:2]}
    validated = [r for r in replicated if r['height'] in heights[2:] and
                 (r['target'], r['feature']) in discovery]
    return dict(featuresTested=len(names), mainFeatures=len(features), interactions=len(names)-len(features),
        records=results, graphAgreement=graph_results, sameHeightSeedReplication=replicated,
        discoveryAndHeldOutReplication=validated,
        discoveryHeights=heights[:2], heldOutHeights=heights[2:],
        controls=['N × seed × log-box × role block', 'constant/linear/quadratic log-offset projection',
                  'permutations only within log-offset quartiles of each prime block',
                  'max statistic over all features/interactions within each seed/height/target'],
        permutationUnit='prime, not Cartesian pair', permutations=permutations,
        phaseIsDeterministicGivenExactLog=True, controlsExactLogPosition=False,
        heldOutHeightsAreNotIndependentSamples=True,
        ranksAreExploratoryNotProbabilityCertificates=True,
        growingOrdersOrFullPopulationNotTested=True)


def community_ledger(nodes, heights):
    """Each original atom spends half on each leg. Sum first, then price."""
    ledgers = []
    for y in heights:
        for seed in sorted({n['seed'] for n in nodes}):
            communities = []
            for community in sorted({n['community'] for n in nodes}):
                selected = [n for n in nodes if n['seed'] == seed and n['community'] == community]
                values = [complex(n['populationEstimatedCharges'][str(y)]['re'],
                                  n['populationEstimatedCharges'][str(y)]['im']) for n in selected]
                communities.append(dict(community=community, nodes=len(selected),
                    joinedEstimatedSourceCharge=pair.encode(sum(values)),
                    sumNodeAbsoluteCharge=float(sum(map(abs, values))),
                    oneSidedJoinedPrice=max(sum(values).real, 0.)))
            ledgers.append(dict(height=y, seed=seed, communities=communities,
                joinedEstimatedSourceCharge=pair.encode(sum(complex(c['joinedEstimatedSourceCharge']['re'],
                    c['joinedEstimatedSourceCharge']['im']) for c in communities)),
                ordinaryBuildOrCofinalFloorCredit=0))
    return ledgers


def regressions():
    for n in (1, 2**7*3**4*17*1009, 257**3, 1_000_003**2):
        f = factor_profile(n)
        assert int(f['knownSmallPart'])*int(f['unfactoredResidual']) == n
        assert math.prod(p**k for p, k in f['factors']) == int(f['knownSmallPart'])
    a = arithmetic_features(257)
    assert a['minus']['factors'] == [[2, 8]] and a['plus']['factors'] == [[2, 1], [3, 1], [43, 1]]
    assert a['legendre']['2'] == 1
    assert neighbour(101, -1)['prime'] == '97'
    assert neighbour(101, 1)['prime'] == '103'
    toy = [dict(N=1, seed=1, box=1, role='largest', logOffset=i/8) for i in range(8)]
    projectors, blocks = geometry_projectors(toy)
    polynomial = np.array([1+2*n['logOffset']+3*n['logOffset']**2 for n in toy])
    assert np.linalg.norm(project_geometry(polynomial, projectors)) < 1e-12
    assert sorted(i for b in blocks for i in b) == list(range(8))
    return dict(exactSmallFactorReconstruction=True, quadraticCharacterRegression=True,
        provenPrimeNeighbourRegression=True, geometryProjectionRegression=True,
        statisticalTestsAreDiagnostics=True)


def render(report, path):
    # Standalone, local viewer. No CDN, telemetry, web service or CI hook.
    payload = json.dumps(report, separators=(',', ':'), allow_nan=False).replace('<', '\\u003c')
    template = r'''<!doctype html>
<html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Retained prime-pair arithmetic atlas</title>
<style>
:root{color-scheme:dark;--ink:#e5edf6;--muted:#a6b7c9;--line:#314559;--blue:#71bada;--coral:#f0a181}
.sections>.card{min-width:0}.scroll{max-width:100%}
*{box-sizing:border-box}body{margin:0;background:#101923;color:var(--ink);font:15px/1.55 system-ui,sans-serif}main{max-width:1350px;margin:auto;padding:30px 24px}h1{font-size:30px;line-height:1.2;margin:5px 0 15px}h2{font-size:20px;margin:0 0 12px}h3{font-size:16px}p{margin:8px 0}a{color:#9bd5ff}small,.muted{color:var(--muted)}.kicker{letter-spacing:.1em;text-transform:uppercase;font-size:12px;color:var(--blue)}.scope{border-left:4px solid var(--coral);padding:10px 18px;background:#1c2835}.cards{display:grid;grid-template-columns:repeat(4,1fr);gap:12px;margin:22px 0}.card{background:#172432;border:1px solid var(--line);border-radius:8px;padding:14px}.number{font-size:24px;font-weight:600}.toolbar{display:flex;gap:12px;flex-wrap:wrap;align-items:end;margin-bottom:14px}label{display:flex;flex-direction:column;font-size:12px;color:var(--muted)}select,button{font:inherit;padding:8px 10px;border:1px solid #506479;border-radius:5px;background:#1a2a3a;color:var(--ink);max-width:100%}button{cursor:pointer}label.check{flex-direction:row;gap:6px;align-items:center;padding:9px 0}.layout{display:grid;grid-template-columns:minmax(0,2.2fr) minmax(270px,1fr);gap:16px}.plotarea{position:relative;min-width:0}canvas{display:block;width:100%;height:520px;background:#101b28;border:1px solid var(--line);border-radius:8px;touch-action:none;cursor:crosshair}#legend{min-height:24px;font-size:13px;color:var(--muted)}#hover{min-height:62px;overflow-wrap:anywhere;font-size:13px}#detail{height:645px;overflow:auto;overflow-wrap:anywhere}#detail ul{padding-left:18px}.prime{font:12px/1.65 ui-monospace,monospace;overflow-wrap:anywhere;padding:10px;background:#0f1923;border-radius:4px}.detailrow{border-bottom:1px solid var(--line);padding:8px 0}.sections{display:grid;grid-template-columns:1.6fr 1fr;gap:16px;margin-top:18px}.scroll{overflow:auto}table{border-collapse:collapse;width:100%;font-size:12px}td,th{text-align:left;padding:8px 5px;border-bottom:1px solid var(--line)}th{color:var(--muted)}#associations td:first-child{min-width:190px}details{margin-top:16px}summary{cursor:pointer}footer{margin-top:22px;color:var(--muted);font-size:13px}#status{font-size:13px;color:var(--muted);margin:8px 0}.hint{border:1px solid var(--line);padding:9px 12px;border-radius:5px}code{overflow-wrap:anywhere}
@media(max-width:800px){main{padding:20px 12px}h1{font-size:25px}.layout,.sections{grid-template-columns:1fr}.cards{grid-template-columns:repeat(2,1fr)}canvas{height:390px}#detail{height:auto;max-height:500px}.toolbar{gap:8px}.toolbar label{max-width:100%}select{width:100%}}
</style><main>
<div class="kicker">Optional numerical discovery · actual primes · local research</div>
<h1>Retained prime-pair arithmetic atlas</h1>
<p>Explore the unpaid balanced-pair population through arithmetic characteristics, complex phase, signed weight and neighbourhood geometry.</p>
<div class="scope"><strong>Exploration, not a floor certificate.</strong> These are sampled actual primes in disjoint interior log boxes at order 256. They do not cover the retained population. Heights are diagnostic controls, not claimed off-critical zero ordinates. The independent cofinal <code>0.0798</code> upper bound remains open.</div>
<div class="cards"><div class="card"><div class="number" id="primeCount"></div><small>distinct actual primes</small></div><div class="card"><div class="number" id="pairCount"></div><small>literal pair incidences per height</small></div><div class="card"><div class="number" id="featureCount"></div><small>arithmetic features, before interactions</small></div><div class="card"><div class="number" id="repCount"></div><small>discovery + held-out replicated candidates</small></div></div>
<div class="toolbar">
<label>Coordinates<select id="view"><option value="pca">Arithmetic feature projection</option><option value="diffusion">Structural graph projection</option><option value="log">Prime log position</option><option value="pairs">Pair total-log / share geometry</option></select></label>
<label>Height<select id="height"></select></label><label>Seed<select id="seed"><option value="all">Both seeds</option></select></label>
<label>Leg<select id="role"><option value="all">Both prime legs</option><option value="largest">Largest prime</option><option value="smaller">Smaller prime</option></select></label>
<label>Colour<select id="colour"><option value="phase">Complex phase</option><option value="charge">Signed real incidence charge</option><option value="legendre">Quadratic-character colour</option><option value="residue">Residue mod 210</option><option value="minus">Known small-factor log fraction of p−1</option><option value="plus">Known small-factor log fraction of p+1</option><option value="community">Structural community</option></select></label>
<label class="check"><input id="edges" type="checkbox">Neighbour edges</label><button id="fit">Fit view</button><button id="clear">Clear selection</button>
</div><div id="legend"></div><div id="status"></div>
<div class="layout"><div class="plotarea"><canvas id="plot" width="1040" height="650" aria-label="Interactive arithmetic and phase atlas"></canvas><p id="hover">Hover for a prime or pair; click to inspect it. Wheel to zoom, drag to pan.</p><p class="hint">The structural graph uses p±1 valuations and partial factor profiles, quadratic characters, residues and digit features. It excludes phase, signed charge, prime size, seed and leg role. Projections and graph cycles do not establish a cancellation theorem.</p></div>
<aside id="detail" class="card"><h2>Inspect the arithmetic</h2><p>Select a point for the actual prime, partial factorisation, residue/character data, phase and retained signed charge.</p><p>True consecutive-prime neighbours are proved by FLINT only for the designated anchors. Gaps between accepted sample marks are a different quantity.</p></aside></div>
<div class="sections"><section class="card"><h2>Structure-to-phase / charge diagnostics</h2><p class="muted">Feature tests include all pairwise scalar interactions. The rank below uses the maximum statistic across those features. Discovery: heights 54, 65. Held out: 100, 142. Replication requires the same feature and height across both seeds with matching orientation.</p><div id="candidateSummary"></div><div class="scroll"><table id="associations"></table></div><p class="muted">Within-box polynomial log-position controls and quartile shuffles are coarse controls. Phase is exactly determined by log p; these tests do not condition on its exact value. Signed incidence charges share their opposite-prime marginal. Height reuse is not independent sampling.</p></section>
<section class="card"><h2>Neighbourhood topology</h2><p class="muted">Filtration of the structural neighbour graph. Cycle rank is E−V+components; it is not higher persistent homology.</p><div class="scroll"><table id="filtration"></table></div><div id="graphAgreement"></div><p class="muted">The separate single-linkage MST records 0-dimensional component mergers in the full structural metric. Colouring either projection does not change the graph.</p></section></div>
<details class="card"><summary>Coverage, prime quality and provenance</summary><p>“Prime quality” here means explicit measurable attributes, not a ranking of how good a prime is: valuations and factors of p±1 found by trial division through 257; Legendre symbols for 2, 3, 5, 7, 11; residues; digit balance; sample spacing; and proven neighbour gaps where measured. Unfactored residuals are not declared prime.</p><p>Quadratic-character colour is a five-bit visual classifier. It is distinct from the repository's prime-power/mixed-support arithmetic colour, which is constant for these ordinary-prime pair legs.</p><p>Each pair's exact weighted complex contribution spends one half on each node. Node charges therefore sum to the original pair sum without double counting. Population-scaled charges use stopped-sampling count estimates and cover these boxes only; they are not certified estimates of the whole carrier.</p><pre id="provenance" style="white-space:pre-wrap;overflow-wrap:anywhere"></pre></details>
<footer><a href="atlas.json">Full atlas data</a> · <a href="../riesz-pair-structure/scan.html">Parent pair detector</a> · <a href="../../docs/zeta-riesz-prime-atlas.md">Investigation note</a><p>No build, Lean proof, ordinary CI or public theorem-explorer dependency is added.</p></footer>
</main><script>
const R=PAYLOAD,$=id=>document.getElementById(id),C=$('plot'),X=C.getContext('2d');
let screen=[],points=[],chosen=null,zoom=1,pan=[0,0],drag=null,extent=null,moved=false;
const cx=v=>({re:v.re,im:v.im}),phaseAngle=v=>Math.atan2(v.im,v.re),fmt=(v,d=5)=>Number(v).toPrecision(d),complexText=v=>`${fmt(v.re)} ${v.im>=0?'+':'−'} ${fmt(Math.abs(v.im))}i`,phaseColour=v=>`hsl(${(phaseAngle(v)*180/Math.PI+360)%360} 73% 63%)`,signColour=(x,m)=>x>=0?`rgba(240,161,129,${.24+.76*Math.min(1,Math.abs(x)/m)})`:`rgba(113,186,218,${.24+.76*Math.min(1,Math.abs(x)/m)})`;
function mul(a,b){return {re:a.re*b.re-a.im*b.im,im:a.re*b.im+a.im*b.re}}
function pairsAtHeight(p){let v=mul(R.nodes[p.largest].phases[$('height').value],R.nodes[p.smaller].phases[$('height').value]);return {re:p.relativeWeight*v.re,im:p.relativeWeight*v.im}}
function eligible(n){return ($('seed').value==='all'||n.seed==$('seed').value)&&($('role').value==='all'||n.role==$('role').value)}
function coordinates(n){return $('view').value==='log'?[n.logOffset,n.logPrime/n.N]:n[$('view').value]}
function setupPoints(){if($('view').value==='pairs'){points=R.pairs.filter(p=>($('seed').value==='all'||p.seed==$('seed').value)&&p.retainedAtHeight[$('height').value]).map(p=>({x:p.T/p.N,y:p.smallerShare,item:p,pair:true}))}else points=R.nodes.filter(eligible).map(n=>({x:coordinates(n)[0],y:coordinates(n)[1],item:n,pair:false}));let xs=points.map(p=>p.x),ys=points.map(p=>p.y);extent={minx:Math.min(...xs),maxx:Math.max(...xs),miny:Math.min(...ys),maxy:Math.max(...ys)};if(extent.maxx===extent.minx)extent.maxx++;if(extent.maxy===extent.miny)extent.maxy++;screen=points.map(p=>({...p,sx:50+(p.x-extent.minx)/(extent.maxx-extent.minx)*(C.width-85),sy:C.height-45-(p.y-extent.miny)/(extent.maxy-extent.miny)*(C.height-85)}))}
function colourFor(p,m){let n=p.pair?R.nodes[p.item.largest]:p.item,mode=$('colour').value,y=$('height').value;if(mode==='phase')return phaseColour(p.pair?mul(n.phases[y],R.nodes[p.item.smaller].phases[y]):n.phases[y]);if(mode==='charge')return signColour(p.pair?pairsAtHeight(p.item).re:n.charges[y].re,m);if(mode==='legendre')return `hsl(${n.arithmetic.legendreColour*137.508%360} 67% 60%)`;if(mode==='residue')return `hsl(${n.arithmetic.residues['210']*137.508%360} 67% 60%)`;if(mode==='minus'||mode==='plus')return `hsl(${210-180*Math.min(1,n.arithmetic[mode].knownLogFraction/.1)} 70% 62%)`;return `hsl(${n.community*137.508%360} 65% 60%)`}
function position(p){return [C.width/2+(p.sx-C.width/2)*zoom+pan[0],C.height/2+(p.sy-C.height/2)*zoom+pan[1]]}
function draw(){setupPoints();X.clearRect(0,0,C.width,C.height);X.strokeStyle='#263d54';for(let i=1;i<6;i++){X.beginPath();X.moveTo(50+(C.width-85)*i/6,40);X.lineTo(50+(C.width-85)*i/6,C.height-45);X.stroke();X.beginPath();X.moveTo(50,40+(C.height-85)*i/6);X.lineTo(C.width-35,40+(C.height-85)*i/6);X.stroke()}X.fillStyle='#a6b7c9';X.font='13px system-ui';X.fillText(fmt(extent.minx),50,C.height-15);X.fillText(fmt(extent.maxx),C.width-110,C.height-15);X.fillText(fmt(extent.miny),6,C.height-45);X.fillText(fmt(extent.maxy),6,35);
 let axes=$('view').value==='pairs'?'total log / N → · smaller-prime share ↑':$('view').value==='log'?'position within unit log box → · log p / N ↑':$('view').value==='pca'?'arithmetic principal projection 1 → · projection 2 ↑':'structural graph projection 1 → · projection 2 ↑';X.fillText(axes,65,20);
 if($('edges').checked&&$('view').value!=='pairs'){let byid=new Map(screen.map(p=>[p.item.id,p]));X.strokeStyle='#5b778742';for(let [i,j] of R.topology.edges){if(!byid.has(i)||!byid.has(j))continue;let a=position(byid.get(i)),b=position(byid.get(j));X.beginPath();X.moveTo(...a);X.lineTo(...b);X.stroke()}}
 let m=Math.max(1e-15,...screen.map(p=>Math.abs(p.pair?pairsAtHeight(p.item).re:p.item.charges[$('height').value].re)));
 for(let p of screen){let [x,y]=position(p);if(x<0||x>C.width||y<0||y>C.height)continue;X.fillStyle=colourFor(p,m);X.beginPath();X.arc(x,y,p.pair?2.3:4.5,0,2*Math.PI);X.fill();if(chosen!==null&&((!p.pair&&p.item.id===chosen)||p.pair&&(p.item.largest===chosen||p.item.smaller===chosen))){X.strokeStyle='#fff';X.lineWidth=1.8;X.stroke();X.lineWidth=1}}
 $('status').textContent=`${points.length.toLocaleString()} visible ${$('view').value==='pairs'?'literal pair incidences':'actual primes'} · height ${$('height').value} · source-normalised floor credit: 0`;
 const labels={phase:'Hue = arg(exp(−i y log p)); pair view uses the full product phase.',charge:'Coral = positive signed real charge; blue = negative. Pair charges are relative to each box; joined node charges spend half on each leg.',legendre:'Five-bit colour of Legendre symbols (2,3,5,7,11)/p. Pair view colours its largest leg.',residue:'Residue modulo 210. Pair view colours its largest leg.',minus:'Known small-factor log fraction of p−1 (only factors ≤257). Pair view colours its largest leg.',plus:'Known small-factor log fraction of p+1 (only factors ≤257). Pair view colours its largest leg.',community:'Community in phase/outcome-free structural projection. Pair view colours its largest leg.'};$('legend').textContent=labels[$('colour').value];$('role').disabled=$('view').value==='pairs';$('edges').disabled=$('view').value==='pairs';showStatistics()}
function factorText(f){return f.factors.map(([p,k])=>`${p}${k>1?'^'+k:''}`).join(' × ')+(f.unfactoredResidual!=='1'?' × [unfactored residual]':'')}
function showNode(n){chosen=n.id;let a=n.arithmetic,y=$('height').value,near=n.nearestPrimes;let profiles=['minus','plus'].map(sign=>`<div class="detailrow"><strong>p${sign==='minus'?'−':'+'}1:</strong> ${factorText(a[sign])}<br>Known log fraction ${fmt(a[sign].knownLogFraction)}. Residual: <span class="prime">${a[sign].unfactoredResidual}</span><br><small>Exact trial factors through 257; residual primality not asserted.</small></div>`).join('');$('detail').innerHTML=`<h2>Prime ${n.id}</h2><div class="prime">${n.prime}</div><div class="detailrow">Order ${n.N} · seed ${n.seed} · box ${n.box} · ${n.role}<br>log p = ${fmt(n.logPrime,9)}; box position ${fmt(n.logOffset)}<br>Parent primality: FLINT; Lean certificate: none.</div><div class="detailrow">Phase at y=${y}: ${complexText(n.phases[y])}<br>Half-incidence signed charge: ${complexText(n.charges[y])}<br>Estimated partial-population source charge: ${complexText(n.populationEstimatedCharges[y])}</div>${profiles}<div class="detailrow">Residues: ${JSON.stringify(a.residues)}<br>Legendre symbols: ${JSON.stringify(a.legendre)}<br>Structural community ${n.community}; component ${n.component}.</div><div class="detailrow">${near?`Proven consecutive-prime gaps: previous ${near.previous.gap}, next ${near.next.gap}. FLINT verified; no Lean certificate.`:'Consecutive-prime gaps not measured for this prime.'}<br>Accepted-sample gaps: ${n.sampledSpacing.lowerAcceptedSampleGap??'lower boundary'} / ${n.sampledSpacing.upperAcceptedSampleGap??'upper boundary'}<br><small>These accepted-sample gaps are not neighbouring-prime gaps.</small></div>`;draw()}
function showPair(p){let v=pairsAtHeight(p);chosen=p.largest;$('detail').innerHTML=`<h2>Literal pair incidence</h2><p>Order ${p.N} · seed ${p.seed} · box ${p.box}</p><div class="detailrow">T/N = ${fmt(p.T/p.N,9)}<br>Smaller share = ${fmt(p.smallerShare,9)}<br>Joined−Selberg coefficient / N = ${fmt(p.coefficientOverN,9)}<br>Actual allocation = ${fmt(p.allocation,9)}<br>Signed relative weight = ${fmt(p.relativeWeight,9)}<br>Full phase-weighted contribution = ${complexText(v)}<br>Complete-period / core mask retained at this height: ${p.retainedAtHeight[$('height').value]}</div><p>Inspect either actual leg:</p><button id="inspectLargest">Largest prime ${p.largest}</button> <button id="inspectSmaller">Smaller prime ${p.smaller}</button><div class="prime">${R.nodes[p.largest].prime}<br>×<br>${R.nodes[p.smaller].prime}</div><p class="muted">Full physical, factorial allocation and coefficient masks are inherited unchanged from the parent pair adapter. Population weights are estimates, not a whole-carrier certificate.</p>`;$('inspectLargest').onclick=()=>showNode(R.nodes[p.largest]);$('inspectSmaller').onclick=()=>showNode(R.nodes[p.smaller]);draw()}
function showStatistics(){let y=Number($('height').value),seed=$('seed').value,rows=R.statistics.records.filter(r=>r.height===y&&(seed==='all'||r.seed==seed)).sort((a,b)=>a.maxStatisticRank-b.maxStatisticRank||b.score-a.score).slice(0,12);$('associations').innerHTML='<tr><th>Arithmetic feature</th><th>Seed / target</th><th>|correlation|</th><th>Max-stat rank</th></tr>'+rows.map(r=>`<tr><td>${r.feature}</td><td>${r.seed} / ${r.target}</td><td>${fmt(r.score,3)}</td><td>${fmt(r.maxStatisticRank,3)}</td></tr>`).join('');let candidates=R.statistics.sameHeightSeedReplication;$('candidateSummary').textContent=candidates.length?`${candidates.length} same-height seed-replicated flags; ${R.statistics.discoveryAndHeldOutReplication.length} also meet the discovery/held-out rule. These remain exploratory.`:'No feature or interaction passes the same-height, same-orientation, both-seed replication rule after feature-search adjustment.';$('graphAgreement').innerHTML='<h3>Residual field on this graph</h3>'+R.statistics.graphAgreement.filter(r=>r.height===y&&(seed==='all'||r.seed==seed)).map(r=>`<p>Seed ${r.seed} ${r.target}: agreement ${fmt(r.residualGraphAgreement,3)}; diagnostic shuffle rank ${fmt(r.twoSidedPermutationRank,3)}.</p>`).join('')}
function nearest(event){let r=C.getBoundingClientRect(),x=(event.clientX-r.left)*C.width/r.width,y=(event.clientY-r.top)*C.height/r.height,best=null,d=16;for(let p of screen){let pos=position(p),dist=Math.hypot(x-pos[0],y-pos[1]);if(dist<d){d=dist;best=p}}return best}
C.onpointerdown=e=>{drag=[e.clientX,e.clientY,...pan];moved=false;C.setPointerCapture(e.pointerId)};C.onpointermove=e=>{if(drag){let r=C.getBoundingClientRect();pan=[drag[2]+(e.clientX-drag[0])*C.width/r.width,drag[3]+(e.clientY-drag[1])*C.height/r.height];moved ||= Math.hypot(e.clientX-drag[0],e.clientY-drag[1])>4;draw();return}let p=nearest(e);$('hover').textContent=p?(p.pair?`Pair ${p.item.largest} × ${p.item.smaller}; T/N ${fmt(p.item.T/p.item.N)}, share ${fmt(p.item.smallerShare)}, signed coefficient/N ${fmt(p.item.coefficientOverN)}`:`Prime ${p.item.id}; seed ${p.item.seed}, ${p.item.role}, log p ${fmt(p.item.logPrime)}, phase ${complexText(p.item.phases[$('height').value])}, charge ${complexText(p.item.charges[$('height').value])}`):'Hover for a prime or pair; click to inspect it. Wheel to zoom, drag to pan.'};C.onpointerup=e=>{drag=null;if(!moved){let p=nearest(e);if(p)p.pair?showPair(p.item):showNode(p.item)}};C.onpointercancel=()=>{drag=null};C.onwheel=e=>{e.preventDefault();let r=C.getBoundingClientRect(),v=[(e.clientX-r.left)*C.width/r.width-C.width/2,(e.clientY-r.top)*C.height/r.height-C.height/2],next=Math.max(.5,Math.min(20,zoom*Math.exp(-e.deltaY*.0015))),ratio=next/zoom;pan=pan.map((p,i)=>v[i]-(v[i]-p)*ratio);zoom=next;draw()};
for(let y of R.heights)$('height').add(new Option(y,y));for(let s of R.seeds)$('seed').add(new Option(s,s));for(let id of ['view','seed','role'])$(id).onchange=()=>{zoom=1;pan=[0,0];draw()};for(let id of ['height','colour','edges'])$(id).onchange=()=>{draw();if(chosen!==null&&$('view').value!=='pairs')showNode(R.nodes[chosen])};$('fit').onclick=()=>{zoom=1;pan=[0,0];draw()};$('clear').onclick=()=>{chosen=null;$('detail').innerHTML='<h2>Inspect the arithmetic</h2><p>Select a prime or pair on the map.</p>';draw()};
$('primeCount').textContent=R.nodes.length.toLocaleString();$('pairCount').textContent=R.pairs.length.toLocaleString();$('featureCount').textContent=R.features.length;$('repCount').textContent=R.statistics.discoveryAndHeldOutReplication.length;
$('filtration').innerHTML='<tr><th>Distance ≤</th><th>Components</th><th>Edges</th><th>Cycle rank</th></tr>'+R.topology.graphFiltration.map(r=>`<tr><td>${fmt(r.edgeDistanceThreshold,3)}</td><td>${r.components}</td><td>${r.edges}</td><td>${r.graphCycleRank}</td></tr>`).join('');$('provenance').textContent=JSON.stringify({scope:R.scope,sourcePins:R.sources,neighbourAnchors:R.neighbourAnchors,discoveryControls:R.statistics.controls},null,2);draw();
</script></html>'''
    path.write_text(template.replace('PAYLOAD', payload))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=Path('.lake/riesz-pair-structure/scan.json'))
    parser.add_argument('--output', type=Path, default=Path('.lake/riesz-prime-atlas/atlas.json'))
    parser.add_argument('--neighbours', type=int, default=10)
    parser.add_argument('--neighbour-budget', type=int, default=32)
    parser.add_argument('--permutations', type=int, default=127)
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    tests = regressions()
    if args.self_test:
        print(json.dumps(tests, indent=2))
        return
    if args.neighbours < 2 or args.neighbour_budget < 0 or args.permutations < 31:
        parser.error('Require >=2 structural neighbours, nonnegative anchor budget and >=31 permutations')
    parent = json.loads(args.input.read_text())
    for source in parent['sources']:
        if digest(source['path'])['sha256'] != source['sha256']:
            raise ValueError(f"Parent source pin changed: {source['path']}; rerun or explicitly audit adapter")
    sample_pin = parent['sampleFile']
    if digest(sample_pin['path'])['sha256'] != sample_pin['sha256']:
        raise ValueError('Sample cache hash changed')
    samples = json.loads(Path(sample_pin['path']).read_text())
    ctx.prec = max(1200, int(2*max(samples['orders'])/math.log(2))+256)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    heights = [int(y) if float(y).is_integer() else y
               for y in sorted({r['height'] for r in parent['sampled']})]
    nodes, index = build_nodes(samples, heights)
    group_count = len({(n['N'], n['seed'], n['box'], n['role']) for n in nodes})
    if args.neighbour_budget > group_count:
        parser.error(f'Current deterministic anchor rule permits at most {group_count} neighbours')
    cache_path = args.output.with_suffix('.neighbours.json')
    neighbour_anchors(nodes, args.neighbour_budget, cache_path)
    _, scaled, graph, features = feature_table(nodes)
    topology, W = structural_topology(graph, nodes, args.neighbours)
    pairs, cases = carrier_incidence(nodes, index, samples, heights, parent)
    statistics = association_scan(nodes, scaled, features, W, heights, args.permutations)
    if cache_path.exists():
        neighbour_source = [digest(cache_path)]
    else:
        neighbour_source = []
    report = dict(schemaVersion=1, classification='Optional actual-prime arithmetic/phase atlas; no floor credit',
        orders=samples['orders'], seeds=samples['seeds'], heights=heights,
        nodes=nodes, pairs=pairs, literalCaseReplays=cases, features=features,
        topology=topology, statistics=statistics, communityLedger=community_ledger(nodes, heights),
        neighbourAnchors=sum(n['nearestPrimes'] is not None for n in nodes), regressions=tests,
        sources=[digest(Path(__file__).relative_to(Path.cwd())), digest(args.input),
                 digest(sample_pin['path'])]+parent['sources']+neighbour_source,
        scope=dict(actualPrimes=True, sampleBoxesNotFullPopulation=True,
            originalCoefficientAllocationPhysicalAndPeriodMasksRetained=True,
            allSelectedSmallerPrimesAbovePolynomialPaidRange=True,
            primalityMethod='FLINT, inherited and replayed; no Lean certificates',
            factorisationOfPMinusPlusOne='Partial trial division through 257; residual not declared prime',
            structuralGraphExcludesPhaseOutcomeSizeSeedAndRole=True,
            phaseColourIsNotRepositoryPrimePowerColour=True,
            pairIncidencesNotIndependentSamples=True,
            populationScaledChargesAreEstimatedPartialPopulationOnly=True,
            phaseDeterministicGivenLog=True, statisticsAreExploratory=True,
            cofinalFloorCredit=0, buildAndOrdinaryCIIntegration=False))
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
    render(report, args.output.with_suffix('.html'))
    print(json.dumps(dict(event='atlasComplete', primes=len(nodes), pairs=len(pairs),
        features=len(features), interactions=statistics['interactions'],
        seedReplications=len(statistics['sameHeightSeedReplication']),
        heldOutReplications=len(statistics['discoveryAndHeldOutReplication']),
        neighbourAnchors=report['neighbourAnchors'], output=str(args.output)), indent=2), flush=True)


if __name__ == '__main__':
    main()
