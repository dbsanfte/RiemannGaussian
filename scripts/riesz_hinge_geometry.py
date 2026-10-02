"""Exact finite-input geometry of signed subset hinges.

Optional detector backend, not a prime-density or source-budget theorem.
The cutoff prefix keeps signed incidence moments of degrees zero, one,
and two. Complete free cubes annihilate signed monomials of degree below
their dimension. Unsigned knot distances are computed separately: a
canceled signed coefficient does not delete a physical boundary.

Every unfinished calculation returns null main values. No partial tensor,
guessed rank, or guessed transport radius is exported as a result.
"""

from dataclasses import dataclass
from fractions import Fraction
import math
import random

import sympy as sp


class GeometryBudgetExhausted(Exception):
    pass


@dataclass(frozen=True)
class Incidence:
    zeroth: int
    first: dict
    second: dict
    unsigned_count: int


def _clean(values):
    return {key: value for key, value in values.items() if value}


def _subtract(left, right):
    result = dict(left)
    for key, value in right.items():
        result[key] = result.get(key, 0)-value
    return _clean(result)


def _difference(left, right):
    return Incidence(left.zeroth-right.zeroth,
                     _subtract(left.first, right.first),
                     _subtract(left.second, right.second),
                     left.unsigned_count-right.unsigned_count)


def _insert_difference(left, right, index):
    """Missing/included branches, with the actual included parity sign."""
    first = _subtract(left.first, right.first)
    first[index] = first.get(index, 0)-right.zeroth
    second = _subtract(left.second, right.second)
    second[index, index] = second.get((index, index), 0)-right.zeroth
    for leg, value in right.first.items():
        key = tuple(sorted((index, leg)))
        second[key] = second.get(key, 0)-value
    return Incidence(left.zeroth-right.zeroth, _clean(first), _clean(second),
                     left.unsigned_count+right.unsigned_count)


def _reflected_complement(moment, indices):
    """Exact Boolean complement, retaining signed degree-two moments.

    On a free cube of dimension >2 the full signed tensor is zero.
    A strict upper prefix is minus (-1)^m times the inclusive reflected
    lower prefix, and vice versa. Unsigned counts complement separately.
    """
    sign = -(-1)**len(indices)
    first = {i: sign*(moment.zeroth-moment.first.get(i,0)) for i in indices}
    second = {}
    for k,i in enumerate(indices):
        second[i,i] = first[i]
        for j in indices[k+1:]:
            pair = tuple(sorted((i,j)))
            value = sign*(moment.zeroth-moment.first.get(i,0)-
                          moment.first.get(j,0)+moment.second.get(pair,0))
            if value:
                second[pair] = value
    return Incidence(sign*moment.zeroth,_clean(first),_clean(second),
                     2**len(indices)-moment.unsigned_count)


class HingeGeometry:
    def __init__(self, logs, state_budget=32768, moment_budget=1000000):
        self.logs = list(map(Fraction, logs))
        if not self.logs or any(x <= 0 for x in self.logs):
            raise ValueError('strictly positive exact finite-input logs required')
        if state_budget < 0 or moment_budget < 0:
            raise ValueError('nonnegative work budgets required')
        denominator = math.lcm(*(x.denominator for x in self.logs))
        integers = [x.numerator*(denominator//x.denominator) for x in self.logs]
        divisor = math.gcd(*integers)
        self.unit = Fraction(divisor, denominator)
        self.integers = [x//divisor for x in integers]
        self.indices = sorted(range(len(logs)), key=self.integers.__getitem__)
        self.xs = [self.integers[i] for i in self.indices]
        self.prefix = [0]
        for x in self.xs:
            self.prefix.append(self.prefix[-1]+x)
        self.state_budget, self.moment_budget = state_budget, moment_budget

    def prefix_moments(self, cutoff, inclusive=False):
        """All subsets below the EXACT cutoff; equality is explicit."""
        D = Fraction(cutoff)/self.unit
        denominator = D.denominator
        visited = free_cubes = annihilated = inactive = stored = reflected = 0

        try:
            # Explicit postorder stack: growing counts do not depend on
            # the interpreter's recursion limit or drop deep branches.
            root = (len(self.logs),D.numerator,inclusive)
            cache = {}
            stack = [(root,False)]
            while stack:
                key,ready = stack.pop()
                if key in cache:
                    continue
                m,numerator,equality = key
                reflect = m>2 and 2*numerator>self.prefix[m]*denominator
                deps = ([(m,self.prefix[m]*denominator-numerator,not equality)]
                        if reflect else [(m-1,numerator,equality),
                                         (m-1,numerator-self.xs[m-1]*denominator,equality)]) if m else []
                answer = None
                if not ready:
                    visited += 1
                    if visited>self.state_budget:
                        raise GeometryBudgetExhausted('state budget')
                    if numerator<0 or (numerator==0 and not equality):
                        inactive += 1
                        answer = Incidence(0,{}, {},0)
                    elif numerator>self.prefix[m]*denominator or (
                            equality and numerator==self.prefix[m]*denominator):
                        free_cubes += 1
                        if m>2:
                            annihilated += 1
                            answer = Incidence(0,{}, {},2**m)
                        elif m==2:
                            answer = Incidence(0,{}, {tuple(sorted(self.indices[:2])):1},4)
                        elif m==1:
                            i=self.indices[0]
                            answer=Incidence(0,{i:-1},{(i,i):-1},2)
                        else:
                            answer=Incidence(1,{}, {},1)
                    elif m==0:
                        answer=Incidence(1,{}, {},1)
                    else:
                        if reflect:
                            reflected += 1
                        stack.append((key,True))
                        stack.extend((child,False) for child in reversed(deps) if child not in cache)
                        continue
                elif reflect:
                    answer=_reflected_complement(cache[deps[0]],self.indices[:m])
                else:
                    answer=_insert_difference(cache[deps[0]],cache[deps[1]],self.indices[m-1])
                stored += len(answer.first)+len(answer.second)+1
                if stored>self.moment_budget:
                    raise GeometryBudgetExhausted('stored moment budget')
                cache[key]=answer
            answer=cache[root]
            exhaustion = None
        except GeometryBudgetExhausted as exc:
            answer = None
            exhaustion = str(exc)
        return answer, dict(complete=answer is not None, visitedExactStates=visited,
                            completeFreeCubes=free_cubes,
                            degreeTwoAnnihilatedCubes=annihilated,
                            exactComplementReflections=reflected,
                            inactiveSubtrees=inactive, storedMomentEntries=stored,
                            stateBudget=self.state_budget, momentBudget=self.moment_budget,
                            exhaustedResource=exhaustion,
                            inclusiveBoundary=inclusive, skippedUncertainSubtrees=False)

    def boundary_gap(self, cutoff):
        """Nearest UNSIGNED subset knot on both sides, including equality."""
        D = Fraction(cutoff)/self.unit
        visited = 0

        cache={}
        def largest(m, numerator, denominator):
            nonlocal visited
            root=(m,numerator,denominator)
            stack=[(root,False)]
            while stack:
                key,ready=stack.pop()
                if key in cache:
                    continue
                m,numerator,denominator=key
                deps=[(m-1,numerator,denominator),
                      (m-1,numerator-self.xs[m-1]*denominator,denominator)] if m else []
                if not ready:
                    visited += 1
                    if visited>self.state_budget:
                        raise GeometryBudgetExhausted('unsigned knot state budget')
                    if numerator<0:
                        cache[key]=None
                    elif numerator>=self.prefix[m]*denominator:
                        cache[key]=self.prefix[m]
                    elif m==0:
                        cache[key]=0
                    else:
                        stack.append((key,True))
                        stack.extend((child,False) for child in reversed(deps) if child not in cache)
                else:
                    a,b=cache[deps[0]],cache[deps[1]]
                    cache[key]=max(a if a is not None else -1,
                                   b+self.xs[m-1] if b is not None else -1)
            return cache[root]

        try:
            lo = largest(len(self.logs), D.numerator, D.denominator)
            reflected = Fraction(self.prefix[-1])-D
            hi_ref = largest(len(self.logs), reflected.numerator, reflected.denominator)
            hi = self.prefix[-1]-hi_ref if hi_ref is not None else None
            distances = ([D-lo] if lo is not None else [])+([hi-D] if hi is not None else [])
            gap = min(distances)*self.unit
        except GeometryBudgetExhausted:
            lo = hi = gap = None
        return dict(complete=gap is not None, exactUnsignedGap=str(gap) if gap is not None else None,
                    unsignedBoundaryAtCutoff=gap == 0 if gap is not None else None,
                    visitedExactStates=visited, stateBudget=self.state_budget,
                    canceledSignedKnotsStillPresent=True)

    @staticmethod
    def _export(moment, count):
        return dict(signedCount=str(moment.zeroth), unsignedCount=str(moment.unsigned_count),
                    first=[str(moment.first.get(i, 0)) for i in range(count)],
                    second=[dict(legs=[i,j],value=str(v)) for (i,j),v in sorted(moment.second.items())],
                    secondIsSignedIncidenceNotHingeHessian=True)

    def two_hinge(self, left, right):
        results = [self.prefix_moments(cut, equality)
                   for cut in (left, right) for equality in (False, True)]
        audits = [audit for _,audit in results]
        if any(moment is None for moment,_ in results):
            return dict(complete=False, momentAudits=audits, coefficient=None,
                        gradient=None, interactionRank=None, candidateDirections=None,
                        unfinishedCalculationNotRanked=True)
        lm, li, rm, ri = [moment for moment,_ in results]
        joined = _difference(lm, rm)
        gradient = [-joined.first.get(i, 0) for i in range(len(self.logs))]
        coefficient = Fraction(left)*lm.zeroth-Fraction(right)*rm.zeroth+sum(
            (x*g for x,g in zip(self.logs,gradient)), Fraction(0))
        boundary = [self.boundary_gap(cut) for cut in (left, right)]
        groups = {}
        for i,g in enumerate(gradient):
            groups.setdefault(g, []).append(i)
        # Only nonzero correlation rows enter exact rational algebra.
        active = sorted({i for key in joined.second for i in key})
        matrix = sp.zeros(len(active))
        positions = {i:k for k,i in enumerate(active)}
        for (i,j),v in joined.second.items():
            matrix[positions[i],positions[j]] = v
            matrix[positions[j],positions[i]] = v
        # Repeated rows carry one actual constraint, not many independent
        # directions. Deduplicate them exactly before rational elimination.
        unique_rows = list(dict.fromkeys(tuple(matrix.row(i)) for i in range(matrix.rows)))
        rank = sp.Matrix(unique_rows).rank() if unique_rows else 0
        # These are candidate low-moment directions, not a prime transport
        # or invariant neighborhood. Actual flat directions depend on the
        # unsigned knot gap, fixed cutoffs and separately retained weights.
        constraint_rows = list(dict.fromkeys(unique_rows+[
            tuple(gradient[i] for i in active),tuple(1 for _ in active)])) if active else []
        constraints = sp.Matrix(constraint_rows) if constraint_rows else sp.zeros(0,0)
        nulls = constraints.nullspace() if active else []
        directions = [dict(legs=active, weights=list(map(str,v))) for v in nulls[:8]]
        gap_complete = all(x['complete'] for x in boundary)
        gap = min(Fraction(x['exactUnsignedGap']) for x in boundary) if gap_complete else None
        return dict(complete=True, coefficient=str(coefficient),
                    gradient=list(map(str,gradient)), momentAudits=audits,
                    prefix=[self._export(m,len(self.logs)) for m in (lm,rm)],
                    hingeWall=[self._export(_difference(li,lm),len(self.logs)),
                               self._export(_difference(ri,rm),len(self.logs))],
                    unsignedBoundaries=boundary, exactUnsignedTwoHingeGap=str(gap) if gap is not None else None,
                    unsignedBoundaryCalculationComplete=gap_complete,
                    localRadiusCertifiedForFiniteInput=gap_complete and gap>0,
                    affineNeighborhoodRequiresFixedCutoffsAndL1DisplacementBelowGap=True,
                    fixedTotalGradientGroups=[dict(gradient=str(g),legs=legs) for g,legs in groups.items()],
                    pairRedistributionDirections=sum(len(legs)*(len(legs)-1)//2 for legs in groups.values()),
                    activeCorrelationLegs=active, interactionRank=rank,
                    signedDegreeTwoNullity=len(self.logs)-rank,
                    candidateDirections=directions,
                    correlationNullDirectionsNotAutomaticallyTransport=True,
                    phaseAllocationOrPrimeInventorySaving=False)


def _enumerate(logs, cutoff, inclusive):
    values = [(Fraction(0), ())]
    for i,x in enumerate(logs):
        values += [(s+x,indices+(i,)) for s,indices in values[:]]
    zeroth = count = 0
    first, second = {}, {}
    for s, indices in values:
        if not (s <= cutoff if inclusive else s < cutoff):
            continue
        sign = (-1)**len(indices)
        zeroth += sign; count += 1
        for i in indices:
            first[i] = first.get(i,0)+sign
            for j in indices:
                if j >= i:
                    second[i,j] = second.get((i,j),0)+sign
    return Incidence(zeroth,_clean(first),_clean(second),count), values


def self_test():
    """Independent exact enumeration, including canceled unsigned walls."""
    rng = random.Random(88291)
    tests = gaps = 0
    for count in range(1,11):
        for sample in range(4):
            logs = [Fraction(rng.randrange(1,32),8) for _ in range(count)]
            profile = HingeGeometry(logs)
            total = sum(logs)
            cuts = [Fraction(0),total,total+1,total*Fraction(7,16),logs[0]]
            for cut in cuts:
                for inclusive in (False,True):
                    truth,_ = _enumerate(logs,cut,inclusive)
                    result,audit = profile.prefix_moments(cut,inclusive)
                    assert audit['complete'] and result == truth
                    tests += 1
                _,knots = _enumerate(logs,cut,False)
                expected = min(abs(s-cut) for s,_ in knots)
                gap = profile.boundary_gap(cut)
                assert gap['complete'] and Fraction(gap['exactUnsignedGap']) == expected
                gaps += 1
            result = profile.two_hinge(total*Fraction(7,16),total*Fraction(11,16))
            truth = sum((-1)**len(indices)*(max(Fraction(0),total*Fraction(7,16)-s)-
                            max(Fraction(0),total*Fraction(11,16)-s)) for s,indices in knots)
            assert result['complete'] and Fraction(result['coefficient']) == truth
    canceled = HingeGeometry(list(map(Fraction,[1,2,3,7,11,15])))
    lower,_ = canceled.prefix_moments(Fraction(3),False)
    upper,_ = canceled.prefix_moments(Fraction(3),True)
    assert upper.zeroth-lower.zeroth == 0 and upper.unsigned_count-lower.unsigned_count == 2
    assert canceled.boundary_gap(3)['unsignedBoundaryAtCutoff']
    unfinished = HingeGeometry([Fraction(i) for i in range(1,80)],state_budget=1).two_hinge(150,251)
    assert not unfinished['complete'] and unfinished['coefficient'] is None and unfinished['interactionRank'] is None
    small_storage = HingeGeometry([Fraction(i) for i in range(1,12)],moment_budget=0).two_hinge(15,27)
    assert not small_storage['complete'] and small_storage['candidateDirections'] is None
    hierarchy = HingeGeometry([Fraction(2**i) for i in range(300)])
    result = hierarchy.two_hinge(Fraction(2**295+13,4),Fraction(2**298+37,8))
    assert result['complete']
    # A growing almost-complete cube must not hit Python's call-stack
    # limit. Its only excluded subset is the full 512-coordinate vertex.
    deep=HingeGeometry([Fraction(2**i) for i in range(512)])
    high,audit=deep.prefix_moments(sum(deep.logs)-Fraction(1,2))
    assert audit['complete'] and high.unsigned_count==2**512-1 and high.zeroth==-1
    assert len(high.first)==512 and all(v==-1 for v in high.first.values())
    assert len(high.second)==512*513//2 and all(v==-1 for v in high.second.values())
    return dict(passed=True,independentSignedTensorEnumerations=tests,
                independentUnsignedBoundaryComparisons=gaps,
                completeTwoHingeEnumerations=40,
                canceledSignedWallRetainsUnsignedBoundary=True,
                stateAndStorageExhaustionNeverProducesRank=True,
                complete300LegSubsetCoverage=str(2**300),
                complete512LegComplementRegression=True,
                highDimensionalRecursionStates=sum(x['visitedExactStates'] for x in result['momentAudits']))


if __name__ == '__main__':
    import json
    print(json.dumps(self_test(),indent=2))
