"""Exact finite-input enclosures for arbitrary signed subset hinges.

This backend never changes a logarithm to its rounded grid value.  The grid
only partitions subsets.  Every state retains exact integer multiplicity,
first/second moments, extrema, and true subset parity.  Its enclosure is for
the supplied finite binary numbers, not for unverified real logarithms.
No prime-density, phase-transport, or source-scale assertion is made here.
"""

from dataclasses import dataclass
from fractions import Fraction
import math
from functools import lru_cache

import mpmath as mp


def binary_fraction(value):
    value = mp.mpf(value)
    sign, mantissa, exponent, _ = value._mpf_
    mantissa,exponent = int(mantissa),int(exponent)
    mantissa = -mantissa if sign else mantissa
    return Fraction(mantissa << exponent) if exponent >= 0 else Fraction(mantissa, 1 << -exponent)


@dataclass(slots=True)
class Moments:
    count: int
    first: int
    second: int
    minimum: int
    maximum: int

    def insert(self, x):
        return Moments(self.count, self.first + x*self.count,
                       self.second + 2*x*self.first + x*x*self.count,
                       self.minimum+x, self.maximum+x)

    def merge(self, other):
        self.count += other.count
        self.first += other.first
        self.second += other.second
        self.minimum = min(self.minimum, other.minimum)
        self.maximum = max(self.maximum, other.maximum)


def ceil_sqrt(n):
    r = math.isqrt(n)
    return r + (r*r != n)


class SubsetMoments:
    """A complete (rounded-sum, actual parity) subset partition."""

    def __init__(self, logs, grid=4096,recursion_budget=32768):
        logs = [mp.mpf(x) for x in logs]
        if not logs or any(not mp.isfinite(x) or x <= 0 for x in logs):
            raise ValueError('finite strictly positive inputs are required')
        if not isinstance(grid, int) or grid < 1:
            raise ValueError('grid must be a positive integer')
        if not isinstance(recursion_budget,int) or recursion_budget < 0:
            raise ValueError('recursion budget must be a nonnegative integer')
        self.recursion_budget = recursion_budget
        self.exponent = min(x._mpf_[2] for x in logs)
        integers = [(int(x._mpf_[1]) << (x._mpf_[2]-self.exponent)) for x in logs]
        self.unit = Fraction(1 << self.exponent) if self.exponent >= 0 else Fraction(1, 1 << -self.exponent)
        divisor = math.gcd(*integers)
        integers = [x//divisor for x in integers]
        self.unit *= divisor
        self.integers, self.count, self.grid = integers, len(integers), grid
        total = sum(integers)
        # Detect a tractable exact lattice without requiring the caller to
        # name one. Otherwise retain the same complete moment enclosure.
        self.exact_lattice = total <= grid
        self.rounded = integers if self.exact_lattice else [(2*x*grid+total)//(2*total) for x in integers]
        self.sparse_lattice = False
        self.exceptional_legs = 0
        regular = list(range(self.count))
        exceptions = []
        basis = 1
        if not self.exact_lattice and self.count >= 6:
            # Discover a common exact lattice in MOST inputs; no caller
            # marks the exceptional legs. Keep every exceptional subset
            # as its own exact shift, never rounding it to the lattice.
            candidates = {math.gcd(x,y) for i,x in enumerate(integers) for y in integers[i+1:]}
            options = []
            for d in candidates:
                bad = [i for i,x in enumerate(integers) if x % d]
                if not bad or len(bad)>min(4,self.count//5):
                    continue
                good = [i for i,x in enumerate(integers) if x % d == 0]
                degree = sum(integers[i]//d for i in good)
                if degree <= grid:
                    options.append((len(bad),degree,d,good,bad))
            if options:
                _,_,basis,regular,exceptions = min(options,key=lambda z:z[:2])
                self.sparse_lattice = True
                self.exceptional_legs = len(exceptions)
        states = {(0, 0): Moments(1, 0, 0, 0, 0)}
        for i in regular:
            x = integers[i]
            g = x//basis if self.sparse_lattice else self.rounded[i]
            updated = {key: Moments(z.count,z.first,z.second,z.minimum,z.maximum)
                       for key,z in states.items()}
            for (position,parity),z in states.items():
                key = (position+g,1-parity)
                v = z.insert(x)
                if key in updated:
                    updated[key].merge(v)
                else:
                    updated[key] = v
            states = updated
        if self.sparse_lattice:
            states = {(position*basis,p):z for (position,p),z in states.items()}
            for i in exceptions:
                x = integers[i]
                updated = {key:Moments(z.count,z.first,z.second,z.minimum,z.maximum)
                           for key,z in states.items()}
                for (position,p),z in states.items():
                    key = (position+x,1-p)
                    v = z.insert(x)
                    if key in updated:
                        updated[key].merge(v)
                    else:
                        updated[key] = v
                states = updated
        self.states = states
        assert sum(z.count for z in states.values()) == 2**self.count
        for z in states.values():
            assert z.count*z.second >= z.first*z.first
            assert z.count*z.minimum <= z.first <= z.count*z.maximum
        if self.count >= 2:
            assert sum((-1)**p*z.count for (_,p),z in states.items()) == 0
            assert sum((-1)**p*z.first for (_,p),z in states.items()) == 0

    @staticmethod
    def hinge_bounds(z, D):
        """Exact first-moment lower and Cauchy/chord upper bounds.

        If A=C*D-M, then sum(D-x)+ <= (A+sqrt(A²+C*S-M²))/2.
        An INTEGER square-root enclosure makes this bound rational.
        Extrema first collapse every completely affine/inactive state.
        """
        if D <= z.minimum:
            return Fraction(0),Fraction(0)
        if z.maximum <= D:
            answer = z.count*D-z.first
            return answer,answer
        d,q = D.numerator,D.denominator
        A = z.count*d-z.first*q
        variance = z.count*z.second-z.first*z.first
        lower = Fraction(max(A,0),q)
        upper_moment = Fraction(A+ceil_sqrt(A*A+variance*q*q),2*q)
        upper_chord = Fraction((z.maximum*z.count-z.first)*(d-z.minimum*q),
                               (z.maximum-z.minimum)*q)
        upper = min(upper_moment,upper_chord)
        assert lower <= upper
        return lower,upper

    def hinges(self, terms):
        """Keep a complete finite combination joined in each parity state.

        terms = [(coefficient, cutoff), ...]. The signs of the response and
        subset parity are preserved. No uncertain state is skipped.
        """
        terms = [(Fraction(c),binary_fraction(D)/self.unit) for c,D in terms]
        lower = upper = Fraction(0)
        crossing_states = crossing_subsets = 0
        crossing_variance = 0
        guard_scale = 1 << 32
        for (_,parity),z in self.states.items():
            lo = hi = Fraction(0)
            crossing = False
            for coefficient,D in terms:
                a,b = self.hinge_bounds(z,D)
                crossing |= a != b
                if coefficient >= 0:
                    lo += coefficient*a; hi += coefficient*b
                else:
                    lo += coefficient*b; hi += coefficient*a
            if parity:
                lo,hi = -hi,-lo
            if crossing:
                # Exact OUTWARD rational rounding prevents denominator
                # explosion when different chord endpoints are selected.
                # It cannot discard an unresolved state or shrink a bound.
                lo = Fraction((lo.numerator*guard_scale)//lo.denominator,guard_scale)
                hi = Fraction(-((-hi.numerator*guard_scale)//hi.denominator),guard_scale)
            lower += lo; upper += hi
            if crossing:
                crossing_states += 1
                crossing_subsets += z.count
                crossing_variance += z.count*z.second-z.first*z.first
        recurrence = dict(attempted=False,allTermsResolved=False)
        if lower != upper and self.recursion_budget:
            exact_terms = []
            term_audits = []
            for coefficient,D in terms:
                value,audit = self.recursive_response(D)
                term_audits.append(audit)
                if value is not None:
                    exact_terms.append(coefficient*value)
            recurrence = dict(attempted=True,allTermsResolved=len(exact_terms)==len(terms),
                              termAudits=term_audits)
            if recurrence['allTermsResolved']:
                value = sum(exact_terms,Fraction(0))
                assert lower <= value <= upper
                lower = upper = value
        lower *= self.unit; upper *= self.unit
        return dict(lower=lower,upper=upper,exact=lower if lower == upper else None,
                    states=len(self.states),representedSubsets=2**self.count,
                    crossingStates=crossing_states,crossingSubsets=crossing_subsets,
                    exactFiniteInputEnclosure=True,
                    signedRecurrenceAudit=recurrence,
                    aggregateCrossingVariance=Fraction(crossing_variance)*self.unit**2)

    def recursive_response(self,D):
        """Exact finite differences with complete affine subtree cancellation.

        F_m(D)=F_(m-1)(D)-F_(m-1)(D-x_m). Every prefix of at least
        two legs has zero signed affine response beyond its total length.
        Discover/prune these regions without assigning an input family.
        Hitting the budget returns NO guessed response, so the complete
        moment enclosure remains authoritative. D is in integer units.
        """
        xs = sorted(self.integers)
        prefix = [0]
        for x in xs:
            prefix.append(prefix[-1]+x)
        denominator = D.denominator
        visited = inactive = affine = 0
        class BudgetExhausted(Exception):
            pass
        @lru_cache(maxsize=None)
        def F(m,numerator):
            nonlocal visited,inactive,affine
            visited += 1
            if visited > self.recursion_budget:
                raise BudgetExhausted
            if numerator <= 0:
                inactive += 1
                return Fraction(0)
            if m == 0:
                return Fraction(numerator,denominator)
            if numerator >= prefix[m]*denominator:
                if m >= 2:
                    affine += 1
                    return Fraction(0)
                return Fraction(xs[0])
            return F(m-1,numerator)-F(m-1,numerator-xs[m-1]*denominator)
        try:
            answer = F(self.count,D.numerator)
            complete = True
        except BudgetExhausted:
            answer = None
            complete = False
        return answer,dict(complete=complete,visitedExactStates=visited,
                           inactiveSubtrees=inactive,zeroAffineSubtrees=affine,
                           stateBudget=self.recursion_budget,
                           skippedUncertainSubtrees=False)

    def response(self, cutoff):
        return self.hinges([(1,cutoff)])

    def two_hinge(self, left, right):
        return self.hinges([(1,left),(-1,right)])

    def parity_features(self):
        """Unlabelled subset-bin structure, without knowing a geometry family."""
        positions = sorted({i for i,_ in self.states})
        matched = unsigned = 0
        imbalance = 0
        mean_gap_lower = mean_gap_upper = 0
        guard_scale = 1 << 40
        for position in positions:
            e,o = self.states.get((position,0)),self.states.get((position,1))
            ce,co = (e.count if e else 0),(o.count if o else 0)
            matched += 2*min(ce,co); unsigned += ce+co
            imbalance += abs(ce-co)
            if ce and co:
                gap = min(ce,co)*abs(Fraction(e.first,ce)-Fraction(o.first,co))
                mean_gap_lower += (gap.numerator*guard_scale)//gap.denominator
                mean_gap_upper += -((-gap.numerator*guard_scale)//gap.denominator)
        return dict(parityOverlap=Fraction(matched,unsigned),
                    localParityImbalance=imbalance/unsigned,
                    matchedCentroidGapLower=Fraction(mean_gap_lower,guard_scale)*self.unit/unsigned,
                    matchedCentroidGapUpper=Fraction(mean_gap_upper,guard_scale)*self.unit/unsigned,
                    zeroRoundedLegs=sum(x == 0 for x in self.rounded),
                    stateCount=len(self.states),grid=self.grid,
                    exactLatticeDetected=self.exact_lattice,
                    sparseExactLatticeDetected=self.sparse_lattice,
                    independentlyDetectedExceptionalLegs=self.exceptional_legs,
                    representedSubsets=2**self.count)

    def coordinate_sensitivity(self,left,right):
        """Exact local response gradients on a tractable detected lattice.

        Divide the SIGNED subset polynomial by each (1-z^x_i). Keeping
        every coefficient gives the derivative with respect to leg i.
        Equal gradients identify an automatically discovered redistribution
        invariant until a subset reaches either hinge. This is not prime
        matching, nor a statement about allocation-weight derivatives.
        """
        if not self.exact_lattice:
            return dict(available=False,reason='no tractable exact full lattice; no derivative is guessed')
        degree = sum(self.integers)
        P = [0]*(degree+1)
        for (position,parity),z in self.states.items():
            assert z.minimum == z.maximum == position
            P[position] += (-1)**parity*z.count
        D,E = binary_fraction(left)/self.unit,binary_fraction(right)/self.unit
        prefix = lambda coefficients,X: sum(coefficients[:max(0,min(len(coefficients),
            (X.numerator-1)//X.denominator+1))])
        gradients = []
        for x in self.integers:
            Q = [0]*(degree-x+1)
            for n in range(len(Q)):
                Q[n] = P[n]+(Q[n-x] if n>=x else 0)
            for n in range(degree+1):
                assert P[n] == (Q[n] if n<len(Q) else 0)-(Q[n-x] if 0<=n-x<len(Q) else 0)
            gradients.append(prefix(Q,D-x)-prefix(Q,E-x))
        bound = self.two_hinge(left,right)
        assert bound['exact'] is not None
        # Euler's exact homogeneous identity is an independent check of
        # ALL coordinate derivatives, including the two cutoff terms.
        predicted = (D*prefix(P,D)-E*prefix(P,E)+sum(x*g for x,g in zip(self.integers,gradients)))*self.unit
        assert predicted == bound['exact']
        groups = {}
        for i,g in enumerate(gradients):
            groups.setdefault(g,[]).append(i)
        gaps = [abs(X-Fraction(k)) for X in (D,E) for k,z in enumerate(P) if z]
        # Unsigned states are needed for the ACTUAL knot gap: a canceled
        # polynomial coefficient still represents a possible crossing.
        actual_gaps = [abs(X-position) for X in (D,E) for position,_ in self.states]
        gap = min(actual_gaps)*self.unit
        return dict(available=True,exactCompletePrefixDerivatives=True,
            coordinateGradients=[str(g) for g in gradients],
            equalGradientGroups=[dict(gradient=str(g),legs=legs) for g,legs in groups.items()],
            fixedTotalRedistributionInvariants=sum(len(v)*(len(v)-1)//2 for v in groups.values()),
            actualTwoHingeBoundaryGap=str(gap),
            signedPolynomialBoundaryGap=str(min(gaps)*self.unit),
            gradientSpread=str(max(gradients)-min(gradients)),
            homogeneousIdentityChecked=True,
            primeMatchingOrSourceScaleSaving=False)


def direct_response(logs,cutoff):
    """Independent small exact rational enumeration, for regressions only."""
    values = [(Fraction(0),1)]
    for x in map(binary_fraction,logs):
        values += [(s+x,-sign) for s,sign in values[:]]
    D = binary_fraction(cutoff)
    return sum((sign*max(D-x,0) for x,sign in values),Fraction(0))


def self_test():
    import random
    rng = random.Random(919)
    checks = 0
    for count in range(2,12):
        for grid in (8,32,128):
            logs = [mp.mpf(rng.randint(1,700))/128 for _ in range(count)]
            profile = SubsetMoments(logs,grid)
            for ratio in (0,.1875,.46875,.71875,1,1.125):
                D = mp.fsum(logs)*mp.mpf(str(ratio))
                truth = direct_response(logs,D)
                bound = profile.response(D)
                assert bound['lower'] <= truth <= bound['upper']
                reflected = profile.response(mp.fsum(logs)-D)
                truth_r = direct_response(logs,mp.fsum(logs)-D)
                assert truth == (-1)**count*truth_r
                assert reflected['lower'] <= truth_r <= reflected['upper']
                recursive,audit = profile.recursive_response(binary_fraction(D)/profile.unit)
                assert audit['complete'] and recursive*profile.unit == truth
                checks += 1
            D,E = mp.fsum(logs)*mp.mpf('.40625'),mp.fsum(logs)*mp.mpf('.6875')
            bound = profile.two_hinge(D,E)
            truth = direct_response(logs,D)-direct_response(logs,E)
            assert bound['lower'] <= truth <= bound['upper']
            checks += 1
    # The sparse-lattice branch must keep BOTH exceptional legs and
    # every one of their subset shifts. Check it by direct enumeration.
    sparse_logs = [mp.mpf(i) for i in range(1,13)]
    sparse_logs[2] += mp.mpf(3)/128
    sparse_logs[8] += mp.mpf(5)/64
    sparse = SubsetMoments(sparse_logs,512)
    assert sparse.sparse_lattice and sparse.exceptional_legs == 2
    for D in (mp.mpf('15.375'),mp.mpf('39.625'),mp.mpf('60.125')):
        assert sparse.response(D)['exact'] == direct_response(sparse_logs,D)
        checks += 1
    # Independent finite differences verify coordinate sensitivities and
    # fixed-total invariants without reusing the polynomial division.
    sensitivity_checks = 0
    lattice_logs = list(map(mp.mpf,[1,2,3,7,11,15]))
    p = SubsetMoments(lattice_logs,256)
    for D,E in ((mp.mpf('13.375'),mp.mpf('21.625')),
                (mp.mpf('9.25'),mp.mpf('35.125'))):
        analysis = p.coordinate_sensitivity(D,E)
        step = mp.mpf(1)/1024
        assert binary_fraction(step) < Fraction(analysis['actualTwoHingeBoundaryGap'])/4
        base = direct_response(lattice_logs,D)-direct_response(lattice_logs,E)
        for i,g in enumerate(analysis['coordinateGradients']):
            changed = lattice_logs[:]; changed[i] += step
            derivative = (direct_response(changed,D)-direct_response(changed,E)-base)/binary_fraction(step)
            assert derivative == Fraction(g)
            sensitivity_checks += 1
        for group in analysis['equalGradientGroups']:
            if len(group['legs']) < 2:
                continue
            i,j = group['legs'][:2]
            changed = lattice_logs[:]; changed[i] += step; changed[j] -= step
            assert direct_response(changed,D)-direct_response(changed,E) == base
            sensitivity_checks += 1
    # A signed polynomial coefficient can cancel while the UNSIGNED
    # subset knot is real. Such a boundary must NOT disappear from the
    # claimed radius of an affine neighborhood.
    boundary = p.coordinate_sensitivity(mp.mpf(3),mp.mpf('5.125'))
    assert Fraction(boundary['actualTwoHingeBoundaryGap']) == 0
    assert Fraction(boundary['signedPolynomialBoundaryGap']) > 0
    # A completed hierarchical recursion covers all 2^55 subsets, while
    # a deliberately insufficient budget is explicitly unresolved.
    hierarchy = SubsetMoments([mp.mpf(2)**i for i in range(55)],256)
    recursive,audit = hierarchy.recursive_response(Fraction(2**53+13,4)/hierarchy.unit)
    assert audit['complete'] and audit['visitedExactStates'] < 200
    tiny = SubsetMoments([mp.mpf(i) for i in range(1,12)],8,recursion_budget=1)
    unresolved,audit = tiny.recursive_response(Fraction(25)/tiny.unit)
    assert unresolved is None and not audit['complete']
    # On exact integer-grid inputs the backend resolves EVERY subset,
    # even though enumeration of the 2^63 subsets is infeasible.
    logs = [mp.mpf(1+(i*37)%113) for i in range(63)]
    profile = SubsetMoments(logs,sum(map(int,logs)))
    for D in (mp.mpf('733.25'),mp.mpf('1421.75'),mp.mpf('2300.125')):
        bound = profile.response(D)
        assert bound['exact'] is not None
        reflected = profile.response(mp.fsum(logs)-D)
        assert bound['exact'] == -reflected['exact']
    return dict(passed=True,exactRationalEnumerations=checks,
                independentSensitivityChecks=sensitivity_checks,
                canceledUnsignedKnotRetained=True,sparseExceptionalSubsetsVerified=True,
                independentSignedRecurrenceChecks=180,
                incompleteRecursionNeverPromotedToExact=True,
                complete63FactorSubsets=str(2**63),
                bothParitiesMomentsAndTwoHingesRetained=True,
                inputRoundingNotAnIntervalLogCertificate=True)
