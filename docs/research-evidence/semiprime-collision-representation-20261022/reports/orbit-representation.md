# Constructive native-to-orbit representation attempt

22 October2026. Original scalar gamma=t², supplied public unit t, prime row modulus m, whole coefficient algebra A=(Z/N)[X]/(X^m−1). No frozen changes or numerical coverage claims. The deterministic gcd-aware KMP consumer for fixed cyclic coefficient arrays is retained. This report constructs exact low-degree presentations and one shared native POWER-PIECE diagonal, but does not obtain fixed arrays representing the complete covered native leaf.

## 1. A genuinely acquired low-degree comparison family

Use the unit-safe rational base

    W=t(1+gamma X)/(X+gamma).

The base and W^N are ONE acquired vector each, in soft m by modular powering. Unit denominators follow from the retained odd order: norm(X+gamma)=gamma^m+1 is a unit. For any already acquired fixed B,

    (X^j+gamma)(B−rho_j W)
      =C+X^jD,
    C=gamma B−t, D=B−t gamma.                    (1)

Thus whole-local matching B=rho_j W is exactly additive cyclic matching of the fixed coefficient arrays D and −C, with unit denominator preservation. Gcd-aware KMP directly applies in soft m; randomness and coefficient sparsity are unnecessary. Restrict output rotations to unit j if wanted. The arrays are actually acquired, not specified entrywise by an unpaid oracle.

Taking B=W^N makes (1) an actual public comparison family. It does NOT establish all-input native coverage: at the true tag j=P modm, Frobenius gives W^P=rho_jW modP, hence W^N=(rho_jW)^Q, not rho_jW. For a fixed exponent a, clearing B−(rho_jW)^a gives O(a) shifted common vectors, with explicit binomial coefficients. The fixed-a=1 case is therefore solved as an orbit comparison; native a_j can be Theta(m), and this expansion does not produce a polylogarithmic fixed-array family for the full query.

## 2. Exact native rearrangement and finite-fiber presentation

Write B=W^N. The corrected target is

    Z_j=W^ell_j (rho_jW)^a_j rho_(j^-1)(B), Q=W^(m²).

The exact covered equation Z_j=Q^I rearranges to

    B=rho_j(A_(j,I)),
    A_(j,I)=W^(m²I−ell_j)(rho_jW)^(−a_j).          (2)

At the true P tag it equals the original integer native index. Source coverage is whole local, not an isolated character evaluation. Equation(2) is useful for identifying the data needed by KMP, but A depends on BOTH j and unknown I. No per-j/I acquisition is free.

Changing to the W-coordinate has a particularly small public presentation. Solving the Möbius map gives

    X=(t−gamma W)/(W−t gamma),
    (t−gamma W)^m−(W−t gamma)^m=0.                (3)

The leading coefficient (−gamma)^m−1=−(gamma^m+1) is a unit; (3) and its monic version have O(m) explicit binomial coefficients and are paid in soft m. This is an exact degree-m carrier presentation with no hidden root extraction. It does not make the many powers in (2) simultaneous scalar values: each distinct polynomial remainder still has rank m. No bounded-fiber operation eliminating I follows merely from presentation(3).

The automorphism-versus-power defect remains visible. Since a_j j²=N modm,

    (rho_(j²)W)^a_j
       =rho_N(W) * rho_(j²)(W^a_j/rho_(a_j)W).    (4)

The public conjugate rho_N(W) is cheap. The residual rational defect W^a/rho_aW has a numerator/denominator with O(a) explicit binomial terms, not uniformly O(polylogm) terms. This rewrites one varying factor as a common conjugate plus a short DEGREE-a defect, but summing that expansion over native rows would cost Theta(m²). No theorem shrinking the residual source defect is asserted.

## 3. A paid diagonal of the native j²/a power piece

There is nevertheless an exact whole-family contraction for one nontrivial part of(4). Work in the FULL cyclic coefficient algebra, including its trivial component. For any fixed integer c>=0 and b=cN modm,

    [X^b] rho_(j²)(W^a_j)
      =[X^(c a_j modm)] W^a_j
      =CT[(W/X^c)^a_j],                           (5)

because a_j=Nj^−2 modm. Here CT means the actual constant coefficient AFTER cyclic reduction, not a formal power-series coefficient before reduction. Thus all these varying-tag selected coefficients are ONE power-trace sequence of the fixed rational R_c=W/X^c. This is stronger than describing each j separately, and retains every modular wrap/carry.

For c=1 there is a very explicit paid constructor. Let

    R_1=t(1+gamma X)/(X(X+gamma)),
    Delta(z)=det(1−z R_1) on the m-dimensional cyclic algebra.

Then

    Delta(z)=res_X(X^m−1, X²+(gamma−zt gamma)X−zt)/(gamma^m+1).

Put s=gamma(zt−1), p=−zt, and S_0=2, S_1=s, S_n=s S_(n−1)−p S_(n−2). The two roots of the monic quadratic have sum s and product p, so the resultant is exactly

    p^m−S_m+1.                                    (6)

This identity is polynomial and does not require adjoining or choosing either quadratic root. At z=0 its value is gamma^m+1, so Delta(0)=1 as required. Polynomial matrix powering or the doubled power-sum recurrence acquires S_m and Delta, degree at most m, in soft m bit work with the native O(logN)-bit scalars. The denominator gamma^m+1 is guarded and is a certified unit under the retained order promise.

Finally,

    −Delta'(z)/Delta(z)
       =sum_(a>=1) Tr(R_1^a) z^(a−1),
    CT(R_1^a)=Tr(R_1^a)/m.

Formal series inversion through degree m costs soft m, and m is a unit. This acquires ALL entries needed in(5) for every native a_j<m in soft m. No integer a-dependent denominator or hidden field is required. The trace is the regular algebra trace, so the identity automatically includes trivial and proper character components; for prime m the latter distinction is simply trivial versus primitive. This gives actual scalar output O(m).

For fixed c>1 the same construction uses the monic degree-(c+1) polynomial X^c(X+gamma)−zt(1+gamma X). A fixed-dimensional companion/exterior-power computation acquires its resultant against X^m−1 in soft m; if c grows, its matrix/degree cost must be charged. No assertion of simultaneous m slopes at the same price is made.

This contraction is an unweighted rational power projection, specialized to the native quadratic tag relation. It is NOT advertised as new access to the full weighted native trace, whose acquisition remains open. It provides a concrete narrowly usable interface for another construction to exploit.

## 4. Why the contraction has not yet absorbed the whole native source

Multiplying the power piece in(5) by an arbitrary acquired B changes its selected coefficient to

    [X^b] B rho_(j²)(W^a_j)
       =sum_l B_l [X^((b−l)j^-2 modm)] W^a_j.

For b=N this is a sum of m different slopes c_l=(N−l)N^−1 modm. Formula(5) acquires a FIXED slope cheaply, not this weighted mixture for all a_j. The additional native factor (rho_j W)^ell_j introduces another varying power and permutation. Simply acquiring all its rank-m vectors or all the slopes restores quadratic work. No cancellation from the canonical ell_j=m b_j−2a_jj has been proved to turn this weighted mixture into a constant/polylogarithmic number of fixed R_c traces.

Multiplying the original base W by X^c does not resolve that issue. Native grade ell_j+a_j j+N j^−1 is zero modm, so the monomial gauge cancels globally from Z_j, and X^(c m²)=1 in the seed. Thus this gauge provides useful equivalent power-piece coordinates but no new independent native support equations.

The antipodal products also remove phase rather than isolate I:

    Z_j Z_-j=gamma^(N+a_j) Q^(−s_j).

At a true leaf Z_j=Q^I, this prescribes Z_-j=gamma^(N+a_j)Q^(−I−s_j). The second equation follows from the paid pair product; it is not another independent fixed-array constraint selecting I. Eliminating I via the scalar conjugation norm returns the original gamma exponent mask, which is the unsolved query. No saturation/recovery equivalence is obtained by ignoring that distinction.

## 5. Formal scalar-parameter jets are not a valid shortcut

One tempting normal form expands t, hence gamma=t², around t=0 or t=1 so W becomes a monomial or a scalar to leading order. But the Frobenius relation W_t^P=rho_j(W_t) is valid for scalar t in F_P as a FUNCTION, not as a low-degree identity over F_P[t]. The elementary polynomial t^P−t vanishes at every scalar yet has derivative−1. Differentiating the source relation or truncating its formal parameter jets can therefore destroy the very source one intends to retain. A nilpotent parameter also satisfies (1+epsilon)^P=1 when its truncation degree<P, rather than behaving like an arbitrary fixed scalar t. No source retention is inferred from such a deformation.

At the degenerate rational limits t=0 or gamma=1 the remaining base becomes monomial/scalar and orbit equations can become globally tautological; that is not an acquired separator for the original source. This is an exact warning about a candidate construction, not a generic lower bound against other parameter transforms.

## Current outcome and precise constructive next step

Actual paid outputs obtained here are (i) the complete low-degree comparison family(1) as TWO fixed arrays for deterministic KMP, (ii) the low-degree W-carrier presentation(3), and (iii) the native selected power-piece diagonal(5)–(6) as O(m) acquired scalars. The all-input bridge would need to package the FULL weighted native expression into O(polylogm) such fixed arrays or power traces while retaining the unknown SAME row/index source and a proper-gcd/original-annihilator recovery route. In particular it must absorb B=W^N and the ell_j-power without constructing m length-m vectors. No such packaging has been proved, so no full collision algorithm or factoring-rate improvement is claimed.

## Follow-up: exact varying-weight diagonal after the fixed-weight repair

The parent/torus agent's stronger fixed-weight resolvent constructor pays all Tr(B R_1^a), a<m, for an ARBITRARY ONE acquired B: its generating function Tr(Bg/(g−zf)) reduces the numerator modulo the same quadratic, using balanced evaluation in its companion algebra. This should be credited as a real strengthening of the power-piece interface, not omitted because B is dense. It still has ONE fixed weight.

For the actual native j² expression, the weight changes with a. Set b=N modm, a=a_j, R_1=W/X. Exact cyclic constant-term invariance under rho_(j^-2) gives

    [X^b] B rho_(j²)(W^a)
      =CT[rho_(a/b)(B) R_1^a]
      =sum_k B_k CT[(X^(k/b) R_1)^a].              (7)

All divisions a/b,k/b mean multiplication by b^−1 modulo m; these are public unit-index operations. The first equality RETAINS integer cyclic wrapping; it is not a formal-series coefficient approximation. The dependence on j has disappeared except through the two-to-one a_j values, but (7) does not become a fixed-weight power projection.

One can make the residual generating function completely explicit without claiming it acquired. Over geometric roots x of X^m−1,

    H_a=(1/m)sum_(x^m=1,k) B_k [R_1(x) x^(k/b)]^a.

Thus a possible shared evaluator is the first m coefficients of the weighted resolvent

    G(z)=(1/m)sum_(x^m=1,k) B_k/(1−z R_1(x)x^(k/b)).

This has m² spectral pairs before exploiting structure. For a nontrivial x, varying k cycles through all m roots, so the UNWEIGHTED full denominator collapses to factors involving z^m. The arbitrary B_k weights stay in its numerator. This supplies an exact compressed denominator, not an acquisition of the first m numerator coefficients. Multiplying out the denominator alone would repeat the old norm-only mistake.

The simple finite-group Fourier shortcut also needs a condition that is absent. Correlating the automorphism indices modulo m does not make a->R_1(x)^a periodic modulo m: a wrap introduces R_1(x)^m. For this W, that wrap cannot generally be replaced by a scalar. Indeed if W^m=c in the cyclic algebra at a retained hidden prime, compare coefficients1 and2 in

    t^m(1+gamma X)^m−c(X+gamma)^m =0 mod(X^m−1).

Because m and the binomial coefficients in these positions are units and m>=3, the comparisons force c=t^m gamma^(2−m)=t^m gamma^(4−m), hence gamma²=1, contrary to the high-order promise. Since X^m=1, R_1^m=W^m. This rules out this PARTICULAR scalar-wrap simplification, not a general bivariate/diagonal algorithm.

A genuinely useful next constructor would acquire (7) for all native a in soft m directly from the ONE B and low-degree W, perhaps by transposed bivariate reduction or a weighted root-of-unity resolvent, without forming its m² numerator/spectral data. Even if obtained, the additional W_j^ell factor in the full native source must be included or otherwise eliminated by an exact identity. No such constructor was proved in this follow-up.
