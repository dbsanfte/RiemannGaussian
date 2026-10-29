# Advancing finite descendants: exact rational Green attempt

2026-10-25. This report tests the actual descendant recurrence in its m-variable; it uses only multiplication by Z on the fixed quotient B=R[Z]/G, not shifts of Z. No improvement of the paid soft O(J+sqrt(JM)) query is proved. The original acquisition goal remains open.

## 1. A concrete Padé/Green-function initialization attempt

Let C_0=1 and C_n(Z)=prod_(r=1..n)(Z-q^r-q^-r). Define A_M(u)=sum_(j=0..M-1) C_j(Z)u^j. The exact finite equation is

    q*u*A_M(q*u)+(1-Z*u)*A_M(u)+q^-1*u*A_M(q^-1*u)
       = 1-C_M(Z)*u^M.                                      (1)

All coefficients belong to B. Evaluating at u=q^m gives the previously derived finite descendant recurrence. The state equation is legitimate on B and has order two in m. The attempted algorithm is to initialize its two states by finding a low-degree rational exact Green generator A(u), normalized by A(0)=1, satisfying (1) with right side 1, then recover the truncation/boundary through approximants or a middle product.

The following exact analysis decisively excludes its *low-degree exact rational generator* step on generic scalar components. It does not exclude truncated Padé, fast approximants with other representations, or an algorithm exploiting guaranteed-hit promises.

## 2. Small exact rational Green generators are exceptionally restricted

**Derived lemma.** Work over a field K with unit q, order L>2 (or infinite order), and scalar t. Suppose A(u) in K(u) satisfies

    q*u*A(q*u)+(1-t*u)*A(u)+q^-1*u*A(q^-1*u)=1.                (2)

There is no pole at zero: if its order were r>0, the A(u) term has order r while both terms multiplied by u have order at most r-1. For nonzero poles pass to an algebraic closure. Their q-orbits have length L.

If one such orbit has some poles, its missing positions cannot contain two consecutive positions: at the missing position adjacent to a block of poles and to another missing position, exactly one shifted A term has a pole, with a nonzero coefficient, contradicting (2). Therefore at least ceil(L/2) positions in that orbit are poles. In particular any nonpolynomial rational A has denominator degree at least ceil(L/2). For infinite-order q, take an extremal pole in its finite orbit support; the same argument excludes every nonzero pole, so A must be polynomial.

If A is polynomial of degree d, coefficient comparison at zero and successive powers of u forces its coefficients to be C_0(t),...,C_d(t), and the top equation forces C_(d+1)(t)=0. Thus polynomial solutions occur precisely at terminating trace nodes t=q^r+q^-r; the minimal such r determines degree r-1 (subject to possible earlier collisions).

**Consequence for this task:** in either residue field, L>16k², so a nonpolynomial rational exact generator needs denominator degree >8k², far above J=soft O(k). A polynomial generator at a hit t=q^r+q^-r can still have degree r-1 up to M-1; components outside the full q-trace orbit have no polynomial generator. A component that misses the searched interval but lies elsewhere in the full q-trace orbit can terminate later, so absence of a hit in the searched interval alone does not exclude polynomial generators. Consequently a uniform two-start initialization by exact rational functions of degree soft O(J) fails. This is a statement about this specific ansatz, not a lower bound for recurrence advancement or all algorithms.

The proof uses only field specialization, not access to unknown primes. It establishes why a claimed small rational Green state needs a different representation or a genuinely truncated approximation theorem.

## 3. What the truncated approximant must actually compute

The unique formal solution of (2) at u=0 has coefficients C_n(t). Finding A_M modulo u^M is therefore the exact bivariate task

    Find A in B[u]/u^M with A(0)=1 and
    q*u*A(q*u)+(1-Z*u)*A(u)+q^-1*u*A(q^-1*u)=1 mod u^M.

The desired residue is minus the u^M coefficient of its residual. This is a precise **residual-only q-Padé primitive**: compute only that residual coefficient, or a collision-preserving projection of it, without materializing the M coefficients in B. It is stronger than approximant algorithms whose output includes A_M, which has up to JM scalar coefficients. A middle-product proposal must supply a compact representation and initialization and avoid that output charge. Ordinary power-series Newton inversion is inapplicable directly because the q-shifts couple coefficients by distinct diagonal multipliers rather than ordinary convolution.

A useful specification is: input monic acquired G, q, M; return the u^M residual coefficient above in soft O(J+sqrt M), with finite-ring divisions certified or factor-revealing, and support the same task for restricted seed intervals for label recovery. Equation (1) proves correctness of this reduction. It does not provide the requested complexity, and the primitive is not asserted to be easier than the original product.

## 4. A constructive full-period diagnostic: Dickson compression

Suppose, as an additional assumption, q has *known common exact order* L in the coefficient fields and the roots of X^L-1 are exactly its distinct powers. Define the Dickson polynomial D_L by

    D_L(x+x^-1)=x^L+x^-L.

Then the full-period kernel satisfies

    C_L(Z)=D_L(Z)-2.                                         (3)

Proof: substitute Z=x+x^-1 and multiply the factors x^-1(x-q^r)(x-q^-r); the result is x^-L(x^L-1)^2=x^L+x^-L-2. Equality of polynomials follows. Dickson doubling computes D_L mod G in soft O(J log L) ring operations via D_(2n)=D_n²-2 and the standard adjacent-index pair identities. Thus complete-period collision testing admits a small quotient computation without scanning L roots.

Also C_(n+L)=C_L*C_n, so the formal exact Green generator is rational:

    sum_(n>=0) C_n*u^n
      = (sum_(n=0..L-1) C_n*u^n)/(1-C_L*u^L).

The denominator coefficient C_L is cheap under the extra period assumption, but its degree L and the unacquired numerator remain large. Equation (3) explains one genuine mechanism for cheap long transfer: complete cyclic spectral sets have Chebyshev/Dickson compression. It does not solve the required incomplete prefix M<L, does not discover the local orders, and does not license choosing an artificial short period. The project's long-order setup explicitly prevents using a short full cycle to replace the native window.

For unknown semiprime components with different orders, a common supplied exponent L that is merely a multiple requires accounting for multiplicities; equation (3) as written requires the exact distinct-power hypothesis. No such L is acquired here.

## 5. Askey–Wilson literature and precise relevance

Primary source: Siddhartha Sahi, *Raising and Lowering Operators for Askey–Wilson Polynomials*, SIGMA 3 (2007), 002, published 2007-01-04, [author PDF](https://sites.math.rutgers.edu/~sahi/Reprints/07raisingAskeyWilson.pdf), §2.2 Theorem 1 and equations (2)–(4). Its operators use rational coefficients multiplying q-shifts of the Laurent argument; the theorem supplies raising/lowering identities for the four-parameter Askey–Wilson family. This supports bispectral operator experiments but gives no stated algorithm for the present residual-only q-Padé task. Its rational denominators involving 1-x² and 1-qx² would require actual unit tests over R; long order of q alone does not certify these target-dependent factors.

The successful reduction here instead retains the figure-eight m-recurrence, which needs only Z multiplication and q-units. The Green-function denominator lemma and full-period Dickson identity above are direct derivations; no theorem attribution or novelty claim is made for them.

## 6. Ring operations, localization, and validation

Equation (1), its formal coefficient initialization, and Dickson polynomial recurrences are division-free after acquiring q^-1. Modular multiplication in B costs soft O(J), so O(log L) complete-cycle operations are affordable. Generic O(sqrt M) such operations still cost soft O(J sqrt M), above the target. Scalar field specialization in the rational-generator exclusion is an analysis device, not an executable use of the unknown factorization.

Any hypothetical fast residue evaluator must support shifted/restricted intervals or deliver an index label. Full-window zero values alone do not recover i. In the trace fold each local hit gives x=q^i or q^-i, with possibly different signs at the two primes. Test both signs on the original row using the established gcd/annihilator consumer. Initialization and interval calls are part of the budget.

No new code is needed to validate the coefficient proof of (1) beyond the prior exact composite-ring reproducer.

## Outcome

The low-degree exact rational Green-function attempt fails for a precise reason stronger than merely unspecified starts: finite poles require at least half a full q-orbit. A viable approximant method must compute a high-order *residual only* from a compact state without producing the truncated series. Complete-cycle Dickson compression provides an executable special-family diagnostic, while incomplete-window advancement remains unsolved.

## Addendum: a finite short-Padé criterion

This strengthens the specific exact-rational test to a finite-order approximation test; it is not a lower bound for arbitrary compact states or algorithms.

**Derived proposition.** Over a scalar field K, let q be a unit of order r>2 (possibly infinite), and let

    F(u)=sum_(n>=0) C_n(t)u^n

be the unique normalized formal solution of (2). Suppose A=P/Q, Q(0)=1, deg P<=a, deg Q<=b, and A-F=O(u^M). Define

    L(A)=q*u*A(qu)+(1-t*u)*A(u)+q^-1*u*A(q^-1u).

Put W=Q(u)Q(qu)Q(q^-1u), which has constant term 1 and degree at most 3b. The numerator of L(A)-1 over denominator W is exactly

    q*u*P(qu)*Q(u)*Q(q^-1u)
    +(1-t*u)*P(u)*Q(qu)*Q(q^-1u)
    +q^-1*u*P(q^-1u)*Q(u)*Q(qu)
    -Q(u)*Q(qu)*Q(q^-1u).

Its degree is at most

    D=max(a+2b+1, 3b).                                     (4)

Indeed each of the first three products has degree at most a+2b+1, and the last at most 3b. Since L(F)=1, q-shifts preserve the u-adic order and the shifted terms multiplied by u increase it, the assumption gives L(A)-1=O(u^M). Multiplication by W preserves this vanishing. If M>D, the numerator polynomial must vanish identically. Hence **every such short Padé approximant is already an exact rational solution**.

Combine this with §2: if b<ceil(r/2), exactness forces A to be polynomial after cancellation. Its degree d is at most a, and termination forces C_(d+1)(t)=0, hence C_(a+1)(t)=0 because the C_n are nested products. Therefore the following is an explicit scalar-component exclusion criterion:

    M>max(a+2b+1,3b),
    b<ceil(r/2),
    C_(a+1)(t) != 0

imply that no P/Q of those degrees can approximate F modulo u^M. For infinite-order q, replace the second condition by the fact that every exact rational solution is polynomial.

**Application limits.** With a,b=soft O(J), M=Theta(k^(3/2)), J=soft O(k), and r>16k², the first two inequalities hold for sufficiently large k. The third is row- and prime-dependent: it excludes targets that are not among the first a+1 trace nodes in that component. It does not exclude components at early terminating nodes, and this report does not assert that every row or every guaranteed-hit component is generic. A quotient-wide Padé method would specialize to every scalar component, so a single component satisfying all three conditions defeats this particular uniform degree claim. No such component is assumed to be supplied by the factoring promise. This only identifies exactly which additional structural claim a proposed small Padé initialization would need.

The argument is division-free until passing to the scalar rational function field for analysis. Q(0)=1 certifies only formal invertibility at u=0; it does not certify that Q(q^m) is a unit in R for descendant-state evaluation. Any executable method must also pay these evaluations/unit checks, or retain formal data without such divisions.

## Addendum: full-period identity including repeated trace roots

For exact period L, the trace nodes q^j+q^-j repeat under j -> L-j. Root counting that ignores these multiplicities would give the wrong degree. The Laurent substitution proves the claimed identity with multiplicities intact:

    x^L*C_L(x+x^-1)
      = prod_(j=1..L)(x-q^j)(x-q^-j)
      = (x^L-1)^2,

because both ordered lists {q^j} and {q^-j} run through all L distinct roots of X^L-1. Thus

    C_L(x+x^-1)=x^L+x^-L-2=D_L(x+x^-1)-2.

The map K[Z] -> K[x,x^-1], Z -> x+x^-1, is injective: a nonzero polynomial of degree d contributes its nonzero leading coefficient to x^d, which no lower-degree term contributes. Hence C_L(Z)=D_L(Z)-2 as claimed. This proof covers odd and even L, repeated internal trace nodes, and the special trace endpoints. In particular odd L has the trace 2 once and each other trace node twice; no square-root normalization or missing factor is introduced. Over the unknown semiprime ring the identity holds if the exact distinct-power assumption holds in each local field with the same L, by the Chinese remainder theorem. A mere common multiple of different local orders does not satisfy that assumption.
