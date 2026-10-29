# Native arithmetic contraction candidate — 26 October 2026

Outcome: I tested a coverage-preserving arithmetic subfamily and an exact content/Adams descent, rather than repeating a single-row generating function. A shortest virtual Gauss witness can be restricted to content d=gcd(|a|,|b|) dividing the public k=2*3^e. Every such content block then descends to primitive (a0,b0), a smaller phase modulus, and a known Adams base beta^d, with all d phase lifts retained. This is an executable finite fusion identity with safe zero support. Its paid sum is still soft(k+sqrt(kM)); the primitive d=1 block remains size Omega(k). Thus it does not supply the desired soft-k zero-prefix primitive.

## Prior credit and scope

Read the complete scalar catalogue, its actual virtual-shortest-vector proof, hyperbola-cosets.md, deletion-and-grouping.md, swap-erratum.md, and the half-center row-cancellation/algorithm reports. Root-coset tiling, smooth valuation grouping, half-center opposite folding, lambda=0 axis removal and the resulting old query cost are prior results. The new candidate tested here is restricting the *content of the actual shortest witness* and descending the entire resulting arithmetic block. No claim is made that an arbitrary Gauss-reduced vector has the same content property: choose an actual shortest nonzero vector for the coverage proof.

All statements use the supplied continuing branch: distinct primes N=PQ, gcd(N,k)=1, beta a unit with odd local orders, q=beta^H with H=k², and both local q orders>16H. The algorithm does not acquire the virtual factor residue or shortest witness. It acquires a public subcatalogue proven to contain one.

## 1. A coverage-preserving smaller arithmetic subfamily

For the actual virtual tag j=[P]_k, the witness lattice is

    L_j={(a,b) in Z²: a j²=bN mod k},

with the factor-bin positive diagonal Euclidean scaling used in the archived coverage theorem. Let (a,b) be a shortest nonzero vector and d=gcd(|a|,|b|), using the usual gcd convention for an axis.

Claim: d divides k. Suppose a prime ell divides d. If ell does not divide k, dividing a,b by ell preserves the congruence, since ell is invertible modulo k, and strictly shortens the scaled vector. If ell|k and v_ell(d)>v_ell(k), dividing a,b by ell still preserves every prime-power divisibility in the congruence: at ell both coordinates retain v_ell(k), and at the other primes division is invertible. This also strictly shortens the vector. Both contradict shortestness. Therefore every prime of d divides k, with v_ell(d)<=v_ell(k).

Thus the public condition

    gcd(|a|,|b|) divides k                                  (1)

preserves at least one coverage witness for every allowed semiprime. It is invariant under swap and simultaneous sign change; it commutes with public zero-row deletion and complete-swap pruning. The four stored axes have d=k and are retained by (1). The condition is checked in soft(1) per acquired pair, hence soft(k) total, with no factor advice.

This is deliberately a support restriction, not division of a collision factor. Extra rows removed by (1) need no unit certification because the shortest-witness proof supplies coverage of the retained family. For later Boolean queries use the same retained family at every prefix; the old first-zero consumer applies to that family once its endpoint coverage is established.

The existing paid lambda=0 screen can remove the at-most-four axis rows at lambda=0. The new restriction does not alter its proof. The documented central screen and opposite fold then apply normally.

## 2. Exact finite content/Adams descent

For a nonaxis pair with content d|k write a=d a0,b=d b0, gcd(a0,b0)=1. Put

    k_d=k/d,    H_d=H/d²,    B_d=beta^d.

Every native phase root lambda is divisible by d: the congruence lambda²=4d²a0b0N mod k² implies p^(2v_p(d)) divides lambda² at each p|d. Hence Lambda=lambda/d is an integer and the phase equation becomes

    Lambda²=4a0b0N mod H_d,    0<=Lambda<d H_d.             (2)

Conversely every solution Lambda in that range gives exactly one original lambda=d Lambda. Partition it uniquely as

    Lambda=lambda0+t H_d,
    0<=lambda0<H_d,  0<=t<d,
    lambda0²=4a0b0N mod H_d.                              (3)

All endpoints and all d lifts are included. The corresponding acquired target is

    x_t=B_d^(a0+b0N+lambda0) rho_d^t,
    rho_d=B_d^H_d=beta^(H/d),    rho_d^d=q.                (4)

These are known integer powers of beta. This is an actual Adams d change of base, not a hypothetical N-Frobenius action. Since d|H, each local order of B_d is at least that of beta^H=q, and remains odd and>16H. Thus any use of the existing licensed nonzero-global-annihilator consumer on B_d has the required order premise. Original exponent labels can alternatively be retained, avoiding any new consumer.

For one such residual phase lambda0, the finite row-clock contraction is exactly

    prod_(t=0)^(d-1) prod_(i=1)^m (x_t-q^i)
      =unit * prod_(r=1)^(dm)(1-c rho_d^r),               (5)

where x0=B_d^(a0+b0N+lambda0), c=x0^-1, and the explicit unit is

    x0^(dm) rho_d^(m d(d-1)/2).

Indeed x_t-q^i=x_t[1-x0^-1 rho_d^(di-t)], and the exponents di-t fill 1..dm once each. No collision factor is inverted. This special d-lift contraction is the previously known tiling mechanism, now tied to the new witness-content restriction rather than counted as a new independent identity.

The negative-clock products have the same fully specified finite tiling after reversing the r interval. All half-center row identities can instead be applied before or after (5), retaining the uncentered opposite carry. The common half-center eta=beta^(H/2) remains the same for every d, since B_d^(dH_d/2)=eta whenever that exponent is integral; if dH_d is odd, use eta directly rather than asserting an integer exponent in B_d. No extraction of roots of units is needed.

## 3. Paid full-family cost and the surviving primitive block

The residual primitive pairs satisfy |a0b0|<k/d². If this range is empty there is no nonaxis block. Otherwise the same 2,3 root-count estimate bounds the residual phase list C_d by soft(k/d²); expanding d lifts gives J_d=soft(k/d). These are bounds, not assumptions that each residual pair has only constantly many ramified roots.

Acquire all residual pairs, roots and starts, or simply filter and regroup the already acquired original catalogue. Both methods cost soft(k) total. For a requested m, (5) and the old monic geometric evaluator give

    soft(C_d+sqrt(C_d*d*m))
       =soft(k/d²+sqrt(km/d))

for block d, with logarithmic subgroups for any remaining lower-modulus ramified root-coset types. Summing over d=2^alpha 3^nu dividing k gives soft(k+sqrt(km)), since sum_d d^-1/2 is bounded by two geometric series. This explicitly pays the transformed starts and longer intervals. It is not additive soft(k+sqrt(m)).

This calculation treats nonaxis blocks. The remaining lambda!=0 axis rows still number O(k), even after the at-most-four lambda=0 screen. Their public deletion exceptions prevent blindly inserting a complete axis coset and dividing out its deleted row: that row may contain a trivial exact zero. Keep the actual retained axis list and use its old paid evaluator, costing soft(k+sqrt(km)), or use the previously proved explicit missing-row handling. Thus the stated full-family upper bound also pays axes, with no improper zero-factor division. The axis contribution is an additional unresolved cost for the hoped-for soft-k primitive, not something the content restriction deletes.

The primitive block d=1 cannot be dropped under the current proof. It also remains large as an acquired family: a=1 and positive b<k with bN=1 mod3 give unit discriminant roots modulo 3^(2e), and the mod4 equation has even roots. There are Theta(k) such b and corresponding nonaxis phase rows, all with content 1. For b!=0 none is publicly deleted on the hard branch; complete swaps retain their partners, and diagonal deletion removes at most the b=1 pair in this displayed subfamily. Opposite folding changes this by constant factors. This is a size fact for this candidate, not a lower bound on another selector or a proof that every such row is required for coverage.

## 4. The tempting N-Adams fusion, with its exact discrepancy

At fixed lambda the swap has x'=beta^(b+aN+lambda). A natural cabling/Adams proposal is to identify x' with x^N. Their exact ratio is

    x^N/x'=beta^[(N²-1)b+(N-1)lambda].                    (6)

The native conic congruence controls lambda² modulo H, not this exponent modulo the unknown local orders. Even lambda=0 would require the extra beta^(N²-1) relation for the b direction. In R, raising to N is not a Frobenius ring homomorphism and does not implement the swap for free.

A standard paid exponent test is available: compute gcd(beta^(N²-1)-1,N). A proper gcd factors; a saturated gcd supplies the nonzero known global exponent N²-1 to the licensed extractor; otherwise the discrepancy generator is a unit away from 1. This costs soft(log N) powering/gcd work plus the already licensed extractor when invoked. This elementary test is not claimed as a new factoring technique. It cannot justify setting that generator to 1 on the continuing branch, and the lambda term in (6) remains even if the b discrepancy were removed. Thus the tested N-Adams fusion is not a missing-cost-free way to merge different divisor labels.

The exact phase coupling itself reads

    beta^(lambda²)=beta^(4abN) q^c,
    c=(lambda²-4abN)/H in Z.                              (7)

Its carry is acquired, but depends on a,b,lambda and is generally large. A finite quantum-dilogarithm/fermionic transform using (7) must retain q^c and its row-dependent clock boundary. Dropping the carry would replace the actual phase relation by a root-of-unity relation. None of the finite q-binomial/pentagon formulas reviewed previously removes these varying carries.

## 5. Decision and a sharper remaining candidate

This pass supplies one proved coverage-preserving arithmetic restriction (1), a fully explicit finite descent (2)–(5), and a paid N-Adams factor branch. It does not supply the required whole-family fast prefix. The genuine remaining candidate is to contract the content-1 divisor/phase block across (a0,b0) using its exact carried conic relation (7), or to prove a substantially smaller public witness subfamily inside that block. Root-coset tiling and smooth-content descent alone preserve the old square-root mass and do not solve that contraction.

No repository files or frozen source reports were edited. No generic single-row Heine/Padé audit was repeated, and no exponent improvement is claimed.

## Auxiliary-torsion / Bloch-boundary candidate

I tested an actual small Fourier/Bloch conjugation, keeping its auxiliary torsion parameter separate from arithmetic q. Let A=R[omega]/(omega²+omega+1), where omega is an auxiliary cubic root. This is a rank-two extension; 3 and 1-omega are units because the actual factors of N exceed 16H. For a three-element complete root-lift block set rho=beta^(H/3), so rho³=q, and let D=diag(1,rho,rho²). Conjugating by the unnormalized cubic Fourier matrix F_(r,s)=omega^(rs) gives

    (F D F^-1)_(r,s)
        =(1-q)/[3(1-rho omega^(r-s))].                    (8)

Every denominator is certified unit: the product of 1-rho omega^j over j=0,1,2 is 1-q, already a unit. Thus (8) is valid over A without any target inverse. It is an explicitly acquired dense 3-by-3 circulant Cauchy matrix, and its numerator 1-q is the exact Bloch boundary. Replacing it by zero, as in a torsion specialization rho³=1, would destroy the actual arithmetic operator.

For general L|k, the same construction formally gives a Cauchy circulant with kernel

    (1-q)/[L(1-rho zeta_L^(r-s))],
    rho=beta^(H/L), rho^L=q.                             (9)

The auxiliary Weyl commutator is zeta_L, not q. This avoids the incorrect finite-q-Weyl representation, but does not supply a cheaper norm. In particular

    prod_(i=1)^m det(D-q^i I)
       =prod_(s=0)^(L-1) prod_(i=1)^m(rho^s-q^i),         (10)

and Fourier conjugation leaves this determinant unchanged. Equation (10) is exactly the native root-coset tile: length Lm at finer base rho. Binary powering C rather than D computes powers of rho^s, not the differing factors D-q^i I. A valid accelerated transfer would still need to acquire the varying-shift product in (10); (8) supplies its inexpensive local initialization, not that contraction.

At full zeta_k, the cyclotomic algebra has rank phi(k)=Theta(k), so an explicit length-k Fourier transform over it has Theta(k²) base coordinates before any structural compression. Recursing with only omega keeps the extension rank two for a tensor (Z/3Z)^e Fourier transform, but this is not the cyclic Z/3^eZ transform: integer carries in the native quadratic phase must then be represented as additional non-diagonal gates. No tensor-rank bound for the resulting determinant/zero predicate is supplied by those local butterflies.

### Exact native stationary-phase boundary

Writing an actual lambda as r+ks, 0<=r,s<k, gives a precise two-stage conic test:

    r²=4abN mod k,
    c=(4abN-r²)/k in Z,
    2rs=c mod k.                                       (11)

Its phase weight is beta^lambda=beta^r (beta^k)^s, with (beta^k)^k=q. The second congruence can indeed be represented by the finite auxiliary-character projector

    [2rs=c mod k]=(1/k) sum_(t=0)^(k-1)
                               zeta_k^[t(2rs-c)].       (12)

Here k is a unit in R. Equations (11),(12) are an exact Gaussian/stationary-phase encoding of the native lift, including degenerate 2r; no inverse of 2r is assumed. However (12) is a *linear* projector. Applying it to weighted sums does not evaluate the product over accepted (r,s), which is the required zero-prefix norm. Its direct diagonal-projector determinant lives on k² lift states; enumerating its sparse accepted states returns the already acquired native roots, and then the old norm problem. A proposed metaplectic shortcut must still prove how this projector's determinant/norm contracts across the bounded (a,b) hyperbola with the q-boundary retained.

The concrete tested candidate is therefore the unit-safe cubic Cauchy circulant (8) coupled to the exact lift projector (11). It supplies a lawful constant-rank local Fourier operation, but I found no plausible explicit map from its *linear* stationary-phase matrix element to the full-family multiplicative zero predicate that avoids the old Lm support. This appendix records the candidate and the exact boundary rather than treating an auxiliary metaplectic representation as a new arithmetic algorithm.
