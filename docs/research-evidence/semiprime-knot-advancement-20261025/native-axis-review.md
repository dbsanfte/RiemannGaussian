# Independent review: native axes exclude the short rational Padé ansatz

2026-10-25. **PASS, with the scope below.** This strengthens the scalar-component conditional obstruction to the actual full native catalogue quotient after the specified public zero-row and complete-swap pruning. It is not an obstruction to other representations, weaker selectors, or a different coverage-preserving pruning algorithm.

Inputs checked against the archived `scalar-catalogue.md` and `swap-erratum.md`: H=k², q=beta^H, the four signed axes including (a,b)=(k,0), all lambda roots in [0,H), scalar exponent E=a+bN+lambda, public deletion when E/H is an integer in [-M,M], and complete-swap pruning. The continuing branch has local orders ord(q)>16k². Diagonal pruning does not remove the off-diagonal axis rows. A successful factor/annihilator screen ends that branch; this review concerns the continuing full quotient.

## 1. Surviving native axis rows

For (a,b)=(k,0), the roots of lambda²=0 mod k² are exactly lambda=kt, 0<=t<k, since k²|lambda² implies k|lambda prime by prime. Thus E=k(1+t). Put r=1+t. For r=1,...,k-1, E/H=r/k is not an integer, so public zero-row deletion retains the row. The r=k row has E=H and is deleted because index 1 belongs to the native window.

The swap row (0,k,lambda) has

    E'=kN+k(r-1)=k(N+r-1).

Its E'/H is integral only if N+r-1=0 mod k. Among 1<=r<=k-1 this removes at most one value of r through complete-swap pruning; requiring the resulting quotient to lie in [-M,M] can only reduce the number removed. Therefore at least k-2 of these original axis rows survive both deletion stages. No claim is made if an additional, different pruning step deliberately removes them.

Their centered targets and trace nodes are

    x_r=beta^(kr),        z_r=x_r+x_r^-1.

## 2. Local order and exact collision criterion

Fix either prime p|N. Let L=ord_p(beta), let ell=L/gcd(L,k)=ord_p(beta^k), and let Rq=ord_p(q). Then

    Rq=L/gcd(L,k²) <= ell,

so ell>16k². This is the needed comparison; equality is not assumed.

Over the residue field, z_r=q^i+q^-i iff x_r=q^i or x_r=q^-i, by factoring the quadratic with roots q^i,q^-i. Consequently, for d>=1,

    C_d(z_r)=0
       iff ell divides r-ki or r+ki for some 1<=i<=d.       (1)

No zero multiple occurs: 1<=r<k and i>=1 imply ki-r>=1, and ki+r>=1. If (1) holds, a positive multiple m*ell lies in

    1 <= m*ell <= kd+k-1.

For a fixed positive multiple m*ell, the equation ki+r=m*ell determines at most one pair (i,r) with 1<=r<k, by quotient/remainder modulo k; the equation ki-r=m*ell also determines at most one. Bounds on i may reject either pair. Thus the number of axis r with C_d(z_r)=0 is at most

    B_d = 2*floor((kd+k-1)/ell)
        < (d+1)/(8k).                                    (2)

The endpoint kd+k-1 is correct, and the strict inequality follows from ell>16k² and kd+k-1<k(d+1). This is an upper bound; pairs can coincide or fail the allowed i range.

The z_r are locally distinct. Equality z_r=z_s implies ell divides r-s or r+s; for distinct r,s in [1,k-1], the nonzero absolute values are below 2k, while ell>16k². Thus neither divisibility is possible. Distinctness therefore survives passage from the original rows to a duplicate-free trace modulus G.

After the possible one additional swap deletion, at least

    k-2-B_d

locally distinct retained axis nodes have C_d(z_r)!=0. This count applies separately at each prime, with its own ell and possibly different exceptional r.

## 3. Consequence for finite short Padé initialization

Use the established finite-Padé lemma: for scalar trace t, a rational A=P/Q, Q(0)=1, deg P<=a, deg Q<=b approximating the normalized descendant generating series through O(u^M) must be exact if

    M > D=max(a+2b+1,3b).

If also b<ceil(Rq/2), the pole-orbit lemma forces A to be polynomial. Its degree is at most a, so exactness requires C_(a+1)(t)=0.

Set d=a+1 in (2). If

    k-2 > 2*floor((k(a+1)+k-1)/ell),                        (3)

there is a retained native axis component where C_(a+1) does not vanish. Specializing any quotient-wide Padé identity to that node contradicts the necessary termination condition. This specialization is mathematically legitimate because the constructed G contains that native node, even if other rows or repeated nodes are also present. It is not an algorithm using the unknown prime.

For a,b=soft O(J), J=soft O(k), and M=Theta(k^(3/2)), conditions M>D and b<ceil(Rq/2) hold for sufficiently large k. The right side of (3) is at most polylogarithmic in k, while k-2 grows linearly. Hence (3) also holds for sufficiently large k, with the precise asymptotic threshold depending on the fixed constants and logarithmic powers in the claimed soft bounds.

Therefore the *actual full acquired trace quotient* cannot admit this degree-soft-O(J) rational Padé initialization at precision M, on sufficiently large continuing native instances. The earlier generic-component premise is unnecessary for that particular full-quotient ansatz: the native axes supply many nonterminating components, even though the complete family has guaranteed collision components elsewhere.

## 4. Scope and costs

This excludes rational P/Q approximations in u with bounded u-degrees, normalized Q(0)=1, that represent the full formal descendant series modulo the full G through u^M. It does not exclude computing only the needed boundary combination, a projected residual, an algebraic or nonrational state, rational data of larger degree, or a selector that omits these axes with a separately proved cover. The argument establishes no general algorithmic lower bound and no new factorization exponent.

No new acquisition is used: the axis rows are already in the native catalogue. The nonzero-count proof is a local-field analysis, not a paid row test or an assumption that local orders are known. Existing label recovery, mixed CRT sign handling, and unit checks remain required by any positive algorithm.
