# Colour-cell/Farey coverage: acquired phases and aggregate query budget

26 October 2026. Bounded constructive follow-up to the authoritative trace packet. Scratch only; no experiments, tests, repository edits, or new preparation counted as a query gain. **No guaranteed power improvement obtained.** The concrete attempted reuse is a coarse congruence/Farey cell shared by many colour lifts; its full phase and interval costs are executed below.

## 1. Input and prior credit

Use k=2*3^e>16, H=k², prepared N=PQ<=k⁶, and native beta/q orders above 16H. For each unit colour j mod k,

    Lambda_j={v=(a,b):a*j²=b*N mod k},
    lambda_j(v)=-a*j-b*N*j^-1 mod H, in [0,H).

Prior virtual weighted-Gauss/content-d|k coverage retains its credit. The preceding packet publicly enumerates colours and factor-size scales, acquires a weighted short vector and its selected phase, and includes opposites/swaps and center/deletion recovery. Its full-query cost remains soft(k+sqrt(k*m)), m=O(k^(3/2)). The problem is scalar contraction or smaller guaranteed coverage, not acquiring those O(k polylog N) rows.

The earlier supplied-interval Farey code was read at `/tmp/semiprime-adaptive-gap-acquisition-20261023/sources/factorlab/factorlab/experiments/farey_cover.py`; it is byte-identical to `/tmp/semiprime-arithmetic-locator-20261024/sources/farey_cover.py`, SHA256 `1a44eefa5d114ef464f9ace0557a7711e37f4c5445d8761b43436bb9047c66bd`. It assumes a given factor-containing interval, not an algorithm locating that interval. No numerical output from that source is used here.

## 2. What identical lattices really save

For unit j,l, Lambda_j=Lambda_l iff j²=l² mod k. Since k=2*3^e, the unit square map has kernel {+1,-1}; this gives only a factor-two lattice deduplication. Its phases need not agree: lambda_(-j)(v)=-lambda_j(v) mod H. Reusing the lattice basis is free after acquisition, but it does not erase the required distinct row phases.

A sharper exact incidence check applies to a primitive integer vector v in Lambda_j. Since gcd(a,b)=1, membership forces a,b to be units modulo k: a prime 2 or3 dividing one would divide both. Consequently

    lambda_j(v)=-2*a*j mod k.

The value of lambda for this FIXED vector determines j uniquely modulo 3^e, since 2a is a 3-unit, and j is odd. Hence one fixed primitive native row WITH ITS PHASE belongs to at most one of the k/3 public unit colours. A method covering every public colour by fixed primitive phase rows therefore still needs Omega(k) rows. This is NOT a claim that the actual two factor colours of a fixed N require all public colours; excluding most colours through extra arithmetic could be a new solution. Nor does it apply unchanged to nonprimitive/content rows.

Swap-colour orbits j->N*j^-1 can likewise save a constant factor if all needed factor-size scales and swapped source maps are retained. No polynomial reduction follows just from these involutions.

## 3. Execute a nonprimitive coarse-cell reuse, including every phase

Take d=3^r with d² dividing k, and K=k/d. Suppose a fixed primitive v0=(a0,b0), with a0,b0 3-units, lies in the coarse lattice a0*j0²=b0*N mod K. Consider the one scaled vector v=d*v0 across all d colour lifts

    j_t=j0+K*t mod k, 0<=t<d.

It is stationary in Lambda_(j_t) for every t. Thus this really is a common slope/Farey representative for a coarse colour cell, not an arbitrary unrelated list. Its native admissibility must still be checked: d²*|a0*b0|<k. The primitive/unit-core hypothesis here excludes axes; the separate native-axis calculation is given below. A coarse Gauss vector does not automatically pass this stricter product test.

Put J0=j0^-1 mod H and u=(a0-b0*N*J0²)/K, an integer. Because K is divisible by d, the inverse expansion, after multiplication by d, truncates exactly modulo H:

    j_t^-1=J0-K*t*J0²+K²*t²*J0³ + remainder,
    d*remainder=0 mod H.

Therefore the actual canonical phase is the reduction of

    lambda_(j_t)(v)=lambda_(j0)(v)+(H/d)*Q(t) mod H,
    Q(t)=-u*t-b0*N*J0³*t² mod d.                  (1)

The quadratic coefficient is a 3-unit. For d>1, completing the square modulo odd d shows its image has at least phi(d)/2=d/3 values: the unit-square residues alone give that many. Thus a full coarse cell needs at least d/3 DISTINCT phases on this one common vector. Isolated highly ramified fibers can contain many colours, but they do not yield a small aggregate list. Acquiring the full colour/phase outputs costs soft d, not soft log d.

For the actual native horizontal axis v=(epsilon*k,0), the separate phase difference is -(H/d)*epsilon*t modulo H. For the native vertical axis v=(0,epsilon*k), it is (H/d)*epsilon*N*J0²*t modulo H; its quadratic remainder vanishes because d² divides k. Each coefficient is a unit modulo d, so each native axis has EXACTLY d distinct phases. These axes correspond to nonprimitive coarse cores (epsilon*K,0) or (0,epsilon*K), and are not cases of the primitive-core theorem. Nonzero-phase axes remain subject to the inherited complete axis ledger.

This is an actual finite same-cell calculation on the phase law. It rules out counting one coarse slope as one native row independently of its phases. It is not a bound against all coarse covers: larger d, nonunit primitive cores, root-coset orbit tiling, or a new correction identity need their own analysis. The already established content/coset tiling is not counted as a new gain.

## 4. Execute public factor-interval subdivision and charge its budget

For a fixed colour and admitted row, let g(p)=a*p+b*N/p. On a public interval centered at p0, of length L<=p0, containing a hypothetical factor p, Taylor's theorem gives the conservative exact bound

    |g(p)-g(p0)| <= |a-b*N/p0²|*L/2
                         +8*|b|*N*L²/p0³.         (2)

With its known lambda, (2) supplies an explicitly acquired INTEGER clock interval centered near (g(p0)+lambda)/H. Endpoints are outward rounded. Both signs, the original I-to-negative opposition map, and deletion over the new interval must be retained; an extra off-window endpoint is not automatically a licensed original leaf. Formula (2) can be evaluated by exact rational bounds, not floating point. For a complete implementation, intersect each outward-rounded interval with the original signed Gauss horizon. Every p in the cell is within a factor two of p0, so the inherited norm bound places the actual correct-colour index inside that horizon; clipping loses no witness. All remaining leaves then inherit the original deletion and short-order guards, without introducing off-window endpoints.

For the weighted-Gauss vectors, |a|p0 and |b|N/p0 are O(sqrt(kN)). Dividing a factor-size band into T cells of relative width O(1/T) therefore gives O(m/T+m/T²+1) indices per colour/cell. The straightforward all-colour, all-cell implementation has

    acquired row/cell count O(k*T),
    guaranteed upper interval budget O(k*m+k*T).

This is an EXECUTED algorithm with charged starts/tails, but its bound does not beat the old rate, and for polynomial T its preparation already exceeds soft k. It is not a proof that all adaptive cells have that mass. Reusing a row across adjacent cells may reduce preparation but does not discard the union of its integer windows unless a separate zero-safe identity is proved.

At a genuine critical centre a=b*N/p0² the linear term vanishes; the local width is O(m/T²+1). That looks useful, but covering every colour/cell by such a critical row would still acquire O(kT) representatives, and their existence/admissibility at that spacing is not supplied by Gauss reduction. One cannot assume the critical centres simultaneously align for all colours. A real improvement would need a proved jointly sparse distribution of critical representatives, rather than paying one new representative per colour and factor cell.

The supplied-interval Farey construction exploits precisely critical-point geometry once its factor interval is given. Applying it to an unknown true factor cell requires either paying all cells or a new scalar boundary predicate. Binary descent with the old all-colour interval query does not save the first full-band query; its initial cost is already the old bound. No unacquired interval-location oracle is assumed.

## 5. Primary knot/Hecke scope and exact remaining target

The inspected primary Farey sources are [Chesebro](https://arxiv.org/abs/1902.01968) and [Elzenaar–Martin–Schillewaert, GGD20(2026),215–256](https://ems.press/content/serial-article-files/52234). Their initialized specified-fan recurrences, and the parent's native index-k character, are valid tools for advancing acquired states. They do not supply a union-of-colours or factor-interval selection predicate. Their trace identities are not asserted to prove the new arithmetic coverage statements above. No complex modular/Hecke orbit formula is specialized to native finite-ring zeros without its finite boundary factors.

The concrete new test was coarse colour reuse (1), followed by interval localization (2). The first pays essentially all phase values even on a common slope. The second gives a legal variable-window algorithm whose guaranteed budget remains at the old power scale. This leaves a precise constructive target: acquire only soft k admitted colour/phase/critical representatives whose rounded physical windows cover an actual stationary pair for every prepared N and have total mass at most soft k²; or supply a paid scalar cell predicate that skips the rest without losing the actual pair. Neither the identical-lattice observation nor a specified-node knot trace provides that theorem.

No complete-query improvement, all-semiprime smaller-family theorem, or new factoring exponent is claimed. The prior colour/Gauss family and old evaluator remain available with all original recovery conditions.
