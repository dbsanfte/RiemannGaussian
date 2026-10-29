# Shared Pochhammer recurrence and finite Gauss multiplication on actual slices

26 October2026. Bounded paper probe, no tests, campaign, code or repository edits. Read AGENTS and the frozen colourcontraction/common-character report, retaining the SUPPLIED Gauss orientation. **Outcome:** one polynomial recurrence kernel really is acquired in soft k for the entire family. Its direct scalar readout remains soft k². The concrete finite multiplication candidate can acquire complete residue blocks, but the naively completed native clock envelope has length at least order N/G per retained cell; its safe factoring fallback is only the old soft N^(1/4) factorial algorithm. No whole-query improvement is proved. The specific next acquisition target is a sparse nonnegative decomposition into complete residue blocks WITHOUT filling those large gaps, or a direct partial-residue scalar algorithm.

## 1. A shared recurrence whose coefficients and polynomial start are actually acquired

Write B_G=beta^G,L=H/G, so q=B_G^L exactly. Only O(logk) values G occur. Let K=4k+1 and form ONCE

    P_K(Z)=product_(h=0..K-1)(1-Z*q^-h).             (1)

A product tree acquires its degree-K polynomial in soft k, without any 1-q^i inverse; its leading coefficient is a known monomial unit. This initialization is common to every colour, weight and G. Its exact cleared first-order recurrence is

    (1-Z*q^(1-K))*P_K(qZ)=(1-qZ)*P_K(Z).            (2)

For a common-character source coordinate n=(r,s), the normalized clock is t=h-F_j*r-C_j^clock*s. Up to a mathematical monomial unit, its K-factor contribution is

    P_K(B_G^r*q^[F_j*r+C_j^clock*s])
       =P_K(beta^[e_G*z]), z=P_j^-1*n.             (3)

The polynomial, recurrence coefficients and all two-generator descriptors are thus acquired; there is no unknown seed POLYNOMIAL. The missing scalar is the product of these evaluations over the actual punctured parallelograms.

For a residue rho mod L, set U_rho(d)=P_K(B_G^rho*q^d). Then(2) says

    (1-B_G^rho*q^(d+1-K))*U_rho(d+1)
      =(1-B_G^rho*q^(d+1))*U_rho(d).              (4)

It is invalid to divide its leading coefficient at a possible collision. The source clock order bound does not make that coefficient unit for arbitrary actual d: its beta exponent includes the large acquired source label. Cleared multiplication preserves the identity but does not select U_rho(d+1) when its coefficient vanishes. This is the exact singular-pivot issue for THIS initialized recurrence; no claim is made against other ways to evaluate it.

The older phase-index result explains why O(logk) bases is not O(logk) scalar starts for this recursion: integer q-translations preserve rho modulo L. Directly tabulating all rho in a large L group has L outputs, although the norm does not require such a table and no lower bound against implicit evaluation follows. Direct evaluation of(3) at every actual source point still has soft-k² starts. The existing monic geometric backend, or the degree-O(k) per-cell evaluator, completes this route in soft k². Initializing(1) is positive but is NOT counted as acquiring that scalar.

## 2. Finite multiplication formula: exact algebra, no analytic gamma values

The strongest simple sharing mechanism for q=B^L is the finite identity

    product_(rho=0..L-1) product_(v=a..b)(1-B^[rho+L*v])
       =product_(n=L*a..L*(b+1)-1)(1-B^n).         (5)

It is proved by reindexing integers. It is the finite product mechanism behind q-Gauss multiplication, not a root-of-unity specialization. It works over the current ring and for negative endpoints because B is supplied as a unit. If exponent0 occurs, omit that one factor BEFORE evaluation and split the integer interval; negative exponents are reversed using only monomial units. No numerical division by a vanishing factorial is allowed.

A primary reference explicitly using the complete-residue finite identity is Koepf–Rajkovic–Marinkovic, *On a connection between formulas about q-gamma functions*, JNMP23(2016),343–350, [publisher PDF](https://www.atlantis-press.com/article/125950603.pdf), printed p345, identity preceding its next asymptotic step; [DOI](https://doi.org/10.1080/14029251.2016.1199496). Its analytic gamma formulas assume real0<q<1 and are not imported into Z/N. Only the elementary finite polynomial identity is used here. This is classical identity credit, not a new algorithm theorem.

Reduce an actual common first coordinate r as r=rho+L*d, 0<=rho<L. A normalized leaf has exponent

    B_G^r-q^t = unit*(1-B_G^[rho+L*v]), v=d-t.

Substituting the exact t in common-character.md yields the useful simplification

    v=floor((e_G*z)/H)-h.                         (6)

Thus for each rho the ACTUAL v-support is the union of its original clock intervals. Formula(5) applies directly only to complete residue blocks with the SAME v interval for every rho. The shared character normal form alone does not establish that compatibility; it deliberately retains nonuniform finite domains. Signed ratios of completed factorials would need denominator-unit proofs and cannot discard collision factors.

## 3. Execute complete-residue envelope acquisition on native cells

One can really acquire a complete-residue OVERSUPERSET without expanding the source points. For a supplied cell define

    S_E=(A-1)*|E_u|+(B-1)*|E_w|.

The original signed coefficient box has source label extrema -S_E,S_E; its omitted origin does not affect the extrema. Equation(6) gives the public enclosing interval

    a=floor(-S_E/H)-(K-1), b=floor(S_E/H).          (7)

Complete every residue rho to this interval. All actual factors survive. New factors have exponent G*n, with n in the interval of(5); omit n=0 before evaluation. EVERY remaining added zero is a legitimate proper factor or nonzero short-annihilator event, independently of whether it reconstructs an original point. The endpoint magnitudes are polynomial in N, so those new labels have O(logN) bits and meet the actual inherited extractor interface. Source-cell/clock prefixes can use their corresponding extrema or exact interval unions; global-zero-only status is not substituted for gcd/nonunit recovery.

This is a genuine short-description scalar algorithm: take the extrema per G over the desired cells, use(5), and evaluate O(logk) ordinary B_G-factorial intervals with the inherited monic geometric engine. Its readout cost is governed by their INTEGER lengths, roughly S_E/G+L*K, not the bit length of S_E. Descriptor/extrema acquisition is soft k.

The native input gives a precise warning about these envelopes. All supplied dimensions satisfy A,B>=2 (the Gauss bounds give ell_i<R). At least one basis vector has nonzero b_i, because the basis has determinant+/-k. On a retained cell |a_i|<=a_span<=H, and its canonical phase is<H. Consequently

    |E_i|=|a_i+b_i*N+lambda_i|>=N-2H,
    S_E>=N-2H.                                  (8)

The completed interval in(5) therefore has length Omega(N/G) for EVERY retained cell. In particular a retained G=4 cell makes this naive factorial envelope length Omega(N), even though its source box had only O(k) points. This is an exact actual-input feature, not a fake alphabet or a lower bound on other slice algorithms. The ordinary square-root factorial implementation on that full interval is far above the target; claiming a soft-k readout because it is now "one factorial" would omit this length.

For the factoring objective one need not pay that enormous scalar value: its symmetric interval, with the literal zero removed, contains the positive integers1,...,ceil(sqrtN) on a G=4 cell. Since ord_P(B_G)<=P-1<sqrtN, that prefix already has a nonunit. The old constant-degree factorial engine evaluates/localizes it in soft N^(1/4), plus once-only T_ext=soft N^(31/192). This is the classical factor-size/order cover, not a new speedup; it remains slower than the retained soft k^(5/4) query. In other G groups the exact window(7) is still evaluated/charged by its actual length or can be treated by the same universally available old factorial fallback. No fast value for the original product is inferred from this factor branch.

## 4. A precise sufficient scalar target, not an asserted native decomposition

Formula(5) WOULD give a nearlinear complete algorithm if the ACTUAL supports, or a licensed nonzero-label overcover, could be acquired as S=soft O(k) complete-residue interval blocks across the O(logk) bases, with total INTEGER factorial mass T=soft O(k²). Grouping by interval lengths and applying the existing common-clock monic engine then costs

    soft O(S+sqrt(T))=soft O(k),                   (9)

with endpoint integer powering and one possible T_ext included. Splitting literal exponent0 is done before this evaluation; prefixes must retain valid source maps or new nonzero-label certificates. This is a sufficient acquisition theorem to seek, not a theorem about the present native support.

The complete-envelope algorithm(7) does NOT meet that criterion by(8). Nor does enumerating and separately completing every actual residue slice: its start count can remain soft k² and it fills additional gaps. The ordinary existing acquired completion remains soft k². No conclusion that a clever nonnegative block decomposition is impossible follows, and no lower bound on an implicit norm or circuit is asserted.

Any signed inclusion-exclusion decomposition needs more than the short additive generating function: numerical division by a block containing a local zero is illegal. A proof of unit denominators, or a cleared factor-or-recovery construction retaining every annihilator, is part of the desired scalar algorithm. This is a concrete extra requirement rather than a hypothetical generic obstruction.

## Outcome

The strongest executed candidates are (i) the genuinely shared degree-O(k) recurrence kernel with singular scalar transfer(4), and(ii) complete-residue finite Gauss multiplication with descriptors/extrema acquired without expanding cells. The first leaves soft-k² native evaluation starts; the second's naive native envelope has length Omega(N/G), with only the old N^(1/4) factoring fallback improving its direct scalar evaluation. Neither acquires the target complete scalar in soft k.

A substantive next step is an ACTUAL sparse complete-residue block/clock-union theorem satisfying(9), or a direct partial-residue norm algorithm that avoids expansion and collision division. The common-base identity by itself is fully paid and fully charged here; it is not another claimed solution based on a formal recurrence. The original sixth-exponent goal and its full bit/formal theorem remain open.
