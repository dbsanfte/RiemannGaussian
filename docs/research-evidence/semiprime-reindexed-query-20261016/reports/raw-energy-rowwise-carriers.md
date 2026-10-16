# Raw modular energy survives every rowwise reindexing

2026-10-16. Actual-source extension of the high-digit carrier theorem. A parameterized raw-tag estimate makes arbitrary integer lift choices harmless, and obstructs geometric carriers for all long-scale rowwise starts without exponent wraparound. No arithmetic-operation lower bound or improved query algorithm is claimed.

## 1. Raw energy, including every tag and every congruence

Fix an odd prime m and n in {1,...,m-1}. For h=0,...,m-1 put N_h=n+mh. Use the literal first-current offsets delta_j(h), j=1,...,m-1. Their canonical slope and centered linear lift give

 delta_j(h)=delta_j(0)-m I_j h mod m^2,
 delta_j(h)=n(I_j^2-2I_j) mod m,                  (1)

where I_j=j^(-1) mod m. Define RAW modular energy

 Eraw(n,h)=#{(j_1,j_2,j_3,j_4):
       delta_(j_1)+delta_(j_2)=delta_(j_3)+delta_(j_4) mod m^2}.

This counts tags with multiplicity and only asks for congruence, not exact equality. Nevertheless

 sum_h Eraw(n,h)<=4m^3.                           (2)

Indeed a qualifying inverse-tag quadruple t_1,...,t_4 must satisfy the low quadratic equation sum_signed(t_i^2-2t_i)=0. There are at most 2(m-1)^3 such quadruples. If S=t_1+t_2-t_3-t_4 is nonzero, (1) allows at most one high digit h. If S=0, the quadratic equation fixes both the sum and sum of squares of the two pairs, hence their products and unordered multisets, since m is odd. These at most 2(m-1)^2 trivial ordered quadruples may contribute at every h. Thus the total is at most 2(m-1)^3+2m(m-1)^2<=4m^3. This repeats the earlier counting argument at the stronger RAW MODULAR level; no injectivity or deduplication premise is needed in (2).

For any parameter lambda>=1, at most 4m/lambda high digits per n, hence at most 4m^2/lambda coprime residues N modulo m^2, satisfy

 Eraw(N mod m^2)>lambda*m^2.                      (3)

The literal source is periodic in N modulo m^2, so this is a well-defined bad-residue set.

## 2. Every integer rowwise lift is controlled simultaneously

Choose arbitrary integers s_j, with unrestricted full-input dependence or private advice, and define

 epsilon_j=delta_j-m^2 s_j,
 V_s={distinct INTEGER epsilon_j}.

Their low image is unchanged: exactly N(Squares-1), including zero. Thus J_s=|V_s|>m/2. Every exact equal-sum quadruple of distinct-set elements, after choosing one representing tag per element, injects into a raw congruence quadruple. Consequently, on EVERY residue passing (3),

 E(V_s)<=Eraw<=lambda*m^2                         (4)

for ALL integer choices s at once, even arbitrarily large ones. Selection of representatives may depend on the advised shifts; the injection still holds into the same universal raw count.

The previous partition/Cauchy--Schwarz/Hölder argument therefore gives, for ANY cover of V_s by k integer arithmetic progressions of total listed length T,

 k^2 T >= J_s^4/(2E(V_s)) > m^2/(32lambda).       (5)

Holes, overlap and arbitrary starts/steps are allowed. There is no union over rowwise choices or progression descriptions. Also every containing finite integer carrier C has |C+C|>=m^2/(16lambda).

## 3. Long-scale rowwise geometric carriers in the global unit group

Put d=m^2 and Z_s={gamma^(-N-epsilon):epsilon in V_s}. Let D=ord(gamma) in the ambient group and W_s=max V_s-min V_s. If

 2W_s<D,                                         (6)

then equality of target pair products is equivalent to exact equality of the corresponding integer sums, so E_times(Z_s)=E(V_s) and distinct integer offsets remain distinct targets. Thus (5) applies verbatim to covers of Z_s by arbitrary ambient geometric progressions, including cyclic wraparound within the covering progressions, ratios outside the gamma subgroup and private advice. Any finite containing carrier C satisfies |CC|>=m^2/(16lambda), and any rank-r multiplicative progression box of listed size T satisfies 2^r T>=m^2/(16lambda).

Here the actual GLOBAL order is sufficient for canonical-long-scale rowwise starts. The pinned original qualified supply has distinct prime local orders

 R_P>P^.677, R_Q>Q^.677, P,Q=Theta(M^3), m=Theta(M).

By CRT the order of the actual projected gamma modulo N is EXACTLY D=R_P R_Q>c M^4.062. This uses the historical cross-order exclusion R_P!=R_Q and exact local orders, not merely the weaker native D>16m^4 promise. If the rowwise start range obeys

 max_j s_j-min_j s_j <= m^2 A(M),

then the literal delta span gives W_s<=4m^2+m^4 A(M). Any prescribed polylogarithmic A therefore satisfies (6) eventually, uniformly on the supply. This includes |s_j|<=m^2 polylog(M), after doubling A, and allows an arbitrary common origin. No order is supplied to an algorithm; its lower bound is only a proof-side qualification.

This LONG-scale geometric statement is global modulo N. The individual local orders are only of scale greater than M^2.031 and do NOT justify transferring such large lifted offsets fieldwise. A local-field version remains valid whenever its own order satisfies (6). The arbitrary-shift INTEGER statement (4)--(5) needs no order bound at all.

Unbounded advised starts really can defeat the GEOMETRIC conclusion. On this supply gcd(d,D)=1. Choose s_j=d^(-1)(N+delta_j) mod D; then every target gamma^(-N-delta_j+d s_j) is 1. This does not contradict (4): large wraparound destroys (6). Thus no arbitrary-unbounded-start geometric theorem is asserted. This advised construction is a scope counterexample, not an acquired public shortcut or an equivalent evaluation of the original intervals.

## 4. Parameterized loss on the same actual original supply

Use the same original order-qualified balanced prime-pair supply, its candidate envelope K_*, and the inherited selector-strip boxes. At fixed P,m the Q strip is covered by O(G_m+1) half-open boxes of width at most m^2, and sum_m(G_m+1)=O(K_*M). P is invertible modulo m^2, so each bad product residue in (3) accounts for at most one integer Q per box. Counting all O(M^3) possible integer P gives

 new bad-pair count = O(K_* M^6/lambda).           (7)

This applies simultaneously to every current candidate m, all advised rowwise starts and all covers satisfying the relevant hypotheses. It does not multiply a fixed-m count by a per-input menu size; the varying-selector estimate is explicitly used. The earlier losses are against this SAME original supply of size Omega(M^6/log^2 M), so union is legitimate.

Choose lambda/(K_* log^2 M) -> infinity. Then (7)=o(M^6/log^2 M), and union with the previous soft O(M^5.994) losses still leaves an actual family of size Omega(M^6/log^2 M). For example lambda=max(1,K_* log^4 M) suffices. If K_* is polylogarithmic, lambda is polylogarithmic, and (5) becomes

 k^2 T >= m^2/polylog(M) = soft Omega(m^2).        (8)

Thus polylogarithmically many progressions require softly quadratic total length for EVERY permitted rowwise reindexing on this majority family. The same nearly quadratic bound holds for productsets of containing carriers. This is a proof-side family statement, not the cost of checking energy or constructing a cover. The polynomial menu K_*=O(M^.020) can instead take lambda=M^.04, recovering a power-saving loss O(M^5.980) and exponent1.96 tradeoffs. A growing polynomial menu is not being called a nearlinear observation schedule.

## Scope

The new protection is uniform over rowwise starts, not just one literal lift. It uses raw modular energy and a quantified global no-wrap range, with an explicit counterexample when that range is removed. Shared computations, non-cover-based algorithms, high-productset carriers and factor-selective observables remain open. Altering starts changes row intervals; a geometric cover alone does not evaluate the original query or handle its missing factors. No new prime-distribution input, acquisition bound, all-input controller theorem, Lean declaration, build or numerical example is claimed.
