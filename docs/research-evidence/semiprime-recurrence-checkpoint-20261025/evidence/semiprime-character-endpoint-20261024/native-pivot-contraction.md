# Native mixed pivots: scale covariance, pair cancellation, and the terminal test

24 October 2026. Scratch only; no repository edits, numerical examples or backend work. This tests the ACTUAL native roots in the q-hook-normalized Sylvester chain. It derives the first nontrivial native mixed-pivot cancellation and an exact residual phase for reciprocal tags, then executes a safe first-two-pivot branch and the paid terminal fallback. It obtains no soft-m whole-family query.

## Prior work and input scope

Read the latest AGENTS, the current Gauss-period/tensor reports, native-row-pairing.md, native-polynomial-structure.md, mobius-canonical-carry.md, low-phase-pairing.md and parameter-charlier.md. In particular marked pair interpolation, the four original-boundary-leaf normalization, native q-chain startup and varying reciprocal centers are ALREADY recorded; they are not renamed as new algorithms here. The Charlier parameter-N central cancellation concerns different exponent-polynomial lists with an unresolved coverage theorem and does not supply these mixed pivot values.

Exact read pins:

| Report | SHA-256 |
|---|---|
| /tmp/semiprime-tensor-norm-20261024/sylvester-elimination.md | f3375df02a067a43230d1f4accddc476bbbe020a64c9145b90757ba5404720c2 |
| /tmp/semiprime-gauss-period-20261024/period-constructor.md | c7b338819761dddd0838f81a21ad65c7e9d830f48bcc9da4b4c4c99b6d2e14b5 |
| /tmp/semiprime-gauss-period-20261024/period-query-attempt.md | b876429f4ca01b324e5dec74d62a27706664942c023a5eb97487252df6152cb9 |
| /tmp/semiprime-native-shared-acquisition-20261023/native-polynomial-structure.md | f9af812ff9a027324120aff094408306dd9f47a3b9e32e4169132e60da2cd066 |
| /tmp/semiprime-original-pattern-20261023/mobius-canonical-carry.md | 505862e94056848ff2f13cd213286a629848a8fe37e19ad9ba984ddace09e67a |
| /tmp/semiprime-charlier-coverage-20261023/parameter-charlier.md | 5f59aa34e578123ce8acaadbcfbfbe0a3d4ea78baf188aeb9a0cc124541e25b7 |
| preserved semiprime-block-query-20261016/reports/low-phase-pairing.md | 6fa93147cba648db524c5e95258a134a635b2d0c4876f16c83de9359619f0ab6 |

Retain original beta, H=m², q=beta^H, native a_j,b_j,ell_j,delta_j=a_j+ell_j, and Y_j=beta^(N+delta_j). The prepared local beta/q orders exceed16H, and the global beta order exceeds256H². All offsets lie in [-3H,H].

For the exact antipodal calculation use all raw tags, n=m-1, with multiplicity. Restoring a raw copy deleted by public offset deduplication preserves zero support, but need not preserve the numeric resultant. The all-pivot scale identity below holds equally for a supplied deduplicated F. No inverse of raw target differences is used, and no equality of the raw and deduplicated scalar norms is claimed.

## 1. Common beta^N scaling through EVERY mixed principal pivot

Set gamma=beta^N, y_j=beta^delta_j and F0(X)=product_j(X-y_j). Acquire all y_j and F0 in soft m. Exactly,

    F(X)=gamma^n F0(X/gamma),
    f_(n-r)=gamma^r f0_(n-r).

In the balanced Sylvester trial, B_Z(X)=Z^n F(X/Z) has coefficients f_(n-r)Z^r. Hence the whole matrix, not just its first coefficient, satisfies B_Z(F)=B_(gamma Z)(F0). For each principal subresultant coefficient,

    p_k(Z;F)=p_k(gamma Z;F0).

Using the proven public degree bound k², reversal gives

    phat_k(Y;F)=gamma^(k²) phat_k(Y/gamma;F0).        (1)

This is exact over R=Z/N, including hits and zero divisors. The multiplier is a known unit and its norm/character may be handled lawfully. All q-hook constants p_k(0) are unchanged. Thus the large N contribution is removed from every pivot by ONE acquired shift of the outer grid and known unit factors, not n separate large input lists.

What remains is the actual F0 with roots beta^delta_j. Its coefficients are already cheap input; (1) does not supply phat_k at a unit outer argument, its zero support there, or the additive mixed Schur updates. No short formal prefix is evaluated by dropping its tail.

## 2. Native opposite pairs: the actual center term and its separation

For j'=m-j, a_j'=a_j=a and the centered carry gives

    ell_j+ell_j'=H*tau_a, tau_a in {-2,-1,0}.

Define acquired normalized pair trace and product

    s_a=y_j+y_j',
    k_a=y_j*y_j'=beta^(2a)*q^tau_a.                 (2)

There is exactly one antipodal pair per represented a because a_j=N/j² modulo m is two-to-one. All pair data cost soft m. Grouping tau_a into three values is valid, but does not make the centers equal: for distinct a,b,

    (2a+H*tau_a)-(2b+H*tau_b)

is nonzero modulo m and has absolute value <3H. The local beta order bound therefore makes k_a-k_b a UNIT. Removing the known q carries leaves beta^(2a), still unit-separated. Thus this particular opposite-tag family has Theta(m) distinct centers, not one common reciprocal center or a constant-size list of them. This is a scoped actual-source statement, already anticipated by the older pair reports, not a prohibition on other representations.

Even allowing a bounded public q-shift |r|<=4H cannot identify two normalized centers globally: 2(a-b)-Hr is nonzero modulo m, while its magnitude is <5H²<ord_N(beta). Therefore beta^(2a)=beta^(2b)q^r is impossible in that bounded global range. Accidental local order relations outside this exact test are not excluded.

## 3. First nontrivial native mixed pivot, acquired without dropping cross terms

Write A_n(X)=X^n+A1 X^(n-1)+A2 X^(n-2)+A3 X^(n-3)+..., and F0 similarly with coefficients b1,b2,b3. Put S_r=sum_j y_j^r. Newton identities give

    b1=-S1, b2=(S1²-S2)/2,
    b3=-(S1³-3S1*S2+2S3)/6.

All displayed divisions are by certified small scalar units. The normalized quartic numerator from the actual second Sylvester pivot is

    P20(Y)=(A2²-A1*A3)Y^4
      +b1*(A3-A1*A2)Y^3
      +(b2*A1²+b1²*A2-2A2*b2)Y²
      +A1*(b3-b1*b2)Y+(b2²-b1*b3).

The first mixed cancellations simplify it to

    [Y²]P20=(A1²*S1²-(A1²-2A2)*S2)/2,
    [Y] P20=A1*(S1³-S3)/3,
    [1] P20=(S1^4+3S2²-4S1*S3)/12.                 (3)

For the actual opposite pairs,

    S1=sum_a s_a,
    S2=sum_a(s_a²-2k_a),
    S3=sum_a(s_a³-3k_a*s_a).                        (4)

Thus (3) isolates a genuinely cheap center contribution (A1²-2A2)*sum_a k_a in its Y² coefficient. The center sum can be acquired by three degree-<m indicator polynomials for the represented a values, evaluated at beta² and multiplied by q^tau. More simply all (4) are acquired by a linear scan of the already acquired pair data. This costs soft m for the ENTIRE row family, not one degree-m algebra operation per tag.

The cancellation is real but incomplete: sum s_a² and sum k_a*s_a remain, alongside S1. They are acquired for this first pivot; replacing them by center data alone changes P20. Equations (3),(4) are not a scalar terminal rule for the later square-Schur pivots. Their leading coefficient remains the q-hook unit, and the original quartic is gamma^4 P20(Y/gamma) by (1).

## 4. Reciprocal tags: exact natural normalization still leaves a non-q phase

This tests a different arithmetic relation after the common-center attempt fails. Let j*=[N/j]_m, A=a_j, B=a_(j*), rho=(AB-1)/m. Then AB=1 modulo m. Keep the exact older carries

    c_j=m b_j-a_j j,
    eta=(B c_j-c_j*)/m,
    zeta=(B j*-j)/m,
    d_j=(c_j+j*)/m, d_j*=(c_j*+j)/m,
    nu=(N-j j*)/m.

They are public integers. The corrected native carry identities give j*d_j+nu=0 modulo m and j* d_j*+nu=0 modulo m. Since B/j=1/j* modulo m,

    eta+zeta=B*d_j-d_j*=0 modulo m.

Using delta_j=c_j-Aj+A, an EXACT integer calculation gives

    B*(delta_j+1)-(delta_j*+1)=m*kappa_j,
    kappa_j=eta+zeta+rho*(1-j),
    kappa_j=rho*(1-j) modulo m.                    (5)

For A!=1 and j!=1, 1<=rho<=m-2, so the last residue is NONZERO. Thus even the natural root normalization tilde_y_j=beta^(delta_j+1) satisfies only

    tilde_y_j^B=tilde_y_j* * beta^(m*kappa_j),        (6)

with a residual phase that is not a literal integer q-shift. The exceptions A=1 and j=1 are retained separately; no universal nonzero claim is made there.

The normalized root tilde_y_j=beta^(delta_j+1) is obtained from the FULL target by removing the common beta^(N-1), not by pretending the original beta^N scale is unchanged under a variable power. In full-target notation (6) reads

    Y_j^B/Y_j*=beta^[(N-1)(B-1)+m*kappa_j].

Both the changed common scale and the residual phase must therefore be retained. Adding any individual q-gauge H*r_j to delta_j changes kappa_j only by m*(B*r_j-r_j*), preserving its nonzero residue modulo m. This rules out the tested q-gauge repair, not all possible inverse-pair algorithms. A finer beta^m clock can represent the phase, but even a simple full interval overcover then has horizon of order m*L rather than L; its ordinary degree-J blocking cost is soft(J+sqrt(J*m*L)), or soft m², before addressing the variable powers. No cheaper transport is supplied by changing the clock name.

This remains a non-q phase in the bounded GLOBAL query range: the offset envelope gives |m*kappa_j|<4mH; for |r|<=4H the exponent m*kappa_j-Hr is nonzero modulo H and has magnitude <5H²<ord_N(beta). Therefore beta^(m*kappa_j) is not q^r modulo N in that range. The proof uses the actual native carries and original global order, not an unknown local order or a surrogate family. Without the +1 normalization, the obstruction already appears modulo m as 1-B; (5) shows exactly what survives after removing that first residue.

Accordingly reciprocal labels do not permute these normalized endpoint roots through known bounded q-shifts. The variable power B and residual phase must remain in any cofactor update. Acquiring their transformed individual roots is still soft m, but computing a new target polynomial from those roots would merely supply another cheap input list; it does not pay its long interaction with the q-grid. The older Mobius map j->j/(j-1) has its own carried variable-power/non-q-phase identity and does not remove (5).

## 5. Attempted terminal closure and the actual paid completion

After the scoped common-center and inverse-tag failures, test the remaining pair-moment alternative rather than conclude from them alone. Each pair obeys the initialized Dickson recurrence

    D_0(s,k)=2, D_1(s,k)=s,
    D_(r+2)=s*D_(r+1)-k*D_r,
    S_r=sum_a D_r(s_a,k_a).

Its starts and first mixed moments (4) are acquired. Directly extending r to M costs O(mM) scalar operations. Ordinary Newton/power-series arithmetic on the already acquired F0 gives its first O(m) root power sums in soft m; that is the known cheap coefficient input, not a new endpoint operation. The later Sylvester pivots require mixed sums/products in the marked pairs, not just a fixed constant number of these starts.

An interpolant in the unit-separated centers can encode all s_a at soft-m cost, but this is the marked coefficient algebra already executed in native-polynomial-structure.md. It retains rank Theta(m), and its weighted long-product norm is still unacquired at soft m. This report does not count that older interpolation as new, assume low interpolant degree, or treat rank-m algebra operations as scalar. Doubling the Dickson index changes D_r to D_(2r) but does not shorten the original seed horizon; adding the unit plus-companion is the previously recorded odd-order square fold and leaves the same interaction cost.

A COMPLETE currently acquired algorithm is therefore:

1. Acquire F0, all pair data, (3),(4), first linear/quartic pivot polynomials and their q-hook normalizers in soft m. No hidden field, root extraction or target inverse is used.
2. Apply the first-two-pivot support cleanup in character-resultant.md: evaluate each acquired linear/quartic at the t~m outer nodes, gcd every value, return proper factors; absent those, global zero nodes are public. Unit leading coefficients bound their total by 1+4. Acquire the ORIGINAL inner slice at each such node by n~m monic MPE, and recover from any original nonunit leaf. Unit slices may be recorded and removed by monic exact outer division. Every auxiliary zero is handled at the original object rather than sent directly to a beta decoder. Total cost remains soft m.
3. If no factor/witness finishes, the remaining mixed pivot support is NOT acquired by (3)-(6). Reacquire the whole original scalar norm by its existing blocked constructor, cost soft(J+sqrt(JL)). This avoids any division by an unknown removed product or an assumption that a holed outer grid is still geometric. Restrictions retain original labels and use the same paid constructor.

For a proper original gcd return the verified factor. A saturated ORIGINAL bounded leaf beta^(N+delta_j)=q^i uses the retained factor-sum decoder; an auxiliary pivot zero never does. No all-input hit theorem for the first two pivot supports is asserted. These extra operations provide an initialized adaptive branch, not a covered replacement for the terminal norm.

## Cost and outcome

| Operation | Paid work | What it acquires |
|---|---:|---|
| Common-scale normalization, all native roots/F0 | soft m | actual short coefficient input |
| Every q-hook boundary scalar | soft m | formal unit constants, not endpoint values |
| Opposite/reciprocal integer carries and pair data | soft m | exact centers, traces and residual phases |
| First nontrivial mixed native quartic (3) | soft m | all coefficients; center-only closure fails |
| First two auxiliary supports and <=5 original slices | soft m | safe adaptive factors/removed unit slices |
| Pair-moment iteration to M by direct recurrence | O(mM) | full demanded list, no free terminal contraction |
| Current complete restricted norm and recovery | soft(J+sqrt(JL)) | original covered product/witness |

The native common scale extends through ALL normalized pivots, and the first mixed coefficient cancellation is actually acquired. Opposite centers remain a linear-sized unit-separated family; reciprocal tags retain the explicit non-q phase (5), even after the natural root normalization. The tested alternative pair-moment terminal recurrence retains its marked rank/cost. None supplies the missing whole-family endpoint rule. The complete bound stays soft m^(3/2), with no all-input sixth-rate claim and no generic scalar-algorithm lower bound.
