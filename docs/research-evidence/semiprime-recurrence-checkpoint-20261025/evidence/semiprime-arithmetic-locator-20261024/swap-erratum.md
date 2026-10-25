# Erratum: the complete scalar catalogue has shared global hit indices

24 October 2026. This corrects one substantive scope sentence in the frozen /tmp/semiprime-scalar-terminal-20261024/terminal-contract.md, SHA256 `202706e6213e9ba5e9957c7e7d712a46e2a2dbd555329f4bf6298c2a017026c8`. That file is PRESERVED unchanged. Its sentence “(1) does NOT promise an index s for which f_s=0 globally” is false for the ACTUAL complete swap-closed catalogue. A generic scalar-product-zero identity alone does not imply a shared index; the catalogue's additional arithmetic symmetry does.

Input is scalar-catalogue.md SHA256 `9ded79850c2f200069a7da67502d0de579d1df0457cb06c865fb3d39c9654058`, exact-source review `ce4d15b225d546c8008efaf5e6bdb2d2c0923b2b99d8603d3e1e24273efc6c27`, under /tmp/semiprime-paired-weighted-query-20261024. Retain its actual scalar setup, fixed factored k=2*3^e, H=k², h=2M+1<16H, full signed catalogue and public zero-row deletion. Both beta and q=beta^H have local orders>16H, beta orders are odd, P,Q>16H+1, and every retained tested exponent E-Hi is a nonzero polylog-bit integer. Its licensed short-annihilator consumer and finite fallback remain unchanged.

## 1. Swap produces the SAME index at the other prime

Take the surviving virtual Gauss witness(a,b,lambda) at P, with

    HI=aP+bQ+lambda, |I|<4sqrt(kN)/H+1<M,
    E=a+bN+lambda,
    E-HI=(P-1)(bQ-a).                           (1)

The COMPLETE catalogue also contains(b,a,lambda), including the swapped axes, because ab and the root equation lambda²=4abN modH are unchanged. Its exponent is E'=b+aN+lambda. At the OTHER prime Q,

    E'-HI=(Q-1)(aP-b).                          (2)

Thus beta^E=q^I modP and beta^E'=q^I modQ at exactly the same integer I. Equation(2)'s right side is nonzero: if a=0 then b!=0; otherwise |aP|>=P>k>=|b|. Hence public zero-row deletion cannot remove the swapped row. If E'=Hi0 in the searched interval, local equality at Q and ord_Q(q)>h would force i0=I, contradicting(2). The original witness's survival is already proved by the same argument using(1).

For T=q^M beta^E, T'=q^M beta^E', s=M+I and F(X)=prod_retained(X-T_j), this proves

    F(q^s)=0 modN                               (3)

at a single global index. It does NOT assert that one original scalar leaf vanishes globally: the two local factors can be different rows. The old one-index consumer remains valid and must localize to a proper gcd or an actual saturated nonzero-annihilator leaf.

Opposite signs give a second DISTINCT global index. Put lambda'=(-lambda modH) and kappa=(lambda+lambda')/H in{0,1}. The opposite and swapped-opposite rows have index I'=kappa-I, also inside the same window by its extra unit of slack. They survive deletion because their Fermat integers are the negatives of(1),(2). If kappa=1 integer indices cannot coincide; if kappa=0 coincidence would mean I=0 and aP+bQ=0, forcing a=b=0 since |a|,|b|<=k<P,Q, impossible. Thus there are at least two globally zero f_s. The weighted clock T_clock consequently has T_clock^(h-1)=0, as previously concluded, now with global-index rather than separate-prime witnesses. Existence of unit-coordinate kernel vectors e_s is guaranteed, but their labels are NOT acquired.

## 2. An actual soft-k diagonal preprocessing

Root supplied the following cleaner diagonal count. For a=b!=0, |a|<sqrtk. Write |a|=uv, u supported on primes2,3 and gcd(v,6)=1. The catalogue's proven ramified-root bound gives r(a²)<=32u. Therefore

    sum_(|a|<sqrtk) r(a²)
       =O(sqrtk * #{2,3-smooth u<=sqrtk})
       =O(sqrtk log²k).

All diagonal rows are thus an acquired J_diag=soft sqrtk subset. Query their RETAINED rows first with the existing exact monic evaluator at the same h. Its cost is soft(J_diag+sqrt(J_diag*h))=soft k; localization and the nonzero global-annihilator consumer are also within soft k. No extra order or residue decoder is needed.

A nonunit diagonal aggregate gives a factor by that complete consumer. Otherwise its aggregate is a GLOBAL unit, so delete all diagonals. Coverage (3) survives: a diagonal virtual witness would have made this aggregate nonunit. Hence on the continuing branch there is a NONDEGENERATE swapped witness pair a!=b, still with a common global q-index. This is paid pruning, not a reduction of the remaining asymptotic row count.

## 3. Explicit paired quadratics and mixed roots

First keep only COMPLETE surviving swap pairs: if public zero-row deletion removed one member, discard its unpaired partner too. This is a soft-k metadata operation and is coverage safe by Section1: the actual witness and its swap both survive. It prevents reintroducing a deleted integer-zero leaf. For every resulting nondegenerate pair acquire A=T_(a,b,lambda), B=T_(b,a,lambda) and

    Q_pair(X)=(X-A)(X-B)=X²-(A+B)X+AB.

The whole list and coefficients cost soft k. Scan gcd(A-B,N). A proper gcd factors immediately. If it is N, the known exponent difference

    E-E'=(a-b)(1-N)

is NONZERO and polylog-bit, and beta^(E-E')=1 globally. The licensed short extractor factors in soft k, once. Thus a continuing trace actually certifies all these A-B differences as global units; this is not a silently assumed discriminant promise.

For the witness pair from Section2, z=q^s satisfies z=A modP and z=B modQ. It is a GLOBAL root of Q_pair assembled from DIFFERENT known roots. Since A-B is a unit,

    gcd(z-A,N)=P,
    w=(2z-A-B)/(A-B) satisfies w=+1 modP,-1 modQ.

Thus z would give a nontrivial square root of1 and a proper factor. The acquired discriminant is just(A-B)²; its known trivial roots do NOT select z. A routine returning merely some root of Q_pair could return A or B and give no factor.

No cheap gcd/norm identity tested here locates this mixed root. The finite q-grid polynomial is still implicit and long. A known paired quadratic's full interval query has a paid soft sqrt(h) completion, and identifying one nonunit pair would suffice to finish inside soft k, but locating that pair among the soft-k list is not provided by its coefficients. The generic aggregate localization still costs soft k^(5/4). Swapping and signs give a stronger witness promise, not an acquired index or recursive 3-adic choice.

The corrected theorem and the diagonal/pair guards are constructive arithmetic facts. They do not assert a new full-query exponent, a generic recurrence obstruction or the sixth-rate/Lean goal. All frozen sources and shared documents were left unchanged; only this erratum was written.
