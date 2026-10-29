# Independent audit of the cubic certificate and restricted-HH handoff

26 October 2026. Read cyclotomic-selector.md, cubic_gate.py, supplied Schoof PDF/text, and frozen axis-supplier/review-restricted-residue.md. **PASS: conditional factor-or-palette gate and stated soft-K composition are valid. No universal pass or new complete factoring rate is established.**

## Exact primary-source hypotheses

Schoof arXiv0801.3840 §3 defines sigma_i to FIX the additive q-th roots and act as zeta_r -> zeta_r^i on character roots. Thus sigma_N(z)=z, sigma_N(t)=t^N is exactly correct, not an unknown-prime Frobenius. Proposition 3.3(i) assumes: l prime not dividing N; an auxiliary PRIME q not dividing N; a character of order r>1 a power of l; and tau^(sigma_N-N) a GENERATOR of the actual r-root subgroup modulo N. It does not require a full primality-test pass, squarefree N, or a free assumption that this congruence holds.

Here l=r=3, q=7 and chi(3)=t meet the character assumptions. The initial gcd gates enforce gcd(N,21)=1. The rank-12 monic quotient represents Z[zeta_7,zeta_3]/N faithfully. Complex conjugation changes BOTH roots to inverses, and the exact identity tau*conj(tau)=7 licenses the implemented inverse. The negative sign in Schoof's tau definition is retained. Gamma is computed with the supplied N exponent, not with either unknown factor.

The gcd of N with ALL twelve coefficients of gamma-t^k certifies global equality exactly when it is N; a proper gcd is an actual factor; gcd one does not prove primality or license the identity. Primitive t and t² are distinct by a unit difference (3 is invertible). Therefore either accepted equality supplies the full source hypothesis. The code uses these same tests and reductions. Its structural controls are not evidence of native uniform pass frequency.

## 3-adic consequence and actual HH costs

The source conclusion is p²=N^(2lambda_p) in Z_3 for every prime p|N. Since N²=1 mod 3^t0, continuity of the 3-adic power gives p²=1 mod n=3^min(t0,e). For odd prime powers this implies p=±1 mod n, so the two PUBLIC unit residues cover the smaller factor, indeed both. This is stronger than an arbitrary auxiliary character of p modulo7 and does not invoke a modular square-root oracle.

For the cited HH interface, retain only these S<=2 supplied residues, but retain ALL source factor-size centre bins and ALL labelled matches. The ledger's exact giant/baby cost is soft(Sr+sqrt(N)/(nr)^(3/2)+S+1). With A0=ceil(cuberoot(K^4)), r=ceil(16A0/n), n>=ceil(cuberoot K), N<=K^6, one has Sr=O(K), nr>=16K^(4/3), lambda<=ceil(K/16), kappa<=K/8+3<K. The common beta^(n²) baby order is at least ord(beta^H), since n²|H; no crude division of its order or new preparation is assumed. The source polynomial-height bounds give O(log N)-bit starts/labels; total starts, babies and matching cost fit soft K.

The frozen restricted-residue review supplies the necessary exact recovery amendments: source orientation aQ+bP; all global matches are processed before deletion; zero a or b uses the direct division test; literal-zero exponent labels use exact quadratic/division recovery, not an annihilator decoder. After matched giants are removed, saturated evaluations localize a genuinely nonglobal difference and a proper gcd. Thus the HH conclusion is not merely a quoted balanced complexity exponent and needs no T_ext. The implementation correctly flags its own absence of HH execution/native preparation rather than claiming that the PALETTE result alone is a factor.

## Credit and limits

The growing Gauss-vector algorithm and primitive-order/primality certificate are already credited to the 22 October journal and Schoof. The new composition is a conditional public high-v3(N²-1) success branch with the sharper supplied-palette HH consumer. A failed global certificate returns DECLINE (or an actual coefficient factor); it cannot be converted into a factor residue. Odd 3-rough scalar/torus orders do not imply a high t0. The report states those limits and does not claim this branch is uniformly reached or that a growing extension eliminates its unknown complementary C_Q term.

Replay note: the existing `cubic_gate.py --self-test` was run read-only and returned PASS for its exact integer Gauss identity, three fixed prime Frobenius controls and its declared factor/decline controls. No additional semiprime instance or success campaign was run.
