# Native cyclotomic anti-invariant extraction vanishes for every tag

2026-10-16. A narrow, exact obstruction to the cyclotomic Frobenius selector investigated in this pass. It removes an unknown long index by projecting to the anti-invariant part, but the native row congruence makes that projection zero for ALL tags globally. This does not improve query acquisition or rule out other Frobenius methods.

## The proposed observable

Let R=Z/N for odd N, let m>=3 be an odd prime coprime to N, and work in either A=R[Z]/(Z^m-1) or A=R[Z]/Phi_m(Z). Write zeta for Z. The involution star sends zeta to zeta^(-1) and fixes R. For a nonzero tag j modulo m, sigma_j sends zeta to zeta^j; its inverse is sigma_k with jk=1 modulo m. These automorphisms commute with star.

Use the literal native row parameters

    a_j j²=N mod m,
    ell_j=m b_j-2a_j j,
    d=m².

Here b_j is the actual full-input centered lift. The global cancellation theorem below uses only ell_j=-2a_j j modulo m and permits any higher digits; the separate integer-index identity uses the actual native lift. Set u=1+zeta, f=u^N and

    T_j=u^(ell_j) (sigma_j u)^(a_j) sigma_k(f),
    q_cyc=u^d.

The element u is a unit in both algebras. In the full cyclic algebra, (1+zeta) sum_(r=0)^(m-1)(-zeta)^r=2, and 2 is a unit because N is odd. The same identity holds in its cyclotomic quotient. Thus negative ell_j causes no undefined inverse. All T_j and q_cyc are defined units.

There is an authentic own-tag identity. Suppose N=P Q with distinct odd primes, m not dividing P Q, and j=P mod m. Modulo P the Frobenius map gives sigma_j(u)=u^P and sigma_k(f)=u^Q. Hence

    T_j=u^(a_j P+Q+ell_j)=(u^d)^I,
    I=(a_j P+Q+ell_j)/m².

The integer I and its canonical interval bounds are inherited native row arithmetic. Under P<=Q, P>=m² and N<=m^6, the own index lies in[0,2m²+2). This transfers the row to a degree-m algebra; it does not acquire its long comparison. Since q_cyc is star-fixed, one might try to remove I by testing T_j-T_j^star. The following identity proves that this selector fails before any cost issue is considered.

## Exact global cancellation

More generally, let u be ANY unit of A satisfying u^star=zeta^(-c)u for a known integer c. Then

    (sigma_j u)^star=zeta^(-cj) sigma_j u,
    (sigma_k(u^N))^star=zeta^(-cNk) sigma_k(u^N).

Signed integer powers are legal. Multiplying the three phases gives

    T_j^star=zeta^(-c(ell_j+a_j j+Nk)) T_j.

But a_j j²=N modulo m implies a_j j=Nk modulo m, and therefore

    ell_j+a_j j+Nk=m b_j-a_j j+Nk=0 mod m.

Since zeta^m=1, this proves

    T_j^star=T_j in the WHOLE algebra over Z/N, for EVERY tag j.

No hidden factor, own-tag assumption, prime-period qualification or exceptional-set deletion appears in this calculation. Also (u^d)^star=zeta^(-cd)u^d=u^d because m divides d. For u=1+zeta the hypothesis holds with c=1. For the monomial u=zeta it holds with c=2; in that case T_j=zeta^(ell_j+a_j j+Nk)=1 globally for every tag.

Consequently the anti-invariant difference T_j-T_j^star, or its half when using the normalized projector, is identically zero modulo N for every j. All coordinate gcds of these outputs are saturated. Any R-linear functional applied afterward is also zero. Scalar-weighted sums and products of the T_j remain star-fixed, as do their inverses when defined, so applying the same projector after those operations still returns zero. This statement concerns those invariant-preserving combinations; arbitrary coefficient tests and non-invariant algebra weights are not excluded.

The same proof handles two-weight tangent rows. Put T=u^ell(sigma_j u)^a(sigma_k(u^N))^b. Its phase is c(ell+a j+bNk). The congruence a j²=bN modulo m together with ell=-2a j modulo m makes that phase zero. More generally ell=-a j-bNk modulo m suffices. Thus replacing the native rows by those larger tangent rows does not repair THIS anti-invariant selector.

## What the obstruction does and does not establish

The cancellation is real, but it forgets which candidate was correct: the own-tag equality implies star-invariance, and native low-digit arithmetic already imposes the same invariance on every wrong tag. The high lift and interval location never enter the projected answer. Even granting the entire T_j list for free would not make this projected list informative. This is a uniform failure of one specified observable, not an operation lower bound or a failure of the original coverage theorem.

The earlier reciprocal folded-Frobenius experiment used a different scalar Lucas/Laurent expression, recorded in the pinned probe script; its finite failures were not a theorem about these native sigma_j rows. Earlier quadratic phase savings also concern different products. This note makes only that scoped repository distinction, with no absolute priority claim. Frobenius, cyclotomic automorphisms and phase multiplication are standard tools.

The translated choice u=beta+zeta generally lacks the required self-reciprocity law and is not excluded. Its coefficient-level comparisons and fixed trace pairings remain open, as do non-invariant weights, direct residual norms, selected-output algorithms and other factor-producing observables. No construction of all T_j at soft O(m) is claimed; the proof grants them only to show the proposed projection would still fail. The current whole-query bound remains soft O(m^(3/2)), while the desired restriction-stable soft-O(m) query and complete Lean bit proof remain open.

The proof is classical and independently reviewed; no new Lean declaration, native edit, numerical example, broad build, commit or push is included. Source pins identify the actual native row/coverage definitions and the older probe. [Independent review](reviews/independent-review.md), [source pins](sources/source-pins.json), [journal entry](sources/journal-entry.md), [baseline](sources/pre-entry-baseline.json), [source map](source-map.json) and [manifest](manifest.json) record the exact evidence. Every earlier packet and journal entry is preserved.
