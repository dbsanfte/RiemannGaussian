# Two common character-period products: paid endpoint jets, evaluator still open

22 October 2026. This pass obtains an explicit paid coefficient interface for the two common products, not their evaluation at the J native unit points. The underlying formal log/exp method is classical and already used in the repository's `semiprime-block-query-20261016/reports/q-integration.md`; no new algorithmic priority or factoring-rate advance is claimed. No implementation, examples or repository changes.

## Exact common-product input

Let R=Z/N, N=PQ, and q be the original prepared scalar with both local orders >16m². Let R_eta={0} union the quadratic residues/nonsquares modulo the PUBLIC prime m, eta=±1. Put d=(m+1)/2 and

    A_eta(X)=product_(r in R_eta)(X-q^r),
    H_eta(X)=product_(n=0)^(K-1) product_(r in R_eta)(X-q^(r+mn)).

Both A polynomials are acquired from O(m) generated roots and monic product trees in soft O(m) work; their coefficients do not have the quadratic-Gauss formula for roots zeta_m^r. Here K~m, deg H=dK~m², J~m, and all native size descriptors are O(log N) bits. The already paid boundary reduction assigns explicit native unit points y_j to these two H polynomials.

## Constructive lemma: both endpoint jets in soft O(m+D)

Assume D<min(P,Q) and mD<min(ord_P(q),ord_Q(q)). Then the first D+1 coefficients at X=0 of BOTH H polynomials and the highest D+1 coefficients of BOTH are acquired in soft O(m+D) ring work and the usual soft O((m+D)log N) bit budget. In particular D=m satisfies the retained native promises. No degree-m² product is materialized.

First compute A_eta(0), a unit, and set Abar_eta(X)=A_eta(X)/A_eta(0). The exact constant of H is

    h0=A_eta(0)^K * q^[m*d*K*(K-1)/2].

The exponent is an explicit integer of O(log N) bits. Monic normalization of the scaled factors gives

    H_eta(X)/h0=product_(n<K) Abar_eta(q^(-mn) X).

Compute ell_eta(X)=log Abar_eta(X) mod X^(D+1) by truncated inverse, derivative and integration. Then, for 1≤k≤D,

    [X^k]log(H_eta/h0)
       =[X^k]ell_eta * (1-q^(-mKk))/(1-q^(-mk)).       (1)

Generate q^(-mk),q^(-mKk) successively from two initial powers. Every denominator in (1) is a unit because 0<mk<both local orders. Batch inversion costs soft O(D), including the scalar inversions. All formal divisions by k≤D are also units because P,Q>D. Exponentiating this acquired logarithmic jet and multiplying by h0 gives the desired bottom coefficients.

For the top coefficients, let Astar_eta(T)=T^d A_eta(1/T), whose constant coefficient is one. Then

    Hstar_eta(T)=T^(dK)H_eta(1/T)
               =product_(n<K) Astar_eta(q^(mn) T).

Use precisely the same construction with geometric multiplier (1-q^(mKk))/(1-q^(mk)). Its first D+1 coefficients are the leading coefficients of H. K=0 gives H=1 separately.

All identities are truncated FORMAL identities. Their log/exp operations use only unit constant-term series inversion and integer divisions through D; they need no analytic convergence, field FFT roots, or hidden prime. Standard Newton iteration gives soft-linear truncated multiplication/log/exp over this ring once those denominators are units. Integer-packed multiplication supplies the modular bit implementation. Table construction, initial powers, h0, input/output, batch inverses and both signs are included. This is not a scalar sqrt(K) routine applied to a D-dimensional jet ring with its arithmetic left uncharged.

The jet may be tested by scalar gcds of its explicit coefficients, if desired, but there is no theorem forcing a proper gcd or a useful native collision from these endpoint coefficients. They are not presented as a new universally sufficient detector.

## Why this has not supplied H mod F_J

Let F_J(X)=product_j(X-y_j), with the actual native unit points. A jet modulo X^(D+1) is a nilpotent quotient. R[X]/F_J is the native distinct-root algebra. The y_j are not nilpotent, and substituting them into a truncated formal identity is not an exact evaluation rule. An acquired endpoint jet cannot be substituted for H mod F_J. Composing a short explicit polynomial modulo F_J is paid, but constructing an explicit short polynomial equal to H in that quotient is exactly the remaining acquisition step.

Likewise, the valid doubling identity H_(2K)(X)=unit*H_K(X)H_K(q^(-mK)X) does not allow shifting only H_K mod F_J: the discarded multiple of F_J becomes a generally nonzero multiple of F_J(q^(-mK)X). No q-scaling endomorphism of the fixed quotient is assumed. Retaining all needed moving moduli or coefficients would have to be charged.

The ordinary blocked algorithm forms a degree-dB block and evaluates it at J*(K/B) scaled points, with paid soft O(dB+JK/B+J) cost. At d,K,J~m its optimum is m^(3/2). The endpoint-jet lemma does not change that count. A faster product-grid AGGREGATE, implicit modular reduction or source-preserving short contraction is still needed.

## Primary algorithm contracts inspected

* Brent–Kung, *Fast Algorithms for Manipulating Formal Power Series*, JACM 25 (1978): https://maths-people.anu.edu.au/~brent/pd/rpb045.pdf . Supplies the classical fast formal-series context. The finite composite-ring specialization above is stated and justified directly by its unit denominators; no characteristic-zero result is silently applied at a nonunit integer.
* Bostan–Yurkevich, *Fast Computation of the N-th Term of a q-Holonomic Sequence and Applications*, arXiv:2012.08656v1, Theorem 5: https://arxiv.org/pdf/2012.08656 . For one fixed target, the order-one product has coefficient degree d~m and horizon K~m, so, when K>d as required by that theorem, the degree-sensitive sqrt(Kd) clock is soft m. For K≤d, direct monic multipoint evaluation of A at its K scaled arguments is already soft O(d+K). Its several-index version does not assert simultaneous J varying target parameters at that price. No new restriction from this source is claimed.
* Neiger–Salvy–Schost–Villard, *Faster modular composition using two relation matrices*, arXiv:2601.17422v1, Theorem 1.1 and section 6.1: https://arxiv.org/html/2601.17422v1 . Bivariate coefficients and transposed input vectors remain supplied data; neither theorem acquires the implicit H remainder from its block-product descriptor. This fresh-source contract was already audited in the preceding parameter-batch pass, so it is not counted as new literature progress.
* Kedlaya–Umans, August 31, 2008 author preprint, sections 1.2–1.3: https://drops.dagstuhl.de/storage/16dagstuhl-seminar-proceedings/dsp-vol08381/DagSemProc.08381.5/DagSemProc.08381.5.pdf . Its nonalgebraic route DOES handle composite coefficient rings. The explicit coefficient/evaluation-volume requirement, rather than unknown factors alone, remains the issue here.

Outcome: two masked endpoint jets are genuinely acquired at the target soft-m budget using existing formal-series machinery. No new conversion from those jets to the native remainder, no faster unit-point evaluator, and no improved all-input factoring rate was obtained.
