# Executed twisted free-fermion TQ closure for the retained correction

26 October 2026. Research report, archived after review. **No improved prefix rate is proved.** This pass executes a Baxter closure with both the Bethe polynomial and an off-resonant vacuum polynomial acquired in softly O(L), retains the scalar amplitude, and identifies its remaining query exactly. It does not re-use a short determinant descriptor as an evaluated scalar.

Read the current fusion/fermionic review, scalar/fastprefix packet interfaces, and the earlier `terminal-toda.md` and `colour-fusion.md`. The Hankel mixed-minor/Toda boundary calculation and antipodal Graeffe contraction are prior work, not new progress here.

## 1. Exact native input and a paid TQ seed

Let d=2L, and pass the **recentered** acquired roots v_j=x_j/eta and eta/x_j for representatives of the opposite pairs x_j,q/x_j. Thus

    S(z)=∏_(j=1)^d(z−v_j),
    K(z)=c z^(−L) S(z),
    P_m=∏_(i=1)^m K(t_i),  t_i=eta^(2i+1), q=eta².

The scalar c is a known unit. S, its roots, and original labels are acquired in softly O(L). In particular this uses the actual K roots, not unrecentered original scalar rows or unknown polynomial factorization. The unit normalization is

    ∏_(i=1)^m S(t_i)=c^(−m) eta^[L m(m+2)] P_m.         (1)

Take the quantum spectral deformation t=q, square root h=eta, and diagonal twist kappa=eta. Define zeta=kappa*h^d=eta^(d+1). For the acquired coefficients S(z)=Σ s_j z^j, acquire

    F(z)=Σ_(j=0)^d s_j/(q^j−zeta) * z^j.               (2)

This is an actual coefficient list, not an unknown solution of a functional equation. It satisfies exactly

    F(qz)−zeta F(z)=S(z).                              (3)

Every coefficient denominator is eta^(d+1)*(eta^(2j−d−1)−1). Its nonzero odd exponent has absolute value at most d+1. For the native asymptotic range d+1 below both eta orders, these are certified units. The original order margins imply this range for L=soft(k); exceptional finite scales use the inherited fallback. Powers and all inverses can be batch-acquired in softly O(L) ring operations and softly O(L log N) bit operations. The leading coefficient of F is also a unit. No native target value has been divided.

This is a positive paid seed for the **twisted vacuum-polynomial problem**: a degree-d inhomogeneity polynomial whose Bethe polynomial is exactly the acquired native S. It does not claim that roots of F or a factored spin-chain diagram have been acquired.

## 2. Source formula, scalar amplitudes and the full occupied sector

Primary source inspected: Zhao–Yang–Zhang, *Determinant representation of correlation functions for the U_q(gl(1|1)) free fermion model*, arXiv:hep-th/0506070v4, equations (II.17), (II.23), (II.24): https://arxiv.org/pdf/hep-th/0506070 . Their eigenvalue expression has vacuum factor 1−A(u), with Bethe roots satisfying A(v)=1. A constant diagonal twist replaces A by kappa A; it follows directly by replacing D−A by D−kappa A in the same displayed eigenvalue calculation. No root-of-unity or asymptotic limit is used.

Algebraize their weights using z=exp(2u), inhomogeneities y_j, q=h². With F(z)=const*∏(z−y_j), the vacuum ratio is

    kappa A(z)=zeta F(z)/F(qz).

For a Bethe polynomial Q(z)=∏_(r=1)^b(z−w_r), their common scattering product becomes h^b Q(z/q)/Q(z). The elementary equality c(u,v)/a(u,v)=1/a(v,u) makes both eigenvalue terms share it. Thus the rational TQ identity is

    Lambda(z) Q(z)
       = h^b [F(qz)−zeta F(z)] Q(z/q)/F(qz).          (4)

It is enough to establish this generically and then clear denominators. The physical finite-ring chain, its Bethe vectors, and simplicity of its roots are not needed for the following polynomial specialization.

Now take the completely occupied polynomial Q=S, b=d, with F acquired by (2). Substituting (3) into (4) cancels S symbolically and gives the **retained eigenvalue amplitude**

    Lambda_full(z)=eta^d S(z/q)/F(qz),
    T_full(z):=F(qz)Lambda_full(z)=eta^d S(z/q).       (5)

The second equation is the finite, denominator-cleared identity. It holds even when S(z) or F(qz) is zero or nonunit. It also bypasses possible repeated native roots: no regular Bethe basis over R is asserted. A physical eigenvector realization would require additional work and is not part of the acquired scalar algorithm.

This executes the closure rather than leaving unspecified Bethe roots: Q=S and F are both known in softly O(L). However, the full occupied transfer has become a shifted **native polynomial**, not a cheap known unit. Its long scalar amplitude still contains the target zeros.

## 3. Execute the geometric-string product and every pivot branch

Put z_i=q*t_i, so z_(i+1)=q*z_i. Formally multiplying (4) gives a telescoping Q ratio. After clearing it, the exact identity is

    [∏_(i=1)^m F(q z_i)] [∏_(i=1)^m Lambda(z_i)] Q(z_m)
      = eta^(b m) [∏_(i=1)^m S(z_i)] Q(z_1/q).       (6)

Here the products with Lambda are shorthand for the rational identity; a finite implementation uses the polynomially cleared transfers from the outset. For Q=S and b=d, (5) says directly

    ∏_(i=1)^m T_full(z_i)
       = eta^(dm) ∏_(i=1)^m S(t_i).                  (7)

Combining (1),(7) provides every unit normalization and preserves exactly the desired zero/nonunit predicate. Formula (6)'s endpoint telescoping is therefore not an extra computation of its interior amplitude: with the full occupied seed, (7) returns the original prefix after a one-step shift.

There are three distinct pivot issues.

* Coefficient pivots in (2) are all certified units as proved above; no branch is omitted there.
* Native endpoint pivots Q(z_m), Q(z_1/q) in a numerical use of (6) are **not** certified units. Their evaluations cost softly O(L) in total. A proper gcd gives a factor. A globally zero value at an endpoint in the original searched range is handled by the retained original-row localization/nonzero-annihilator consumer. An endpoint outside that range cannot simply be assigned the original consumer; keep (6) cleared or perform an explicitly extended-label recovery with its own deletion check. The division-free equation (7) avoids this issue altogether.
* Inhomogeneity pivots F(q z_i) are not native linear differences and have no odd-order unit certificate. A proper gcd would factor N, but a saturated zero does **not** automatically give an original-label nonzero annihilator. Therefore one cannot divide by them or call an original-leaf consumer on them. Keep T_full in (5) cleared. Acquiring and certifying their whole product would itself be an additional long polynomial-orbit query, not a free boundary test.

No multiplication of an identity by these potentially nonunit factors is used to infer an equivalence of zero tests. The equivalence is (7), whose prefactor eta^(dm) is a known unit.

## 4. Cost and the actual next interface

Equations (2)–(5) acquire a new off-resonant twisted-vacuum seed and its cleared full-sector transfer in softly O(L), with constant-many endpoint evaluations available at the same cost. This genuinely removes the “solve the Bethe equations / acquire the vacuum input” ambiguity for this candidate, including repeated roots and composite coefficients. It is **not** itself a shared correction evaluator. Expanding roots of F or all m transfer values is not charged as available data.

The remaining scalar in (7) is an initialized ordinary polynomial geometric product. Applying the existing paid evaluator costs softly O(L+sqrt(Lm)); this finishes the candidate with all amplitudes included but changes no exponent. The proposed soft O(L+sqrt m) rate does not follow from the exact TQ seeds. Likewise solving the rational form (6) by endpoint division would either erase collisions or require a new nonunit-pivot algorithm.

The useful next question is now sharply specified: can the particular coefficient-diagonal inverse in (2), together with its fixed known twist kappa=eta and full occupied identity (5), evaluate the **cleared coupled amplitude** in (7) faster than the generic orbit product? Its q-difference right side is the actual native S, so any shortcut must use more than formal vacuum/eigenvalue cancellation. No such shared amplitude algorithm is established here. This report is one executed algebraic closure with paid seeds and honest continuation cost, not a new lower bound or an assertion that other fusion hierarchies cannot work.
