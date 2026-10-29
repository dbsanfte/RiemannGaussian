# Multi-hook collective correction: an executed two-hook test

2026-10-26. This pass tests a collective colored invariant, including its A=1 vanishing order. It does not repeat one-hook scaling as a solution. The exact skein Giambelli relation includes an unacquired satellite correlation; replacing it by a determinant of known hook values fails even as a zero selector. No soft O(L+sqrt m) prefix algorithm is established.

Variable convention (corrected after independent review): K(T) uses the ordinary Seifert/Alexander variable. The HOMFLY skein quantum parameter is s0=beta^(H/4), so s0²=eta and the fundamental A=1 specialization at s0 is K(s0²)=K(eta). Quantum-dimension brackets below are **[h]=s0^h-s0^-h**, while hook knot values remain K(eta^h). These two parameters must not be identified. The v used below is the inverse of Lukac's source v convention, so his loop value (v_source^-1-v_source)/(s0-s0^-1) becomes our (v-v^-1)/(s0-s0^-1). Use zero framing and the explicit dimension formula below consistently.

## 1. A multi-hook color whose diagonal hooks are exactly the desired odds

Write arms/legs in zero-based Frobenius notation. Take

    lambda_m=((m+1)^m,m),
    alpha_i=beta_i=m+1-i,  1<=i<=m.

It has Durfee rank m, size m(m+2), and diagonal hook sizes 2m+1,2m-1,...,3. Thus its diagonal hook factors are exactly the desired P_m=prod_(i=1..m)K(eta^(2i+1)), in reverse order.

In the positive annulus HOMFLY skein, the exact identity is

    Q_lambda = det_(i,j=1..m) Q_(alpha_i|beta_j).        (1)

Here multiplication is multiplication of annular patterns. Satellite insertion into a fixed knot, followed by evaluation, is linear; it is not a ring homomorphism to products of scalar knot evaluations. Therefore (1) does **not** give a determinant of the m² normalized one-hook Alexander values. This distinction matters even after correct quantum-dimension normalization.

Primary: Sascha G. Lukac, *Idempotents of the Hecke algebra become Schur functions in the skein of the annulus*, MPCPS 138 (2005), 79–96, DOI 10.1017/S0305004104007984, [primary PDF](https://www.liverpool.ac.uk/~su14/papers/lukacschur.pdf), [arXiv:math/0110119](https://arxiv.org/abs/math/0110119). The annular idempotent closures obey the Schur/Littlewood–Richardson algebra; this is the level at which (1) is used.

## 2. Correct vanishing order and a legal finite-ring normalizer

Use v for the HOMFLY A-variable, distinct from arithmetic eta and the skein quantum parameter s0. Put tau=v-v^-1 and [h]=s0^h-s0^-h. Since 2 is a unit, tau is a valid formal local parameter at v=1. The quantum dimension is

    d_lambda(v,s0)=prod_(box in lambda)
                        (v s0^content-v^-1 s0^-content)/[hook].

Its vanishing order is the number of diagonal boxes. For a hook (alpha|beta),

    d_(alpha|beta)=tau*(-1)^beta/[alpha+beta+1]+O(tau²).

Applying the ordinary quantum-dimension evaluation, which **is** an algebra map, to (1) gives the leading coefficient

    d_lambda=tau^m*kappa_lambda+O(tau^(m+1)),
    kappa_lambda=det_ij[(-1)^beta_j/[alpha_i+beta_j+1]]. (2)

All [h] needed here have 1<=h<=2m+1. Since [h]=s0^-h*(eta^h-1), they are units under the native eta-order guard. Native odd beta-orders give ord(s0)=ord(eta)=ord(q)>16H. The determinant in (2) is a Cauchy determinant up to unit row/column scalings: with A_i=eta^alpha_i and B_j=eta^(beta_j+1), its kernel is 1/(A_i B_j-1). Its cross denominators and its within-alphabet differences are nonzero short eta-differences, so kappa_lambda is a unit in R. This is a unit certificate, not free numerical acquisition of its large hook product. A finite annular presentation can use the Jacobi–Trudi formula in complete functions h_r with r<=2m+1, so only short quantum-factorial inverses are needed. No inverse of [m(m+2)]! or generic full-size Hecke idempotent is asserted.

Consequently extraction of the tau^m coefficient is a legitimate formal normalization; it is not division by the zero value tau=0 in R. For normalized colored invariants regular at v=1, W_lambda=d_lambda H_lambda, the reduced Alexander value is [tau^m]W_lambda/kappa_lambda. That coefficient must still be acquired. The sparse Seifert matrix of K does not by itself supply a colored HOMFLY satellite expansion to this order.

## 3. Execute m=2, where the required correction is already visible

The desired color is lambda_2=(3,3,2), with Frobenius coordinates (2,1|2,1). Its exact Giambelli relation is

    Q_332=Q_311*Q_21-Q_31*Q_211.                       (3)

The diagonal hook sizes are 5 and 3; both off-diagonal hook sizes are 4. Let E_K be the linear satellite evaluation, W_mu=E_K(Q_mu), and define the exact correlation defect

    B_(mu,nu)=E_K(Q_mu Q_nu)-W_mu W_nu.

Then (3), before specializing v, gives

    W_332=W_311 W_21-W_31 W_211
                    +B_(311,21)-B_(31,211).           (4)

This is an actual identity, not an unproved evaluation-map multiplicativity assertion. Individual defects can have lower vanishing order. Under the regularity hypothesis for the reduced H_332 stated above, the *combined* correction in (4) has order at least tau², because the left side and both displayed products do. This divisibility is not inferred from annular Giambelli alone; the normalized A_332 identity below retains that regularity hypothesis.

Put K_s=K(eta^s), A0=1/([5][3]), B0=1/[4]². The hook leading signs give

    kappa_332=-(A0-B0),
    A0-B0=[1]²/([5][3][4]²),                            (5)

where [4]²-[5][3]=[1]². Thus kappa_332 is a certified unit. Dividing the tau² coefficient of (4) by it yields the exact normalized correction formula

    A_332 = Gamma_2 + E_2,
    Gamma_2=(A0*K_5*K_3-B0*K_4²)/(A0-B0),
    E_2=[tau²](B_(311,21)-B_(31,211))/kappa_332.         (6)

No collision value K_s is inverted. Gamma_2 is genuinely acquired from three known scalar evaluations in O(L) ring operations. E_2 is the missing joint satellite correlation, not an implicitly zero quantity.

### The determinant-only replacement misses a collision

Suppose K_3=0 and K_4 is a unit. Then the desired two-factor norm K_3 K_5 is zero, while

    Gamma_2=-K_4²*[5][3]/[1]²

is a unit. Therefore even the correctly dimension-normalized determinant of hook evaluations is not a zero-preserving replacement for the diagonal norm. The correction E_2 cannot be declared a harmless unit *multiplier* or omitted. This conditional collision calculation does not claim that an arbitrarily selected native catalogue has this exact pattern; it disproves the proposed universal replacement mechanism.

The condition is consistent with genuine integer knot polynomials and odd local orders: take any eta for which eta^3-1, eta^4-eta^3 and eta^4-eta^-3 are units, set c=-(eta^3+eta^-3-2)^-1 modulo N, lift c to an integer, and choose the genuine genus-one Alexander polynomial K(T)=1+c(T+T^-1-2). Then K_3=0 and K_4 is a unit. This is a symbolic diagnostic specialization, not an asserted attained native factoring/controller instance or an experiment campaign.

For the actual native family, (6) is useful as a checklist: a claimed gl(2|2)/modified-trace formula must either compute E_2 or prove a different expression whose zeros retain the original diagonal product. It cannot infer that merely from Giambelli for annular patterns.

## 4. What genuine Giambelli-compatible supergroup averages do and do not imply

Primary: Bertrand Eynard and Taro Kimura, *Towards U(N|M) knot invariant from ABJM theory*, [arXiv:1408.0010v2](https://arxiv.org/abs/1408.0010), 2016 revision; Letters in Mathematical Physics 107 (2017), DOI 10.1007/s11005-017-0936-0. Their supermatrix character averages admit determinants of U(1|1) building blocks, with explicit Cauchy/framing factors for the unknot and a torus-knot-motivated model. This is genuine expectation-level Giambelli compatibility in the specified model, a stronger property than (1). It is not a theorem that the arbitrary native Seifert-realized knot has that measure, or that its building block is simply K(eta^s)/[s].

Even if one had exactly that latter building block, its normalized m-by-m determinant would contain all permutation terms, not only the diagonal norm. Equation (6) executes the first nontrivial difference. Any exact model computing a different collective invariant must prove a norm/zero-preserving identity, not just match the diagonal hook sizes.

The unweighted determinant det[K(eta^(alpha_i+beta_j+1))] is even less suitable: because K is a Laurent polynomial of degree L, it is a sum of at most 2L+1 separated exponentials in i,j, and vanishes identically for m>2L+1. That is a background rank defect, not a prefix hit. The correctly weighted Cauchy denominator removes this simple rank argument, so no such rank claim is made against the dimension-normalized determinant.

## 5. Tug-the-hook and modified traces

Under simultaneous tug alpha_i->alpha_i+epsilon, beta_i->beta_i-epsilon, every cross-hook size alpha_i+beta_j+1 remains unchanged, not just the diagonal ones. The Durfee rank and total size stay m and m(m+2). Even a fully valid tug symmetry therefore does not reduce the number of hooks or remove the correction channels in (6).

Primary scope reference: Mishnyakov–Sleptsov–Tselousov, *A new symmetry of the colored Alexander polynomial*, [arXiv:2001.10596v4](https://arxiv.org/abs/2001.10596), states its tug symmetry conjecturally and studies its group-factor/character constraints. No unproved full-symmetry assertion is used in this report; the invariance of hook sizes just noted is an elementary statement about the transformation itself.

Modified trace is a legitimate way to define invariants when ordinary quantum dimensions vanish, but its defining normalization must be specified. It does not imply multiplicativity of a satellite evaluation on (1). Primary example: Matthew Harper, *A Non-Abelian Generalization of the Alexander Polynomial from Quantum sl3*, SIGMA 22 (2026), 025, [primary paper](https://sigma-journal.com/2026/025/sigma26-025.pdf), uses fourth-root quantum groups and a modified trace; its specializations recover Alexander data, while its generic invariant carries extra information. The auxiliary fourth root can be represented in a fixed étale extension, but its representation parameter is not the native long-order clock. No product formula for all native odd evaluations is inferred from that normalization.

A tensor product of m cut, separately colored knot tangles multiplies their scalar Alexander values, but that is the disconnected m-factor construction again. Placing their colors on one cable introduces the joint satellite terms of (4). A proposed modified trace must establish why those terms are absent or computable with certified units; cutting strands is not an automatic scalar contraction.

## 6. Acquisition ledger and concrete remaining target

The color lambda_m has a binary shape descriptor, but explicitly listing its m Frobenius pairs costs Omega(m), and a literal cabling/idempotent description uses m(m+2) boxes. A literal Giambelli matrix has m² entries, or 2m-1 distinct hook sizes in this arithmetic progression. Acquiring all those scalar hook values by geometric multipoint evaluation costs soft O(L+m), already above soft O(L+sqrt m) at m~k^(3/2), L~k. This is the cost of that implementation, not an output lower bound for a scalar-only algorithm.

For m=2 the known diagonal/off-diagonal scalar part Gamma_2 is cheap, but even its exact correction requires coefficient data of a joint satellite not supplied by K. At general m, the missing coefficient is the connected/mixed part of the tau^m satellite expectation in (1). First Schur constants, the unit kappa normalizer, and the existing sparse Seifert input do not acquire that coefficient.

A genuinely sufficient new result would identify an exact native collective invariant whose tau^m coefficient factors as a certified unit times P_m, *and* compute that coefficient from the acquired O(L)-entry data and binary m in soft O(L+sqrt m), retaining every mixed channel needed at collisions. An alternative is an integral formula for the corrections with a proved soft acquisition bound. Neither is supplied by the inspected identities. Formula (6) states the first correction explicitly enough to test any proposed rule, and prevents its vanishing order from being confused with free normalization.

No numerical experiments, repository edits, or backend lemmas were used. The full native prefix retains the previous soft O(L+sqrt(Lm)) cost, with its existing zero/nonunit and leaf-recovery consumer. This failure is scoped to replacing the collective Giambelli correction by known hook values; it is not an obstruction to another multi-hook or modified-trace algorithm.

## Review correction record

An independent reviewer identified that the first draft used eta in the quantum-dimension brackets, although eta is the ordinary Alexander spectral base. This draft corrects the brackets to s0, where s0²=eta, and the Cauchy auxiliary base from q to eta. The hook values K(eta^h), exact Giambelli correction (4)–(6), its collision diagnostic, and acquisition conclusions are unchanged. The unit proof is now explicitly via eta^h-1; H is divisible by 4, so acquiring s0 requires no root extraction.
