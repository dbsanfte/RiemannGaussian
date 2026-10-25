# Finite adjoint certificates with both coefficient ends paid

24 October 2026. Scratch only. The executed two-step certificate below has genuinely cheap initialized coefficients and correct cross-term cancellation. It transports the desired functional to another endpoint; it does not acquire its amplitude. A variation-of-constants transpose identifies that missing amplitude literally, after the supplied upper boundary terms have been removed. A complete q-log/transpose implementation costs soft D=soft k²; the existing soft k^(3/2) query remains better. This is an audit of these actual algorithms, not a generic adjoint lower bound.

## 1. Exact input and the rough-clock divisions

Use `/tmp/semiprime-quadratic-batch-20261024/reciprocal-recurrence.md`, final SHA256 `4642b776f4c72a42a5a2c20beac07b25dbff0a21ba9f3569cd495108d4801f1b`, independently reviewed at SHA256 `f73675dd2b712132a82a9ae492b1f80a4f9ec7912256f2c48ac2acd8da31b033`.

The actual main interval is L0=2H, H=k², m=k, G=2k and Q=q^m. Its last two original factors are separately acquired; no balanced divisor of 2H+2 is assumed. Let F be the acquired native point polynomial of degree j=J, or its actual reciprocal augmentation of degree j=2J. Put

    A(T)=F(q^(-m(G-1))T), B(T)=F(q^m T),
    R(T)=prod_(g<G) prod_(F(y)=0)(T-q^(mg)y),
    D=jG <=4H, A(T)R(QT)=B(T)R(T).                  (1)

The root-product notation means the supplied actual roots, with multiplicities, not a hidden factoring oracle. A,B have degree j=O(k); a0=b0 is an acquired unit. R is monic, r0 is an acquired unit from the explicit product of its root units and q phases. Both length-k coefficient ends are paid in the source. If a stencil needs j instead of k coefficients, acquire both length-j ends by the SAME power-sum construction, cost soft(k+j)=soft k. This is not free interpolation of a middle vector.

Each local component order of q is k-rough; gcd(m,ord(q))=1 because m=k. Hence Q^n=1 in a component implies q^n=1 there. For 1<=n<=D<=4H<C=16H, the actual q screen excludes this. Therefore Q^n-1 is a unit in the whole constant-rank quadratic ring B, even when mn>C. This proves the legitimacy of a division if used; explicitly producing all D denominators and inverses still costs soft D. Also 1,...,D are units because P,Q>16H. These are supplied-order facts, not an assumption that an unscreened generic clock is nonresonant.

Write a_i,b_i for A,B coefficients. Coefficients outside 0,...,D of R are zero. The exact coefficient operator is

    (L r)_n=sum_(i=0)^j (a_i Q^(n-i)-b_i) r_(n-i)=0,
    (L* z)_s=sum_(i=0)^j (a_i Q^s-b_i) z_(s+i).      (2)

All pairings below are finite: s=0,...,D and n=0,...,D+j. Swapping those two finite sums proves sum_n z_n(Lr)_n=sum_s r_s(L*z)_s. No infinite convergence, output inverse or missing end term is invoked.

## 2. Execute one nontrivial telescoping certificate

The functionals needed for R mod P_m include evaluation at the ACTUAL roots

    t_i=q^(-i), 0<=i<m,
    P_m(T)=prod_(i<m)(1-q^i T).

Their differences and their leading coefficient are certified units by the q screen. Their actual values R(t_i), followed by multiplication and known unit phases, give the original main scalar; in the reciprocal-augmented version they give its known-unit square. The separately acquired last-two-factor square restores the full-query square.

For one such actual t, first try z_s=t^s. Then

    (L*z)_s=t^s[Q^s A(t)-B(t)],
    A(t)R(Qt)=B(t)R(t).                              (3)

Now initialize a REAL two-step certificate, rather than assert an abstract telescoper:

    z_s=t^s[B(Qt)+A(t)Q^s].

Direct substitution gives

    (L*z)_s=t^s[A(t)A(Qt)Q^(2s)-B(t)B(Qt)].          (4)

The coefficient of Q^s is B(Qt)A(t)-A(t)B(Qt)=0. Thus finite summation by parts yields

    A(t)A(Qt)R(Q²t)=B(t)B(Qt)R(t).                   (5)

All four coefficient arrays A(t_i),A(Qt_i),B(t_i),B(Qt_i) are ACTUALLY acquired by four monic multipoint evaluations of supplied degree-j polynomials at m supplied arguments, soft(j+m)=soft k work. Certificate storage is two coefficients per t; the powers t^s,Q^s have O(log N)-bit exponent indices if requested. No D-by-m certificate array is produced. Identity (5) remains valid when any coefficient or R value is nonunit; it does not take an undefined quotient.

For g steps, an explicit fraction-free certificate is

    z_s=t^s sum_(d=0)^(g-1) z_d Q^(ds),
    z_d=prod_(a<d) A(tQ^a) * prod_(d<b<g) B(tQ^b).

Adjacent additive terms cancel because z_(d-1)A(tQ^(d-1))=z_d B(tQ^d). The exact result is

    [prod_(a<g) A(tQ^a)] R(Q^g t)
       =[prod_(a<g) B(tQ^a)] R(t).                  (6)

Literal acquisition at all m arguments has g*m coefficient evaluations and soft(j+gm) multipoint work, plus corresponding products; no g-step generator table is free. At g=G this returns the old degree-j by mG native grid operation, not a cheap boundary amplitude.

Even where the coefficients in (3) or (5) are units, the result is only acquired endpoint TRANSPORT. It supplies no R(t) or R(Qt). In the augmented case the known reciprocal centre b=q^(1-m) sends Qt_i to q^(i+1-2m): this is a different block of m arguments, not the same m initial values. Its actual reflected label is 2m-1-i in [m,2m-1], which must be retained; the supplied first block is not an initialized second block. Repeated transport does not turn a supplied coefficient end into a supplied evaluation.

Nonunit A/B coefficients have not been divided out or declared original witnesses. The certificate requires no such division. One could screen them, but every additional screen needs its actual row/index interpretation and bounded consumer; no arbitrary auxiliary coefficient norm is passed to the original decoder here.

## 3. A finite boundary-value adjoint, with its actual missing state

For clarity, a direct coefficient certificate using both supplied ends can be initialized as follows once its reverse trajectory has been paid. Take w=j, suppose D>2j, set z_n=0 outside j<=n<=D, and also set z_(D-j+1),...,z_D=0. For s=D-j,...,j solve backwards

    z_s=[lambda_s-sum_(i=1)^j(a_i Q^s-b_i)z_(s+i)]
                                  /[a0(Q^s-1)].     (7)

Every denominator is certified by Section 1. Then (L*z)_s=lambda_s for j<=s<=D-j. Its nonzero left boundary lies only at 0<=s<j; its right boundary vanishes. Exact finite summation gives

    sum_(s=0)^D lambda_s r_s
      =sum_(s<j)[lambda_s-(L*z)_s]r_s
                       +sum_(s>D-j)lambda_s r_s.    (8)

Both r vectors on the right are the already supplied ends, enlarged to width j if needed. If D<=2j the entire R is already a soft-k-size input and direct completion is cheap; the native growing branch has D much larger.

Equation (8) really reduces the contraction to those two known ends AFTER the first j adjoint boundary values have been acquired. Naively executing (7) costs O(Dj) ring work for one supplied functional. For lambda_s=t^s its scalar starts are explicit, but the trajectory remains long. This is the exact additional state, not a mere existence assertion for a small approximant basis.

The following faster initialized implementation sharpens that ledger and exposes what transposition needs. Let multiplication and series be truncated modulo T^(D+1). For a series v with v0=0,

    L(Rv)=BR*[v(QT)-v(T)].                          (9)

Consequently, on zero-constant forcing, the normalized causal inverse is the actual linear circuit

    L_+^(-1)=M_R * Delta_Q^(-1) * M_(BR)^(-1),
    Delta_Q^(-1)(sum_(n>=1) f_n T^n)
                         =sum_(n>=1) f_n/(Q^n-1) T^n. (10)

M denotes truncated multiplication. All inverses in (10) have unit CONSTANT coefficients, or are the explicit Q differences. This is not an inverse of a covered terminal value.

If R and its needed inverse series are acquired densely, (10) and its transpose cost soft D by polynomial multiplication and middle products. But those are D actual coefficients. In particular, the FIRST transposed convolution on an evaluation functional is literally

    (M_R^t lambda)_s
       =t^s sum_(a=0)^(D-s) r_a t^a
       =t^s[R(t)-sum_(a>D-s) r_a t^a].              (11)

For 1<=s<=j, the final sum is supplied by the paid upper coefficient end. The remaining term is R(t), exactly the desired unknown amplitude. Thus using the small known head/tail to “initialize the transpose” in this variation-of-constants circuit is circular. This equation identifies the actual unacquired quantity for this candidate; it does not assert that every adjoint implementation must use that circuit.

For a generic single supplied lambda, transposition is lawful after the fixed coefficients in (10) have actually been acquired. The homogeneous polynomial has r0 nonzero: its positive coefficient vector solves L_+r_+=-r0*(A-B)_+. Hence an acquired adjoint z gives the contraction by pairing only with this degree-j source, plus lambda0*r0. This useful short final pairing does NOT acquire the long certificate. Equation (11) states why the proposed shortcut to its initialization has not done so.

## 4. Complete zero-safe initialization and cost

There is an actual soft-D construction of every fixed coefficient used in (10). Since a0=b0 and r0 is a known unit, normalize S=R/r0, S0=1. From (1),

    log S(QT)-log S(T)=log(B/b0)-log(A/a0).

Acquire both logarithms through D, divide their nth coefficients by Q^n-1 for 1<=n<=D, exponentiate, and multiply by r0. All operations are finite series with known unit constants. The only integer divisions have indices <=D<P,Q; every clock denominator is guarded by Section 1. This produces the ACTUAL full R, not a generic formal solution chosen up to an unknown normalization. Its q-difference coefficients and r0 uniquely determine its series through D; equation (1)'s known root product proves this is the intended polynomial.

This algorithm, all denominator arrays, full R and inverse-series constants cost soft D. Then reduce R modulo the actual monic-normalized P_m and/or evaluate it at all m known roots, soft(D+m), and form the scalar resultant with its explicit leading/sign phases. It works at zeros because no R(t_i) is inverted. Restore the original last-two-factor product or its square as appropriate. This is a complete soft k² algorithm for the main query, not the requested soft k improvement and not an improvement on the retained soft k^(3/2) blocked query.

The two-step certificate (4) itself is a positive soft-k acquired object. Its ratio interpretation requires unit endpoints; without them only identity (5) is stated. The causal and finite-boundary adjoint (7)--(11) are fully specified; their shortcut has the exact missing amplitude (11). Both paid ends therefore remove actual tail corrections but have not closed this terminal contraction.

## Ledger and recovery scope

| Quantity or action | Paid cost | What is actually initialized |
|---|---:|---|
| A,B,r0, enlarged O(j) coefficient ends | soft k | actual roots, normalizations and both boundaries |
| Q^n-1 nonresonance for n<=D | proved from roughness | enumerating/inverting all D costs soft D |
| One/two-step certificates at all m roots | soft k | coefficient arrays, no output inverse |
| g-step explicit certificate data at all m roots | soft(j+gm), plus products | transport (6), not endpoint amplitude |
| Reverse stencil (7), naive one functional | O(Dj) | complete finite-boundary certificate |
| Full q-log initialization, fast transpose/remainder | soft D=soft k² | actual full R and every fixed circuit coefficient |
| Hypothetical soft-k first adjoint boundary from ends alone | not acquired | (11) retains R(t) |
| Original optimized blocked query | soft sqrt(JL0)=soft k^(3/2) | retained best whole-query completion |

The augmented main scalar is a known unit times the original main product squared; multiply the acquired original tail squared, not a missing main phase. Reciprocal-image leaves map only inside the main interval by i->L0-1-i. Every completed nonunit norm is localized to an actual original row/index before the nonsplit/G_beta consumer. A saturated norm leaf does not imply whole equality on a split side. Nonunit certificate coefficients and arbitrary transported endpoints have not been assigned that consumer. No new source algebra, finite sample campaign, generic impossibility theorem or factoring exponent improvement is claimed.
