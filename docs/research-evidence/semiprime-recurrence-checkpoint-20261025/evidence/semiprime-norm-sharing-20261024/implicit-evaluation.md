# Exact implicit norm evaluation: logarithmic derivative and telescoping test

24 October2026. Scratch only. This executes an exact first-derivative/norm test from the two supplied short factors, derives a zero-safe polynomial q-difference system, and tests primary creative-telescoping and holonomic-evaluation interfaces. The initialized per-point algorithm costs soft(J+G); m points still cost soft m(J+G). No faster batch is obtained. A separate native multiplicity argument below gives a constant local collision count in one important smaller-prime branch, but does not acquire the collision polynomial or endpoint amplitudes.

## 1. Actual input and scalar orientation

Use `../semiprime-native-terminal-20261024/composed-terminal.md`, SHA256 `6ad4b2e3206dec95673013b34f9a0ee52d77f134b89af9f21bd450902ad264e8`, independently reviewed at `f4eec2729247c98d92b7dd2a623fc244d972a5d740ea94da14368c4576521518`. The actual monic F(X)=product_j(X-y_j) has J=Theta(k) acquired unit roots, Gamma_G(Z)=product_(g<G)(Z-Q^g) has G=Theta(k), Q=q^k, and

    R(t)=product_(j,g)(t-Q^g y_j), D=JG=Theta(k²),
    H_t(X)=X^G Gamma_G(t/X), R(t)=Res_X(F,H_t).     (1)

The coefficient algebra mathcalB is the acquired rank-two étale quadratic algebra over Z/N, with one unknown nonsplit field side. Its coefficient factor/unit/globalzero classifier is available. Actual q orders are k-rough and its guarded differences extend through16H. Main length is L0=2H with m=k,G=2k; reciprocal augmentation uses q^(1-L0), and the two original tail factors remain separate. Repaired length3H+2 uses G=3k. All D<=6H<P,Q. Desired nodes are t_i=q^(-i),0<=i<m, with original native or reciprocal root flags. Equation(1) is monic and exact, not a symbolic norm with an omitted phase.

## 2. Execute one point, including a guarded logarithmic derivative

For an actual unit t, acquire both degree-G coefficient arrays H_t and partial_t H_t in soft G. Run guarded extended Euclid on F,H_t. Every mathcalB pivot is tested: norm-unit gives its inverse; proper integer gcd factors; a saturated norm gives a proper coordinate gcd unless the coefficient is globally zero, which alone permits degree drop. Hence either this finds a factor, or computes the actual monic gcd and resultant in soft(J+G).

A positive-degree gcd certifies a collision in at least one component. It can be localized by the supplied-root/clock subset splitting algorithm of the pinned report, still soft(J+G). A nonunit scalar resultant uses the same original-label localization. No derivative or auxiliary pivot is assigned a collision decoder.

On the UNIT-resultant branch H_t is a unit in E=mathcalB[X]/F. Acquire its actual inverse U_t modulo F by that extended gcd, and form

    Z_t=U_t*(partial_t H_t) modF.

The determinant derivative identity gives

    R'(t)/R(t)=Trace_(E/mathcalB)(Z_t).            (2)

This works with repeated augmented roots: E is free and norm is a determinant; only the actual norm-unit condition is needed. The trace of sum_(r<J) z_r X^r is sum z_r p_r, where p_r are the actual root power sums of F (p0=J). Acquire the first J power sums once by reversing monic F and its formal logarithmic derivative, soft J. All small integer divisions, if used, are units. Multiplication, reduction and trace now cost soft(J+G). This is an actual zero-safe interface: nonunit norm returns an original witness or factor; otherwise (2) is computed using a certified inverse. It does not differentiate a branch-specialized resultant circuit at a zero.

Thus R(t) and, where defined, its logarithmic derivative are acquired per point in soft(J+G). Repeating at all m nodes costs soft m(J+G)=soft k². The trace data do not determine the missing amplitudes R(t_i); a logarithmic derivative alone also discards multiplicative constants. No batch preprocessing improvement is assumed from the common F.

## 3. A short exact telescoping equation, made zero safe

Put A(t)=F(Q^(-(G-1))t), B(t)=A(Q^G t). Both degree-J generators are actually acquired and

    A(t) R(Qt)=B(t) R(t).                         (3)

Let theta=t*d/dt. On a branch where division by R is legitimate, S=theta R/R satisfies

    S(Qt)-S(t)=theta B/B-theta A/A.               (4)

The right side is an acquired rational function with denominator AB of degree2J. To avoid silently treating its poles as legal starting values, differentiate(3) BEFORE dividing. The exact polynomial system is

    A(t)^2 [R(Qt); theta R(Qt)]
       =[[AB,0],[A theta B-B theta A,AB]]
                                      [R(t);theta R(t)]. (5)

All its coefficients and their derivatives cost soft J and it is valid through zero values. At t=0 the known initial state is(R0,0), and short formal coefficient prefixes are paid. But multiplication by Q fixes0; it supplies no path from that constant coefficient state to any unit t_i. On unit-node chains (5) advances by Q=q^k, giving m separate residue-class chains, with the same unknown starting amplitudes as(3). Dividing by A at an auxiliary endpoint is not automatic; retaining(5) avoids that division but does not solve its boundary problem.

An initialized full completion is to compute the D actual formal coefficients via the q-log equation of the previous packet and evaluate them by geometric MPE. It costs soft D. Alternatively use the old labelled blocked algorithm at soft(J+sqrt(JGm))=soft k^(3/2), which remains better. The short forcing in(4) does not remove those costs.

## 4. Primary creative-telescoping test: moving poles are not a supplied ODE

Shaoshi Chen and Michael F.Singer, *Residues and Telescopers for Rational Functions* (2012), [primary preprint](https://arxiv.org/abs/1203.4200), Section4.1.3, Theorem4.13. Its coefficient field has characteristic zero and the q-shift parameter is NOT a root of unity. For a rational function in residual form with poles beta_i(t) in distinct q^Z-orbits, a differential-in-t telescoper for q-difference summation exists iff all those pole locations are constant in t. This is a precise criterion for that rational-certificate setting, not a finite-ring evaluation complexity theorem.

The natural summand for theta R/R is

    psi(t,z)=(t/z) F'(t/z)/F(t/z),
    S(t)=sum_(g<G) psi(t,Q^g).

For a formal characteristic-zero splitting with generic non-Q-related roots y_j, its simple poles in z are t/y_j, with nonzero residues; they MOVE with t. Thus Theorem4.13 does not furnish the hoped-for differential telescoper with a rational z certificate. The easy q-telescoper is instead the boundary relation(4), already executed above. A finite G sum is rational in t and admits differential equations after its denominator is acquired, but that does not make the G-independent rational-certificate hypothesis true.

This formal applicability check is deliberately scoped. Our actual finite Q has finite order, so the characteristic-zero/non-root-of-unity theorem is not a native nonexistence result. Special native cancellations are not excluded by it. In particular the report does not infer that every differential equation for R is large. The ordinary identity R'=(R'/R)R has a degree-D rational denominator in the general root product; acquiring its coefficient array costs soft D using the known completion, and no smaller native denominator is supplied here.

## 5. Primary bit-burst and rectangular-splitting contracts

Marc Mezzarobba, *A Note on the Space Complexity of Fast D-Finite Function Evaluation* (2012 author version), [primary PDF](https://marc.mezzarobba.net/ecrits/Mezzarobba_TruncatedBinarySplitting_v1_2012.pdf), Section2. The setting is a supplied ODE over Q(i)(z), specified initial values, an ordinary expansion point, and a rational complex evaluation point inside a convergence disk and bounded away from its singular boundary. Its degree parameter s is O(1); order and coefficient bit size enter the analysis. Its target is a complex approximation with certified error2^-p, not exact residues modulo an unknown composite. Neither a missing ODE nor the missing initial amplitudes are outputs of this theorem.

For our actual product, the natural first-order differential coefficient in Section3 is not a supplied bounded-degree ODE. Moreover lifting all factors to bounded integers gives an UPPER height bound O(D log N) bits for their product. A literal certified lift/approximate/reconstruct execution may charge that full bound to guarantee exact recovery uniformly, and therefore supplies no desired small clock. This upper bound is not a precision lower bound for every actual product; cancellations or a different certified modular procedure could be cheaper. Merely requesting O(log N) numerical significant bits does not establish exact residue recovery for an unspecified lift. No finite-ring numerical approximation oracle is available.

Fredrik Johansson, *Evaluating Parametric Holonomic Sequences Using Rectangular Splitting*,2013, [primary PDF](https://www3.risc.jku.at/publications/download/risc_4881/1310.3741v1.pdf), Theorems2--3. The promised savings concern nonscalar multiplications; Theorem2 still charges O(n) scalar operations and O(M(n)log n) coefficient operations. Theorem3 with block length b charges O(b+n/b) nonscalar multiplications, O(n) scalar operations and O((n/b)M(b)log b) coefficient operations. Its ordinary holonomic coefficient hypotheses are not automatically a recurrence with Q^n coefficients of growing degree J.

If one instead uses rectangular evaluation of Gamma_G(tv) in the actual rank-J algebra E, even the supposedly scalar coefficient operations on arbitrary E vectors have rank-J cost. Computing all m nonlinear norms afterwards is an additional output operation. Neither the primary operation hierarchy nor an O(sqrt G) nonscalar count makes those rank-J scalar operations free. The previously proved soft(J+G) single-point resultant is actually better for one norm. No improved multiquery exponent follows from this tested rectangular-splitting invocation.

## 6. A native constant-multiplicity refinement, with no sparse-recovery oracle

There is a useful source-specific count when the SMALLER prime P is the nonsplit side. Use the canonical parity-repaired rows from native-pairing.md (pin in the preceding packet), with a<2k, delta=a+ell in span<5H, ell in(-4.5H,H/2), horizon3H+2. At P the odd scalar beta order r_beta divides P-1; the odd norm-one W order r_W divides P+1. They are coprime and each>16H, so r_beta*r_W>256H². Their intersection is trivial. The hypotheses are about actual prepared beta,W; no such order is inferred at the split side.

For a MINUS-colour collision define X=delta-Hi. Separating scalar and torus parts gives

    X=-N mod r_beta,  X=N+2a mod r_W.

Because P=1 modulo r_beta and P=-1 modulo r_W, CRT yields

    r_beta*r_W divides X+Q+(P-1)a.

For the SMALLER P, P<=k³,Q<H²/16,a<2k and i<3H+2 make the absolute value strictly below, for example,8H² on the continuing branch. It is therefore zero as an INTEGER:

    H i=aP+Q+ell.                                 (6)

Multiplying by P and reducing modulo H gives aP²+ell P+N=0 mod k². The authoritative native coefficients satisfy

    aP²+ell P+N
       =a(P-j)²+k b(P-j)+k² c_j.

If a prime l|k has valuation s=v_l(P-j)<v_l(k)=e, the first term has valuation2s and the second at least e+s>2s, so their sum cannot be divisible by l^(2e). Since a is a unit, this proves k|(P-j). Thus a minus hit must have the EXACT own tag j=P mod k, not merely one of several square-root classes. In the canonical one-row-per-tag family there is exactly ONE such hit row; the own-row proof supplies it and the q order>horizon gives one index. Retaining the known duplicate descriptions only changes this constant.

For PLUS rows, V=pi^(N+delta) with pi=beta W, and ord_P(pi)=r_beta*r_W>256H². Two local hits imply that delta_j-delta_h-H(i_j-i_h) is a multiple of that order. Its size<5H+4H² forces it to be zero. Hence all plus hits have one common delta modulo H. Strict delta span<5H and exact-delta fibers<=16 give at most5*16=80 canonical plus hit rows. The full canonical product consequently has at most81 colliding factors at this smaller nonsplit prime.

This is an actual bound for the stated branch, not for the larger nonsplit prime, the split side or arbitrary transformed rows. It could cap the required Hasse depth of a FUTURE uniformly valid scalar-product circuit or a proved sparse-intersection solver. It does not acquire the locations, the nonzero amplitudes, R mod P_m or a collision polynomial. A degree-small local gcd can coexist with a dense remainder and many unknown nonzero values; this report supplies no algorithm bypassing those values from the count alone. No sparse-recovery oracle is introduced. In particular, a small collision multiplicity at epsilon=1 does NOT imply that a deformation product has small degree in epsilon, or that a short/polylogarithmic jet at epsilon=0 determines its value at epsilon=1. Any such homotopy endpoint remains a separate acquisition problem.

## Outcome and primary pins

The completed new interface is a soft(J+G) single-point norm/unit-test/trace computation with certified inverses, and the exact zero-safe system(5). The batch remains soft k² by that route, or soft k^(3/2) by the original blocked completion. Native local multiplicity can be constant in a precise branch, but no faster terminal batch follows yet. All completed nonunits keep their original main/reciprocal/tail maps and use the appropriate original consumer. No generic differential/q-difference lower bound or factoring-rate gain is asserted.

Cached PDFs: `sources/chen-singer-2012.pdf` SHA256 `341640da3b5d3399e95a95f20fac034808fc67086e78ea34764bcd0321e87b48`; `sources/mezzarobba-truncated-2012.pdf` SHA256 `3b88d65995e7d61df0945ced7282709bea673f9b1f2713e13fb044d0e200638e`; `sources/johansson-parametric-2013.pdf` SHA256 `fc061f52d1582ec275a5e0d6e178d5e8159aef00be1b81f6935f26a97ae5a329`. Extracted text is retained. No shared edits or numerical examples were used.
