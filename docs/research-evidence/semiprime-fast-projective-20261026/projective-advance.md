# Projective advancement from the paid prefix: exact block test

26 October 2026. Scratch paper research; no repository changes, tests, implementation, numerical campaign or Lean. **No sixth-rate advancement algorithm obtained.** The executed rational-block compression attempt has a new, scoped native degree obstruction below. This is not a lower bound for scalar evaluation, other compressed representations or all nonlinear algorithms.

Read the frozen projective-readout README, projective-closure.md and initial-chart.md, the current two-monic handoff, and the prior coefficient-forms/structured-expressions and old block/doubling audits. The 5J initialization and the old monic block evaluator are prior credit. They are not unacquired inputs in this pass.

## 1. Start from the ACTUALLY acquired chart

Use the licensed pure K=2*3^e branch, H=K², h=2H+1, q=pi^H, J=phi(K)<=K, and one of the two full unit-tag monic lists. The old preparation supplies odd K-rough scalar/torus orders and actual coupled short units. At the nonsplit prime R, ord_R(q)=ord_R(pi)>256H². One of the two lists has exactly one original hit with tag R mod n; n|K, n>2.

The supplied prefix either factors or acquires an index s and c in {0,1,2}, along with actual raw states (P_s,V_s,U_s), (P_(s+1),V_(s+1),U_(s+1)), such that P_s is a unit, both L=V+cU denominators are certified global units, and the two ratios U/L differ by a certified global unit. The prefix is within the first 5J steps and costs soft J on continuation. The selected chart is locally valid at the eventual hit. This removes the earlier initialization issue completely.

Put rho=q^-1 and use the acquired polynomials

    f(X)=product_j(1-y_j X),
    v(X)=sum_j product_(l!=j)(1-y_l X),
    u(X)=sum_j w_j product_(l!=j)(1-y_l X), w_j=[j]_n.

The homogeneous transition is

    T(X)=[[f,0,0],[v,f,0],[u,0,f]].

Its nilpotent parts have pairwise product zero. Consequently ALL T(X) commute formally; no noncommutative matrix-word problem is hidden here. This yields an exact small block law, but does not supply its values for free.

## 2. Execute polynomial block composition and nonlinear doubling

For a length b and variable start X define

    A_b(X)=product_(t=0)^(b-1) f(rho^t X),
    B_b(X)=sum_(t<b) v(rho^t X) product_(r!=t)f(rho^r X),
    C_b(X)=sum_(t<b) u(rho^t X) product_(r!=t)f(rho^r X).

The block matrix is [[A,0,0],[B,A,0],[C,0,A]]. Empty block is (1,0,0). Concatenation of lengths a,b is exactly

    A_(a+b)=A_a(X) A_b(rho^a X),
    B_(a+b)=B_a(X) A_b(rho^a X)+A_a(X) B_b(rho^a X),
    C_(a+b)=C_a(X) A_b(rho^a X)+A_a(X) C_b(rho^a X). (1)

Thus doubling is actually initialized and division free. Degrees are at most Jb. A monic/shared polynomial arithmetic implementation acquires the three coefficient lists in soft(Jb), evaluates them at all actual giant starts and handles the final residual block in total

    soft O(J+Jb+h/b).

Choosing b about sqrt(h/J) gives the retained soft(J+sqrt(Jh))=soft K^(3/2) monic-target execution. Applying each numeric block to the acquired state preserves singular hits without chart division. Computing a projective normal form after each doubling is the specific improvement tested next; it cannot simply discard a common long scalar.

## 3. Native no-overlap regime for a block

Work at the good nonsplit field. In BOTH possible good families the physical row exponents can be written

    y_j=pi^[Q+c_j P+ell_j],

where P is the smaller factor, c_j ranges over the SAME public coefficient AP {c:1<=c<K,c=N mod6}, and each c has precisely two tags, with opposite centred phases ell,-ell. This uses family A if R=P and family B if R=Q. It is not asserted for the other, unpromised family.

The phases satisfy |ell_j|<H/2. They are nonzero and not the centred half-period: ell_j²=4c_jN modulo H is a 3-unit, whereas 0 and H/2 are divisible by 3. Hence the two opposite phases really differ as integers.

Assume

    1<=b<=h,        6P-H>H(b-1).                (2)

The roots of A_b are alpha_(j,t)=q^t/y_j, 0<=t<b. Suppose two coincide. Then at R,

    pi^[(c_j-c_l)P+ell_j-ell_l-H(t-s)]=1.

The exponent has absolute value less than

    K*P+H+H*(b-1) <= H²+H+2H² <4H²,

using P<=sqrt N<=K³ and b<=2H+1. This is below ord_R(pi), so the exponent is zero as an INTEGER. If c_j!=c_l, the step-6 AP gives absolute value of the first two terms at least 6P-H, contradicting (2). If the coefficient is the same, |ell_j-ell_l|<H forces t=s; equality of phases then forces the same one of the two tags. Finally, for an identical tag the q-order bound forces the same time. Thus all Jb roots are distinct.

This regime includes any actual PREPARED balanced-size branch P=Theta(K³), with b=Theta(sqrt K) and sufficiently large K. That statement is conditional on the input already reaching the supplied prepared branch. It does not prove that the preparation controller must continue on a chosen family, nor replace a needed all-input theorem by special semiprimes.

At alpha_(j,t), only one leaf of the block vanishes. Therefore

    B_b(alpha)!=0, C_b(alpha)=w_j B_b(alpha).

The untagged cofactor is nonzero because every other leaf factor is nonzero. In particular gcd(A_b,B_b)=1 over the good field. The block matrix has no common polynomial factor to cancel. For the selected c chart, B_b+cC_b is also nonzero at every root, since 1+cw_j is a positive integer at most 2n-1<R.

## 4. Stronger bound: even the FIXED-START TAG RATIO has large degree

The relevant proposal is not obliged to construct the whole block matrix. Hold the actually acquired starting state (P_s,V_s,U_s) fixed as constants and consider just its rational block readout

    R_b(X) = [A_b(X)U_s+C_b(X)P_s]
             /[A_b(X)(V_s+cU_s)+(B_b(X)+cC_b(X))P_s]. (3)

At every alpha_(j,t), P_s is nonzero and the denominator equals

    B_b(alpha)*P_s*(1+cw_j)!=0.

Hence (3) has no pole there and takes the EXACT value

    R_b(alpha_(j,t))=w_j/(1+cw_j),               (4)

independent of time t. This remains true after any legitimate cancellation in its numerator/denominator. The values vary with the unit labels: reduction from unit tags modulo K onto units modulo n is surjective, n>2 gives at least two labels, and w->w/(1+cw) is injective at R.

Let A/B be a reduced representation of (3), and let d=max(deg A,deg B). Then R_b(qX)-R_b(X) has numerator

    A(qX)B(X)-A(X)B(qX), degree<=2d.            (5)

For every j and 0<=t<b-1, both alpha_(j,t) and q*alpha_(j,t)=alpha_(j,t+1) lie among the no-pole nodes in (4). Thus (5) vanishes at J(b-1) DISTINCT points.

The numerator is nonzero. If it were zero, R_b would be a q-invariant rational function. Write D=ord_R(q). Any nonzero finite pole/zero of a nonconstant q-invariant rational function has a full orbit of length D, forcing degree at least D. If its only zeros/poles are 0,infinity, it is a nonconstant monomial with exponent divisible by D, with the same degree bound. On the other hand (3) has a representation of degree at most Jb, so d<=Jb<=K(2H+1)<D, because D>256H². Invariance would therefore force it constant, contradicting its distinct values in (4). Equivalently, in a setting allowing d>=D, the desired lower bound below would already be trivial.

Consequently root counting in (5) proves

    d >= J(b-1)/2.                             (6)

This is the reduced degree of the ACTUAL fixed-start tag ratio, not merely the degree of the full unnormalized product. It applies to all three c choices and already permits cancellation of any common factors. Thus finite-window rational interpolation or continued-fraction reduction of this particular variable-start block readout cannot uniformly reduce a long block to degree O(J) in regime (2).

This is an obstruction to EXPANDING/INTERPOLATING THAT RATIONAL BLOCK, not to its evaluation at one supplied scalar, all arithmetic circuits, another nonlinear representation, or the full sixth-rate goal. A sparse/factored descriptor or a different non-polynomial representation could avoid outputting these coefficients. No lower bound on such alternatives is claimed.

## 5. Continued fractions and superposition: exact singularity contract

In the simple chart t=P/V, one has t'=f*t/(f+v*t). The known particular solution t=0 linearizes the reciprocal to

    1/t'=1/t+v/f

only on its legitimate unit chart. At a hit f=0 this expression has the very pole carrying the selected row. The tagged coordinate similarly needs u/f. These finite rational sums are not initialized endpoints merely because t=0 is an elementary particular solution. The block continuation that retains their common zero-safe denominator is exactly (1).

Rechecked the primary [Penskoi–Winternitz, Discrete matrix Riccati equations with superposition formulas](https://arxiv.org/html/math-ph/0305053), Theorem 2, Theorem 3 and Theorem 4. The projective fractional-linear realization uses a supplied invertible homogeneous matrix; the integer-time theorem assumes every one-step matrix nondegenerate, and the q-analytic theorem uses a specified holomorphic/meromorphic complex class and |q|!=1. It is not a finite-ring fast-advancement theorem. Independent particular solutions are inputs, not short initial values alone.

The finite failure at our collision is explicit: T(X_I) has f_I=0 and rank ONE. It maps any state with P!=0 to the same projective reset (0,1,w_*), while every known fixed-line state (0,V,U) is sent to the zero vector. Thus reconstructing a projective automorphism from independent particular solutions or cross ratios is not licensed across that hit. Clearing such superposition equations is allowed but does not justify dividing by the collapsed differences. The raw triple in (1) preserves the selected tag without any such division.

This does not disprove a singularly regularized superposition algorithm with a paid certificate; it identifies the exact extra work that the quoted invertible-group theorem does not provide.

## Result

The initialization is fully paid, including a unit increment. The commuting block law is fully initialized and has the old soft K^(3/2) fallback. The new native degree test shows that common-factor normalization, state-specific rational interpolation and ordinary continued-fraction compression of this variable-start block cannot give a bounded-degree shortcut on prepared inputs satisfying (2), including the stated balanced regime. No faster projective advancement was obtained. A successful next algorithm must evaluate the selected ratio without expanding (3), or use a different interval-sensitive representation while retaining the collision reset; constant-rank closure or invertible superposition alone supplies neither.

### Sharpening of the scoped balanced branch

On any prepared branch with P>=c0*K³ for a fixed c0>0, choose a fixed 0<eta<6c0 and b=floor(eta*K). For sufficiently large K, condition (2) holds (equivalently 6P>Hb), and b<=h. With J=phi(K)=K/3, bound (6) is then Omega(K²). Thus even the fixed-start tag ratio for a length-Theta(K) block cannot be output as a dense bounded-degree rational representation in soft K. At the old optimal b=Theta(sqrt K), the same bound is Omega(K^(3/2)). This remains conditional on the actual prepared balanced-size branch; it neither forces controller continuation nor bounds evaluation circuits or other compressed forms.
