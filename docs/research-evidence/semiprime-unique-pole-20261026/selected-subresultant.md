# Selected subresultant attempt: two companion cofactors and an exact scalar update

26 October 2026. Paper-only initialized elimination experiment. Read the authoritative [unique weighted packet](../semiprime-unique-weighted-20261026/README.md), including unique-cover.md and unique-lambert.md. No repository changes, code, tests or numerical campaign.

**Positive selected target:** whole-bin uniqueness guarantees that TWO specified coefficients of one companion-adjugate column give a useful locator, with no random projection or empty gate. A completely explicit division-free q-clock update is derived below, and its two selected-coordinate recurrences identify the exact remaining scalar prefix evaluation. Section 6 additionally derives a division-free SCALAR recurrence of order J with paid soft-J initialization and an exact two-consecutive-value locator. Its present execution costs soft(Jh); the known joint completion costs soft(J+sqrt(Jh)). No soft-K selected elimination is obtained, and the two cofactors are not falsely identified with the exact canonical first-subresultant coefficients.

## 1. Actual finite input and source credit

Let D(X)=product_j(X-T_j) be the acquired monic row polynomial, degree J<=K/3, and W_t(X)=product_(i<t)(X-q^i), with the harmless inverse-clock convention absorbed into q and T consistently. More explicitly one may take clock a_i=rho^{-i} throughout below, so a_i=q^i, exactly as unique-lambert.md. Their finite length is h=O(K^(3/2)).

At the good nonsplit field in a correct bin there is EXACTLY ONE common leaf, theta=T_j*=q^I. Hence D has a SIMPLE root at theta, W_h has a simple root there, and they have no other common root. D may repeat at other roots. This is the new native hypothesis actually used.

Primary structured context: Barnett, [A Note on the Bezoutian Matrix](https://doi.org/10.1137/0122009), establishes the companion/Bézout relationship; Heinig–Rost, [Bezoutians, Theorem 6.2 and §6.3](https://www.tu-chemnitz.de/mathematik/preprint/2008/PREPRINT_09.pdf), provides its functional-calculus formulation. Their matrix convention is not silently imported: the identities and source vector below are derived with our column companion. The primary theory is over a field; polynomial identities are cleared before application to B.

The older [16 October literature audit §3](../semiprime-descent-query-20261016/reports/literature-audit.md) already audits Moroz–Schost truncated resultants on supplied polynomial inputs. The Tal factorial specialization was also audited in the direct packet. Neither is reused as an implicit-clock oracle here.

## 2. Exact two-scalar locator, no arbitrary projection

Let C be the COLUMN companion: multiplication by X on E=B[X]/D, represented in basis 1,X,...,X^{J-1}. Put e0=1 and

    M_t=W_t(C), v_t=adj(M_t)e0.                 (1)

The matrix in (1) is NOT declared acquired; this defines the selected operation to be executed. Its final vector need not be emitted.

At the good field, E splits as the simple theta factor and the remaining algebra, on which W_h is invertible. Therefore adj(M_h)e0 is nonzero and equals

    v_h(X)=lambda*D(X)/(X-theta), lambda!=0.     (2)

The input e0 is guaranteed to project nontrivially onto the simple factor because evaluation of 1 at theta is one. No unknown eigenvector/random starting vector is supplied. This remains true when the other factor of D is nonreduced: W_h is invertible there and its determinant is nonzero.

Write D=X^J+d_(J-1)X^(J-1)+... and let A=[X^(J-1)]v_h, Vnext=[X^(J-2)]v_h. Then

    A=lambda!=0,
    B=d_(J-1)*A-Vnext=-lambda*theta,
    theta=-B/A.                                (3)

Thus only TWO selected coefficients suffice. At the good field (A,B) is projectively equivalent to the canonical first subresultant aX+b, since both are nonzero linear polynomials with root theta. It is NOT asserted to be that canonical coefficient pair numerically over B or in wrong bins. If J=1, use the sole acquired row/tag with the covered correct-bin consumer instead of a nonexistent second vector coefficient.

Norm-test A: proper gcd factors, unit norm licenses the ratio, saturated norm declines an unpromised attempt. At the correct bin it cannot be saturated. Evaluate the acquired weighted cofactor H_u and D' at theta; D'(theta)!=0 at the good field because the unique ROW there is simple. Its second inverse is proper-factor-or-unit on that branch. The standard bounded scalar/tag/HH validator costs soft K. No P0/empty gate is necessary for the correct BIN promise, but wrong-bin outputs remain bounded checked attempts.

## 3. Execute every q-step without an inverse or long remainder oracle

For a supplied a define the acquired degree-(J-1) polynomial

    Q_a(X)=(D(X)-D(a))/(X-a).

This is synthetic division by a monic linear factor, never inversion of a cross difference. The exact matrix identity is

    adj(C-aI)=(-1)^(J+1)*Q_a(C).                (4)

Indeed (C-aI)Q_a(C)=-D(a)I, and det(C-aI)=(-1)^J D(a); clearing proves (4) at zeros as well. Since all companion factors commute, adjugate multiplicativity gives the fully initialized recurrence

    v_0=e0,
    v_(t+1)=sigma*Q_(a_t)(C)v_t, sigma=(-1)^(J+1),
    a_t=q^t, 0<=t<h.                           (5)

Building Q_(a_t), multiplying modulo monic D and advancing a_t all cost soft J per step. All state vectors and powers have actual supplied coefficients; no field inversion appears. This executes (1) in soft(Jh) ring work, or K^(5/2) at the native scales. It is slower than the inherited engine, but it is an actual selected-elimination algorithm rather than an adjugate descriptor.

### The two-coordinate update exposes one unacquired scalar

For ANY degree-<J vector polynomial v, write r=Q_a*v mod D. Exact coefficient comparison gives

    [X^(J-1)]r=v(a),
    [X^(J-2)]r=(a+d_(J-1))*v(a)-D(a)*[X^(J-1)]v. (6)

One proof uses (X-a)r+D(a)v=([X^(J-1)]r)D; its value at a and coefficient X^(J-1) give the formulas as universal cleared identities. Thus keeping only the top TWO output coordinates of (5) requires precisely the scalar

    eta_t=v_t(a_t).                             (7)

After the unique singular step the vector is proportional to D/(X-theta), and (6)'s projective root freezes at theta. This does not locate the singular step or acquire (7) beforehand. Prefix top coefficients can vanish even though the FINAL A is nonzero, so a normalized projective iteration may not divide them without actual gates. Additive prefix-pivot zeros have no generic annihilator decoder.

The source-specific missing operation is evaluation of these actual evolving cofactor prefixes at the NEXT geometric clock node, not computation of a full determinant as an output. Whole-bin uniqueness removes the final projection degeneracy but does not by itself provide a cost-saving formula for eta_t. Section 6 supplies an actual initialized order-J scalar closure. No claim is made that every use of (6) must emit v_t; the executed recurrence does so, and a new closure for (7) could improve it.

## 4. Bézout/displacement attempt and its exact input

Let B0 be the coefficient matrix of (D(X)-D(Y))/(X-Y). It is anti-triangular with anti-diagonal one, hence determinant a known sign and no root-separation premise. Our column convention gives

    Bez(D,R)=R(C)*B0=B0*R(C^t).                 (8)

Multiplying R by X and reducing modulo D verifies this identity directly; it is the Barnett relationship in the correct orientation. For R=W_h modulo D it gives the J-by-J structured elimination matrix whose rank is J-1 at the good field. Selected minors/adjugate contractions can therefore recover the root.

However its displacement generators include the actual polynomial R, or equivalently W_h(C)e0. The q-clock factors give a compact sequence of operators, but not numeric final generators. Calling a superfast structured inverse/minor routine with those generators supplied would assume the missing long operation. In a singular routine, its necessary unit pivots must additionally be tested; the native good-field rank defect alone is not a global field-gcd oracle.

A COMPLETE faster fallback is to acquire R by the inherited division-free shared engine, then run the already licensed guarded half-GCD/subresultant algorithm and its norm/coordinate branch handling. That cost is soft(J+sqrt(Jh)). The alternative determinant-gradient completion uses the same row values with first variations. Neither is counted as a new algorithm here. Emitting all h q-binomial coefficients first costs soft h and does not improve that bill.

## 5. What uniqueness changes, and what remains unpaid

It guarantees a canonical first subresultant of degree one with nonzero leading coefficient; it also guarantees the explicit cyclic-source companion column (2) has nonzero top coefficient. Thus final selected coefficients or first variations are sufficient WITHOUT an empty gate. It does not require global root separation or nonsplit orientation advice. These are actual native improvements over a many-hit or block-with-empty-input promise.

The tested companion recurrence avoids assuming all W_h modulo D as an input, but its initialized cost is Jh. Selecting its top two coordinates leaves the exact scalar prefix values (7); the Barnett small matrix leaves the exact final generator R. Neither output simplification initializes the respective input. A cheaper computation of the two canonical coefficients, the equivalent pair (3), or the actual eta_t closure would be a genuine acquisition advance. None is proved here; no generic lower bound or new sixth-rate result is asserted.

## 6. Constructive scalar closure: order J, with paid initial data

The selected prefix values DO admit a completely initialized scalar recurrence, but its order grows with the supplied row polynomial. This sharpens the earlier vector-cost test and is the strongest scalar closure obtained in this pass.

For a proof on the regular universal locus define tau_(n+1)=product_(i=0)^n D(a_i) and let F_n be the ordinary divided difference

    F_n=[a_0,...,a_n](1/D), a_n=q^n.

The polynomial identity W_n*v_n=det(W_n(C))+D*Q gives

    eta_n=(-1)^(J*n)*tau_(n+1)*F_n.

Indeed Q is minus the norm times the degree-<n interpolant of 1/D on the first n nodes; evaluating at the next node gives its Newton interpolation error. Put

    E_n=tau_(n+1)*F_n=(-1)^(J*n)*eta_n.         (9)

These normalized quantities extend polynomially through a clock hit, as the following division-free recurrence shows.

Let

    B_k(a_n)=D[a_(n-k),...,a_n]
       =sum_(r=k)^J d_r*q^(-k*(r-k))*a_n^(r-k)*[r choose k]_q.

Here d_J=1. For n>=1,

    E_0=1,
    E_n=-sum_(k=1)^min(J,n) B_k(a_n)
          *[product_(i=n-k+1)^(n-1)D(a_i)]*E_(n-k). (10)

Every product with an empty range is one. Derivation: multiplication by X on Newton basis W_t sends W_t to W_(t+1)+a_t W_t. The equation D(X)*(1/D(X))=1 therefore gives

    D(a_n)F_n+sum_(k>=1) B_k(a_n)*F_(n-k)=0.

Multiplying by tau_n clears every D(a_i) inverse and yields (10). Its coefficients are polynomial expressions, so it remains valid over B even when D(a_I) is zero or a zero divisor. No singular scalar normalization is performed in the actual iteration.

### Paid initialization and per-step coefficient acquisition

If h<=J, evaluate D at ALL h clock nodes in soft(J+h) and use the covered clock root directly; this bounded case needs no recurrence. Otherwise evaluate D at the first J geometric nodes by ordinary monic MPE, soft J. A proper norm gcd factors. A saturated value on a correct attempt already identifies a clock root a_i and gives the known short cofactor/tag consumer; it need not be inverted. Wrong unpromised failures may be declined. If all values are units, batch-invert and perform geometric Newton conversion of the values 1/D(a_i), yielding F_0,...,F_(J-1) and E_0,...,E_(J-1) in soft J. Node differences involve only q powers with index gaps <J and are actual supplied units. Fast geometric conversion is the previously used finite machinery of [Bostan–Schost, Polynomial evaluation and interpolation on special sets of points](https://cs.uwaterloo.ca/~eschost/publications/BostanSchost.pdf); no new point-separation promise is imported. This is a concrete initialized prefix, not an arbitrary initial-condition oracle.

At any next n, the complete vector B_0,...,B_J is the Newton coefficient vector of the known D in the reverse geometric node order a_n,a_(n-1),.... It is acquired by the already used fast geometric Newton conversion in soft J; its only denominator differences have index gaps <=J. Short products of the previous J scalar D(a_i) values and the dot product in (10) cost soft J. Direct D(a_n) evaluation also fits that per-step cost. Thus (10) is an exact scalar algorithm with O(J) stored state, soft-J setup and soft(Jh) execution, without storing an h-entry clock or a J-by-J matrix.

### Only two final scalar values are needed

Combining (6),(9) with the companion sign sigma gives the particularly simple final locator

    theta=a_(h-1)+D(a_(h-1))*E_(h-2)/E_(h-1).  (11)

At the good unique hit E_(h-1) is nonzero by (2), so its norm gate is proper-factor-or-unit there. Earlier E_n need NOT be units, and (10) never divides by them. Formula (11) is therefore a legitimate whole-bin gate-free weak locator after its ONE final denominator check. It is not an assumed Riccati iteration valid through arbitrary prefix zeros.

### Test the small Riccati/Painleve truncation explicitly

For J>2, this recurrence is not a supplied two-state Riccati closure: its tail is

    -sum_(k=3)^J B_k(a_n)
        *product_(i=n-k+1)^(n-1)D(a_i)*E_(n-k). (12)

The last coefficient B_J is exactly ONE. Before the unique clock hit, every D(a_i) in that coefficient product is nonzero at the good field. Thus the literal order-J contribution is present in the ACTUAL native recurrence; uniqueness does not zero its coefficient. A claimed two-lag closure must supply another exact identity eliminating the correlated tail (12), rather than simply omit it. A Toda/Hirota condensation normally introduces neighbouring auxiliary minors; those minors have not been acquired as constant-size state here.

This is NOT a proof that the actual E_n cannot satisfy some different low-order nonlinear or q-Painleve equation, nor a fake-input counterexample to native structure. It identifies the precise tail in the executed initialized scalar closure. Solving (10) with a generic variable-coefficient recurrence theorem must charge growing order J, its polynomial degrees and the actual initialization above; constant-order complexity cannot be imported.

**Updated outcome:** no full W_h mod D is assumed by this scalar algorithm. Whole-bin uniqueness guarantees the two final values needed by (11) are a valid locator and removes projection/empty-gate problems. The actual recurrence and its finite initial data are paid, but its present cost is Jh; the inherited joint remainder/subresultant route remains K^(5/4). A faster evaluation of this particular scalar recurrence or a proved tail-elimination identity would be substantive progress. None is claimed here.
