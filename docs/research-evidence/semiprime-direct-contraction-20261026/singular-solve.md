# Direct singular readout with separated rows and paired inverses

26 October 2026. Scratch paper derivation and primary-source audit. No repository edits, tests, code, numerical campaign or Lean. **No soft-K singular solver acquired.** A normalized Laurent-residue mask and an explicitly evaluated rank-one q-bispectral core are obtained as precise alternative interfaces; neither is counted as an acquired locator. The best complete weighted query remains soft K^(5/4), and the monic fallback soft K^(3/2).

Inputs read: frozen fast-projective README/separation and paired-contraction reports, coefficient-forms structured/combinatorial expressions, and the older Newton/quantum-torus boundary warnings. The missing-diagonal displacement and short-Prony failures are old credit and are not re-proved as new here.

## 1. Actually supplied operations

Work on a continuing good-family attempt after the paid derivative screen. Its root polynomial F=product_j(X-y_j) has globally unit root differences, J<=K; the tag interpolation W(y_j)=w_j is acquired. Put E=B[X]/F, a free rank-J algebra. Monic remainder arithmetic, multiplication by X and the known paired polynomial F_B are acquired. The whole-list cross gate certifies F_B(y_j) units, so F_B is a unit in E and its inverse is actually acquired by guarded fast extended gcd. Paired CRT projectors are likewise acquired.

At the nonsplit prime R this family has exactly one hit y_j*=q^I among 0<=I<h, h=2H+1. All physical q-clock differences are actual units. The other prime need not have unique hits. The static interpolation isomorphism E->B^J is paid; the list of LONG values G_h(y_j) is not assumed.

## 2. Normalize the singular solve by a Laurent residue

Let b(X)=F_B(X) modulo F (one can also use b=1). Introduce a formal variable delta and define the rational operator sum

    S(delta)=sum_(i=0)^(h-1)
                   [1-q^-i X+delta*b(X)]^-1.     (1)

After componentwise field decomposition, every summand has at most a SIMPLE pole at delta=0: b(y_j) is a unit, so a zero constant term gives exactly delta^-1/b(y_j); a nonzero constant term is regular. Therefore delta*S(delta) is regular at zero and

    Pi=b(X)*[delta^0](delta*S(delta)) in E        (2)

has values

    Pi(y_j)=1 if row j hits the clock, otherwise 0.

The clock-order guard ensures at most one hit per row, including every split component. Thus Pi²=Pi globally. Its traces

    V_norm=Trace_(E/B)(Pi), U_norm=Trace_(E/B)(W*Pi)      (3)

are actual local hit counts and tag sums; at the good field they are EXACTLY (1,w_j*). This removes any unknown multiplicative product amplitude from the desired output specification. It is not a computation of (2).

The formal inverse in (1) is justified by the finite product-of-fields decomposition and the uniform simple-pole bound. It is NOT an instruction to invert the constant coefficient when that coefficient is a nonunit. Mixed component hits can give a Laurent inverse whose leading coefficient is a zero divisor; ordinary Newton inversion from a unit delta-constant cannot be applied to it. Computing the required mixed-component idempotent is precisely part of the unsolved task. The paired inverse b is a legal preconditioner, but b=1 shows that this identity alone is not an acquisition gain from the new paired data.

### Initialized fallback and exact first unpaid operation

Acquire all R_j=G_h(y_j), G_h(T)=product_(i<h)(1-Tq^-i), by the old shared monic block engine in soft(J+sqrt(Jh)). Norm/coordinate classification of R_j either factors or makes each surviving row globally unit or globally zero, using the nonsplit field. In the no-factor case the 0/1 row flags are acquired and interpolated in soft J, giving Pi and (3). No whole-hit polynomial or high Hasse precision is needed by this fallback. On a saturated row one may instead finish with the already licensed one-row/HH tag route.

The precise potentially useful new primitive would extract the FIRST Laurent residue in (1) directly from supplied F,b,q,h at soft K, without constructing the long R_j list. Its pole order is bounded by one even with multiple hits at the other prime. A short-pole-order promise is not a free initialized Laurent inversion: the nonsingular constants/invariant subspaces of the individual terms are not supplied. No algorithm with the required cost was found.

## 3. Execute the normalized leaf equation and the paired preconditioner

The proposed normalized system is

    (1-y_j q^-i) Z_(j,i)=1-s, s=sum_(j,i)Z_(j,i).

At the good unique-hit field its zero equation forces s=1; every nonhit entry is zero, and the hit entry is one. Thus the desired tag is sum w_j Z_(j,i). At the GOOD UNIQUE-HIT field this is exactly the singular mask (2) in another basis. If another local component has multiple hits, this normalized system is underdetermined there, whereas (2) still specifies every per-row 0/1 flag; no global identification of those two systems is claimed.

Away from singularity the trace of its inverse reduces to

    sum_i 1/(z-y_j q^-i)
      =z^-1*[h-(y_j/z)G_h'(y_j/z)/G_h(y_j/z)].   (4)

Both ordinary and W-weighted contractions therefore request a finite q-Cauchy tail. At collision its pole residue is legal and useful, but it is not a known input value. Multiplying by the acquired b^-1 normalizes each row's coefficient; it does not compute the Laurent residue of that tail. All direct inversions must either be at certified units or remain formal with their singular extraction paid.

The new CRT data give a separate exact finite test. If E_A=R_B*F_B is the acquired root projector, then E_A/F_B=R_B is a POLYNOMIAL after symbolic cancellation. Treating that ratio as an inverse-companion clock filter supplies only an already acquired polynomial clock sum. Leaving F_B in the denominator creates possible poles at other clock nodes; cross separation does not certify its entire clock norm a unit. Alternatively E_A/(F_A F_B)=R_B/F_A keeps the desired A-root poles, but the finite sum over the clock is again a rational tail like (4), whose zero-mode residue has not been acquired. Thus these actual new inverse/projector data do not themselves implement a singular Schur complement.

## 4. New primary rank-one integrable test: compute the core explicitly

The primary [Gekhtman–Kasman, Integrable Systems and Rank One Conditions for Rectangular Matrices](https://arxiv.org/html/math-ph/0408038), equations (10)–(11), gives q-bispectral Baker–Akhiezer determinant quotients for specified rank-one pairs; Theorem 2.1 constructs KP/Hirota tau functions from supplied rectangular matrix data. It is a structural theorem, not an arithmetic complexity theorem or a finite-ring singular-solve algorithm. The following specialization computes the finite quotient explicitly and checks its actual normalization.

Write F(T)=T^J+sum_(r<J) f_r T^r. Let A be its multiplication/companion matrix and D=diag(1,q,...,q^(J-1)). Then

    D*A-q*A*D=u*e_last^t,
    u_r=(q^J-q^r)*f_r.

This is genuine acquired rank-one data. Under the source equation (11) with X_source=D,Z_source=A, its finite determinant quotient is

    det(q*A*D-x*A-z*D+x*z*I)
      /det(A*D-x*A-z*D+x*z*I).

Ignoring the common exponential formal background, apply the rank-one determinant identity with the numerator (D-xI)(A-zI)-u e_last^t and denominator (A-zI)(D-xI). On the actual unit-denominator locus the result is

    BA(x,z)=T_x(F)(z)/F(z),
    T_x(F)(z)=z^J+(q^J-x)*sum_(r<J) f_r*z^r/(q^r-x). (5)

The companion resolvent identity used here is e_last^t(A-zI)^-1 w=-w(z)/F(z), verified by polynomial division. Every matrix has been specified; no unknown row-factorial diagonal is imported.

Take x=q^h. All q^r-q^h, r<J, are actual units: 1<=h-r<=h<16H. Thus every coefficient of T_(q^h)(F) is ACQUIRED in soft J, with all powers and unit tests paid. Monic MPE even acquires its values at all y_j in soft J. This is a real cheap rank-one core, not an uncomputed determinant descriptor.

Its exact role is exposed by the identity

    (sigma_q-q^h)T_(q^h)(F)=(q^J-q^h)F,
    sigma_q P(z)=P(qz).                          (6)

It is a LINEAR polynomial q-antiderivative. At the desired common root theta=y_j*=q^I, equation (6) relates T(qtheta) and T(theta); it does not impose T(theta)=0 or return its row tag. The denominator F(z) in (5) vanishes at EVERY row root, irrespective of whether that root lies in the physical clock interval. Its residue denominator therefore identifies the already known row spectrum, not the sought intersection mask. New additive zeros of the numerator have no original beta-annihilator license. Only a proper norm/coordinate gcd is an immediate factor branch; no coverage is established for that optional screen.

The source's tau-function theorem does not identify (5) with (1), G_h(A), or its selected residue. Using Miwa factors on the A spectrum requests product_i(A-q^i), the original long input. Using the known short D spectrum instead changes the spectral problem and can introduce universal clock-overlap zeros; it does not retain the original collision divisor by theorem alone. This is not another proof of the older q-dilation/nonclosure observation: (5) explicitly acquires the strongest simple finite q-bispectral quotient for the present supplied pair and identifies the different scalar it computes.

Source scope: equations (5)–(6) are elementary cleared matrix/polynomial identities over the native ring, with only the displayed certified short units inverted. Evaluating (5) at a zero of F still requires residue/regularization; no complex-field tau proof is used to authorize that division. The primary Theorem 2.1 assumes its supplied complex matrix rank/nondegeneracy data; neither that theorem nor its existence of an integrable hierarchy is claimed as a modular initialization/evaluation theorem here.

## Result and next narrow task

The normalized residue mask (2) is a fixed-simple-pole singular target with exact good output (1,w_hit), not merely an arbitrary common amplitude. The paired inverse/root interpolation are legal inputs to it. The actual rank-one q-integrable core (5) is acquired cheaply, but computes (6), not that mask. The direct initialized mask/ratio completion still costs soft(J+sqrt(Jh)).

A useful next theorem would perform the Laurent-residue extraction in (1), or an equivalent normalized singular solve, from the acquired polynomial/paired data with its finite h boundary retained. Small pole order, a tau-function identity, an acquired short core or a root CRT projector is not by itself that algorithm. No general impossibility, fast whole-query result or sixth-exponent claim is made.
