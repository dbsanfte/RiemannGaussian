# Execute paired/AP elimination: paid comaximality, clock traces and sibling determinant

26 October 2026. Scratch finite derivation from the frozen paired-monic
and hybrid handoff. Pure K=2*3^e preparation is treated as licensed by
the current input; no new conductor-removal theorem is asserted here.
No code, tests, numerics, Lean or repository changes.

**Concrete paid advance:** regular A/B quadratics, and even the TWO
WHOLE root lists, can be certified cross-unit-separated in soft K or
a factor is returned. This acquires ordinary polynomial Bezout/CRT
projectors and cheap geometric-clock traces without the long correction
query. A cubic sibling determinant also cancels its unknown factor-
linear part exactly. Neither supplies the wanted cofactor readout:
the CRT projectors distinguish ROOTS, not arbitrary nonhit clock
points, and the sibling determinant does not determine its other
symmetric coefficients or its clock norm. The completed old monic
first-jet readout remains soft K^(3/2), weighted fallback K^(5/4).

## 1. Keep the exact paired data

From `semiprime-projective-readout-20261026/paired-monic.md`:
for A at j let a=[Nj^(-2)]_K and jstar=[N/j]_K. The paired B
row at jstar swaps (a,1) to (1,a), with the SAME centered ell.
Put

    cA=barpi^(a+N), cB=barpi^(1+aN), alpha=pi^ell,
    T=alpha+alpha^(-1), gamma=barpi^(N-1),
    PA(z)=1-cA*T*z+cA^2*z^2,
    PB(z)=1-cB*T*z+cB^2*z^2.

The exact identities are

    yB=yA*gamma^(a-1),
    cB*PA-cA*PB=(cB-cA)*(1-cA*cB*z^2).             (1)

Grouping j,-j uses each a once; the pure-modulus a-image is one
step6 AP and each a has exactly two tags. Remove the a=1 exceptions
only by their separately paid original one-row queries, a constant
number of tags. Their soft-K routing is prior credit. Thereafter
regular a is odd and >=3. The actual two-GP correction bank has
Theta(K) AP starts and clock lengthTheta(H); it is not covered by
itself and is not deleted numerically.

## 2. A cheaper gate than evaluating the whole correction bank

The degree-four resultant is explicit:

    Res_z(PA,PB)
       =(cA-cB)^2*(cA-cB*alpha^2)*(cA-cB*alpha^(-2))
       =(cA-cB)^2*((cA+cB)^2-cA*cB*T^2).          (2)

For example, substitute roots z=alpha^(-1)/cA and alpha/cA
of PA and include its leading coefficient cA^2 squared. This proves
(2) without inverses of specialized PA or PB values.

Each factor in (2), up to a supplied monomial unit, is a point
`1-pi^(+/-2ell)*barpi^L` or `1-barpi^L`, where
L=(a-1)(N-1). These actual points have known norm exponents
2*(L+/-2ell) or2L on beta. They are NONZERO integers:
L>=2(N-1) and |2ell|<=H, while N>256H^2. All have O(log N) bits.

Classify each factor in the quadratic algebra. A proper norm gcd
factors. At the nonsplit prime a zero norm means the WHOLE point is
zero, so a saturated norm with a nonglobal-zero point yields a proper
coordinate gcd. If the point is globally zero, its norm gives the
explicit nonzero beta annihilator just listed and the licensed T_ext
finishes. The O(K) short powers/values and classifications cost soft K,
with T_ext once on a terminating branch. On continuation every
resultant in (2) is a unit.

Thus PB is a UNIT at EVERY local root of PA, and conversely. In
particular at a useful PA clock hit, the remaining correction in (1)
is a unit because cB-cA and the monomial cA are units. This conclusion
does NOT require evaluating the length-H correction string. It is
strictly weaker than saying that correction is unit at every clock.
This is a completed extra interface from the actual paired family.

## 3. Stronger whole-list cross separation, still soft K

Let FA(X)=product_j(X-yA_j) and FB(X)=product_j(X-yB_j), after
the same regular a=1 routing. Their coefficients are already acquired.
Evaluate FB at ALL actual A roots by monic MPE, cost soft K, and
classify the product of their norms. On a nonunit, localize to one
A root and scan the O(K) B root differences. This is a legal
factor-or-unit gate, not an assumed generic discriminant premise.

For any A tag u and B tag v, the ratio yA_u/yB_v has scalar beta
norm exponent

    2*E_uv,
    E_uv=ell_u-ell_v+a_u-1-(a_v-1)*N.

It is nonzero: a_v>=3, |ell_u-ell_v|<=H and a_u<K, so
|E_uv|>=2N-H-K>0. Hence every saturated whole-point root equality
has a known short beta annihilator. If its norm is saturated but
its coordinates are not globally zero, the same nonsplit-field
argument gives a proper coordinate factor. Proper norm gcds finish
directly. Mixed local product zeros are localized before that decoder.
All ordinary and saturated branches are paid within soft K.

On the continuing branch ALL A/B cross differences are units. Thus
Res(FA,FB) is a unit, and the existing guarded FAST half-GCD/extended-
gcd interface acquires RA,RB in soft K with

    RA*FA+RB*FB=1.                                 (3)

No clock scan, useful-hit location or unknown order has been used.
The root points within each list need not be separated merely to
obtain (3); cross-resultant unit is sufficient for the polynomial gcd.
Its arithmetic pivot classifier returns a factor or certified inverse,
as in the frozen norm-sharing/implicit-evaluation Section2 interface.
Zero global coefficients are skipped; a nonglobal zero with saturated
norm is separated by coordinates at the nonsplit field. Unit resultant
alone is not being used to assume that every intermediate pivot is a unit.

This gives actual polynomial CRT projectors

    EA=RB*FB mod(FA*FB), EB=RA*FA mod(FA*FB),
    EA+EB=1,
    EA=1 at A roots, EA=0 at B roots.              (4)

Their coefficients and finite degrees O(K) are acquired, not formal
free inputs. The familiar scalar root-separation machinery is prior
credit; the new point of (2)-(4) is its licensed APPLICATION to the
paired monic lists with explicit nonzero saturated labels.

## 4. Execute the tempting cheap projector trace, and its exact mismatch

One can REALLY evaluate

    TA=sum_(i=0)^(2H) EA(q^i)

in soft K. Write EA(X)=sum_d e_d X^d and use

    sum_i(q^i)^d=(1-q^(d*(2H+1)))/(1-q^d), d>0.

Only d=O(K) denominators occur, so the original short guard certifies
them; the long numerators are multiplied, not inverted. Powers and
one coefficient contraction acquire TA at target cost. Analogous
linear clock statistics of any acquired O(K)-degree numerator are
available. This is a paid possible input, not merely a low-rank diagram.

But (4) is a root selector, NOT an indicator of all clock nodes:
at an ordinary clock point x with FA(x)FB(x)!=0 it generally takes
an arbitrary field value, not zero. Therefore TA includes every
nonhit clock contribution. The actual one-defect observable is

    sum_i EA(q^i)*product_(r!=i)FA(q^r),           (5)

or its row-tag refinement. At the promised A hit, (5) has the correct
one survivor and EA=1. Bare TA does not have that complementary
product. No exact identity cancels all its nonhit terms or proves
its scalar/tag value from the single good hit. We do NOT infer that
TA always fails on attained native inputs; only that this proposed
projector-to-locator implication has not been established.

There is another precise trap: cross separation says the spectra
FA and FB are disjoint, so FB(q^I_A) is a unit at A's hit. It does
NOT certify the ENTIRE product_i FB(q^i) a unit; the wrong family
may hit other clock indices. Multiplying both families and taking
one first derivative can then annihilate the good A first variation
by the other family's zero norm. A separate marker/leading-slice
or a new singular solve is required. Inverting the whole B norm
would simply request the original missing query.

The old reset state for P,V,U, or the cleared Stein solve in the
coefficient-forms packet, still initializes (5) at soft K^(3/2).
The new CRT data have not supplied that faster action. A concrete
future target is to combine (4) and the acquired short moment alphabet
with a collision-safe one-defect solver; no unit-denominator assertion
at a zero has been introduced here.

## 5. Physical-index nonalignment is stronger than a loose size warning

At the good A tag, aR=S modK. If a!=1, choose any prime power p^e||K
where v_p(a-1)=t<e. Then the colour congruence implies
v_p(S-R)=t, since R is a unit. Consequently

    v_p((a-1)*(S-R))=2t<2e.

Hence H does NOT divide the physical exponent difference
(a-1)(S-R) in the regular case. The paired B row therefore has no
INTEGER physical index at this SAME field whenever A has one.
Only modular aliases could put it on the chosen clock. This is an
actual native coefficient/phase fact, not a generic pair example.
The good-B case has the corresponding reversed statement.

This reinforces the provenance warning: the pair correspondence
jstar=N/j does not give TWO factor-tag first-jet ratios at the same
field. Integer tag complementation modulo n is performed only after
a valid readout; it is not an identity in characteristic R.

## 6. Execute the three-adic sibling determinant

Let delta0=K/3, e>=3, and use unwrapped colour lifts
j_s=j+s*delta0, s=0,1,2. The corresponding actual canonical A
coefficients satisfy

    a_s=a+delta0*k_s,
    k_s=-2s*a/j mod3.

For this algebraic identity retain the original acquired a=1 root as
an auxiliary entry if its separately queried exception cuts a triple.
There are only constantly many such boundary triples. This restores
the public three-root identity, not an uncomputed long value or an
inverse of a possibly zero query.

Retain the signed integers k_s from the true coefficient representatives;
their wrap carries are not discarded. Inverse expansion modulo H,
using delta0^3 divisible by H, gives

    ell_s-ell_0
      =delta0[-k_s*j+s*(N*j^(-2)-a)]
        -delta0^2[s*k_s+s^2*N*j^(-3)] modH.        (6)

The inverses in this congruence have precision H. At a factor lift
R=j+delta0*u, N*j^(-2)-a=K*v, the physical root-ratio exponent is

    (a_s-a)R+ell_s-ell_0
      =delta0^2[k_s*u+3s*v-s*k_s-s^2*N*j^(-3)]
                                                  modH.  (7)

Thus qprime=pi^(H/9) really aligns these ratios conditionally on the
coarse factor colour, but the individual exponent still includes u.
It has not become an acquired short clock shift.

There IS an unconditional public cancellation. The three a_s are the
AP triple a_base,a_base+delta0,a_base+2delta0. Choose its MIDDLE
coefficient sibling c and use that row as reference. Then sum_s a_s=3a_c,
and exact multiplication of the acquired roots gives

    product_s y_s=y_c^3*pi^(sum_s ell_s-3ell_c)
                  =y_c^3*qprime^L,
    L=(sum_s ell_s-3ell_c)/(H/9), |L|<=27.         (8)

Integrality is UNCONDITIONAL and follows directly by summing (6)
and subtracting three times its equation for the middle-coefficient
sibling c: sum_s k_s-3k_c=0, so the potentially nondivisible
term -delta0*j*(sum k_s-3k_c) vanishes. The other first-order
term contains N*j^(-2)-a=K*v=3delta0*v, and every remaining
term is already a multiple of delta0^2=H/9. No actual factor R,
compatible factor lift, or existence assumption is needed. The
resulting divisibility is a public identity from acquired phases. Centering only changes L by multiples
of9. The unknown linear R term genuinely disappears in this cubic
DETERMINANT. Equation(8) is exact globally, not just at the hidden field.

However the three-root polynomial also needs its first and second
symmetric coefficients. They are acquired from the three actual roots,
but (8) does not determine them from y_c and a fixed unit. Explicitly
the two noncentral ratios form a reciprocal pair with known product
qprime^L and unknown factor-lift dependence individually; this is not
a cubic root-of-unity orbit. Retaining those coefficients gives one
cubic block per triple and total polynomial degree stillTheta(K).
No finite-q multiplication theorem evaluated its long clock norm here.
Thus a real finite fusion constraint was obtained, not a claim that a
cheap determinant of three roots computes their collision product.

## Outcome and next initialized datum

The strongest completed operations are (2)-(4): soft-K pair/whole-list
cross-unit certificates, acquired Bezout projectors, and their genuinely
cheap geometric-clock linear statistics. The sibling identity (8) is
an additional exact short normalization independent of the unknown
factor lift. None identifies a useful factor tag by itself.

To finish the desired hybrid one needs an initialized one-defect or
singular-linear solve using these projectors/moments, or a three-adic
composition that determines MORE than the cubic determinant while
retaining the collision zeros. The remaining correction bank is not
deleted or declared covered; whole-family fallback and all old paid
normalizers remain available. No general impossibility or new exponent
is claimed.
