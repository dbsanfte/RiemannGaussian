# A public nearest-lift interval selector and its whole-family cost

2026-10-23. Scratch only. **No uniform sixth-rate covered family or new
whole-query exponent is obtained.** One nearest-lift rule is executed
below without listing its m^2 label values. It contracts the complementary
rows into a chosen interval factorial in soft m. Covering the entire
factor range by this rule gives the old soft m^(3/2) algorithm after
shared blocking. The unacquired step is selecting a sufficiently small
collection of successful intervals from N.

## 1. Inputs and exact supplied-interval rule

Use the original prime m, H=m^2, N=PQ<=m^6, P<=Q, P,Q>16H,
and the acquired original a_j,b_j,ell_j. The immediate source is
`../semiprime-residue-construction-20261023/complementary-linear-channel.md`,
SHA256 `c623ae1dfc05000ab46fea3f48247764160e579d35e17407b9edd592316a6ec9`.
The uniform setup source is pinned there and retained unchanged.

For 1<=j<m and 0<=h<m write

    T_j(h)=m*(a_j*h+b_j)-a_j*j.

The already-proved map (j,h)->T_j(h) mod H is a bijection onto H-units:
the low digit is -N/j, and varying h adds m*a_j with a_j a unit mod m.
No hidden factor or own-tag selection is needed for that statement.

Let A be a SUPPLIED PUBLIC integer, with 16H<=A<=floor(sqrt N), and
consider the interval (A,A+H]. Define the integer lift, for every label,

    k_A(j,h)=floor((A-T_j(h))/H)+1,
    n_A(j,h)=T_j(h)+H*k_A(j,h).                    (1)

Then A<n_A<=A+H. It is the unique representative of T_j(h) mod H
in this interval. Consequently (j,h)->n_A(j,h) bijects the integers
in (A,A+H] prime to m. Replacing b_j by b_j+m*k_A is a valid native
coefficient lift at that label; it is not asserted to be a single shared
lift for all h in a row. Literal acquisition of these m^2 lifts would
cost m^2 and is NOT part of the algorithm below.

The interval automatically contains P if A<P<=A+H. The known relation
N=PQ does not tell us which such interval contains P, and (1) makes
no successful-interval assumption when its norm is evaluated.

## 2. The whole selected norm is actually acquired in soft m

The exact bijection proves the integer and hence modular identity

    product_(j,h) n_A(j,h)
      = product_(A<n<=A+H, m does not divide n) n.        (2)

This is more than a short circuit for a still-unacquired norm. Its right
side has the following initialized denominator-safe computation.

Build Q_m(X)=prod_(u=1)^m(X+u). Evaluate it by monic MPE at the m
starts A,A+m,...,A+(m-1)*m and multiply those values. The result is
the full interval product prod_(u=1)^H(A+u). Build/evaluate/multiply
costs soft m modular-bit operations, including all inputs; no differences
of evaluation points or interval leaves are inverted.

To remove the m-multiples let q0=floor(A/m). There are exactly m of
them, with product

    D_A=m^m * product_(u=1)^m(q0+u).              (3)

Here q0+u<=m^2+m<16H<P,Q. Thus D_A is a certified unit; its acquisition
and inversion cost soft m. Dividing the acquired full interval product
by D_A gives precisely (2). In contrast a quotient (A+H)!/A! would
not automatically be lawful when A! is nonunit; that quotient is not
used. All metadata in (1)--(3) are public polylog-bit integers.

If the norm is nonunit, use direct physical interval-product/gcd
localization. Every retained leaf n lies between 16H and
sqrt(N)+H<N on the hard branch, so a nonunit leaf has a proper gcd.
The sum of the square-root interval lengths on a single binary path is
O(sqrt H)=O(m), up to logarithms. Thus the selected interval's norm
AND its witnessed-factor recovery are actually soft m. No unknown k,
CRT factor, local order or subgroup inversion has been supplied.

The N-dependent row residues have canceled in this full-label norm:
they permute all unit representatives in the chosen interval. They are
essential to its label interpretation, but (2) supplies no preferred A.

## 3. What happens when this rule is made covering

Take A_t=16H+tH for consecutive t until these intervals cover
(16H,floor(sqrt N)]. There are

    B=ceil((floor(sqrt N)-16H)/H)

intervals when this difference is positive, and B=O(m), with B=Theta(m)
on the balanced scale. This is a completely public all-input family,
and the last interval may extend slightly past sqrt N without producing
zero or globally N-divisible leaves. At least one interval contains P.

Separate evaluation costs soft(B*m), at worst soft m^2. The familiar
shared-baby construction is better: for baby length b, build the common
degree-b interval polynomial, evaluate it at B*floor(H/b) block starts,
and use one additional polynomial of the COMMON tail length H mod b
at the B tail starts. It acquires all interval products in

    soft(b+B*H/b+B),

with no inverse at a zero leaf. Choosing b near sqrt(BH) gives
soft(sqrt(BH)+B), at most soft m^(3/2). The unit corrections (3) for
these consecutive intervals collectively cost at most that clock:
their inner ranges q0+1,...,q0+m concatenate into an ordinary prefix
of length O(m^2), whose interval block products cost soft m by the
same shared construction (baby size m, O(m) evaluations), and m^m
is common. Gcd localization retains the old soft m^(3/2) upper bound.

Equivalently one can compute one ordinary factor-range interval product
directly at this cost. This is the same factorial channel already paid
in the earlier report, not a second algorithmic gain.

## 4. Bounded outcome

Nearest representatives DO let a huge row-dependent lift table be
contracted without materializing it, for a supplied public factor-size
interval. A fixed or polylogarithmic number of these intervals would
fit soft m, but this pass supplies no rule, from N, which guarantees
one contains P or Q. Moving the center near sqrt N gives a genuinely
useful only-nearby factor interval; it has no all-semiprime coverage.
Dyadic factor-size bounds alone give intervals much wider than H.

The executed complete family above is uniform and covered, but its
best charged computation here is the old soft m^(3/2) one. This is not
a necessity theorem for interval queries or adaptive trees, nor a value-
count lower bound, nor evidence against a more arithmetic N-dependent
selector. It records a specific nearest-lift attempt and its exact cost;
the original soft-m acquisition goal remains open.
