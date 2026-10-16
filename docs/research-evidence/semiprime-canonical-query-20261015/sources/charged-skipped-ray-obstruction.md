# Charged skipped rays: an amended paid family and full-height commensurability obstruction

Classical arithmetic proof, 2026-10-08. This report does not change any
previous source, proof or audit. Its arithmetic input is the frozen complete
Euclidean all-hit theorem, together with the elementary charge budget below.
No examples, additional density conjecture or new native backend are used.

## 1. The new catalog has a paid soft-linear budget

For an odd prime `m`, define the SET

    D_m={ (s*e*r,e*y): s in {-1,1}, r,y,e positive integers,
                         r*y*e<m }.                         (S1)

Its integer-triple occurrence count is bounded by

    2 sum_(r,y>=1) floor((m-1)/(r*y))
      <=2(m-1) (sum_(r<=m-1) 1/r)^2
      <=2m(1+log m)^2.                                     (S2)

Deduplicating can only reduce this count. Every member has
`0<|a|<m` and `0<t<m`, so both coordinates are units modulo `m^2`.
The catalog can be enumerated in soft `O(m)` work by the bounded nested
ranges `r<m`, `y<=floor((m-1)/r)`, `e<=floor((m-1)/(r*y))`.
The loop counts, including their outer prefixes, obey the same harmonic
bound. This is not an enumeration of the full quadratic coordinate box.

Let `C_m` be the preserved universal SET of all actual Euclidean rays.
The new finite candidate universe `C_m union D_m` still has soft `O(m)`
members, uniformly in the entire input state.

For an actual `N` coprime to `m`, turn a candidate `(a,t)` into actual rows
only at its legal public tags, namely

    a = (N*j^(-2))*t mod m.                                 (S3)

At each matching unit tag use the literal public inverse and `liftRow`.
There are at most two matching tags, since `j^2=N*t/a mod m` and `a` is
a unit. A deterministic sorted table of actual `quotientSlope N m j % m`
for all unit tags, followed by `a/t mod m` lookup, gives soft `O(m)` total
construction, including inverse computation, duplicate occurrences, all
applicable source center types and full-N centered lifts. No nonsquare
witness, hidden factor or hidden period is supplied to that construction.

## 2. The amended family still misses every stated local hit

The complete Euclidean proof in
`full-euclid-all-hit-obstruction.md` uses its universal catalog only through
the following properties:

1. It is an input-independent SET of soft `O(m)` integer coordinate pairs.
2. Every pair satisfies `0<|a|<m`, `0<t<m`.
3. A retained row is the exact legal full-N lift at a public unit tag.
4. The tested indices lie within width `W=O(m log^B m)`, for fixed `B`,
   of the literal public/reflected rectangle centers, positive stationary
   center, or negative cancellation center.

All four properties hold for `C_m union D_m`. The source hit polynomial,
two-tag gate, false-tag carry/input-state uniqueness and own-tag integer
forcing need only the coordinate units; they do not require a primitive
ray or a particular Euclidean frame. The same original midpoint formula
holds for these signed coordinates, and `|beta|=O(m)` remains valid.

For completeness the resulting estimates are as follows. At fixed `P`,
partition its literal selector `Q` strip into half-open width-`m^2` boxes.
The centered multiplier function varies by `O(v)` in each box, with error
`O(v*(1+W/m))`. Each possible multiplier gives at most two tags; at a
false tag the exact lifted source fixes one `Q mod m^2`, hence one integer
per box. The count `P=1 mod v` cancels the cofactor `v`. Summing the SET
budget, all `v<=V=O(M^.969)` and the telescoping selector gaps gives

    all false-hit pairs = soft O(V*M^5)=soft O(M^5.969).      (S4)

At an own tag the same `m^2 | K+v*a` and
`|K+v*a|=O(V*m)=o(m^2)` force the exact original true index.
The SET shell bounds are unchanged:

    sum_(0<a<=C*t) t^(-1/2)=soft O(m^(3/4)),
    sum_(0<|a|<=C*t) t^(-1)=soft O(m^(1/2)),
    sum (|a|+t)^(-1)=soft O(m^(1/2)).                       (S5)

For polylogarithmic tolerance `E=1+W/m`, the enlarged cone envelope is
`O(T^2+E*T)`, exactly as in the preserved E36 extension. The reversed
ray/prime interval count gives own stationary loss
`soft O(M^5.75+M^5.525)` and own rectangle/cancellation loss
`soft O(M^5.5+M^5.525)`. The literal `AB>1` rectangle discriminant gate
is unchanged for every signed candidate ray. These are smaller than (S4).

The SAME published actual prime-pair supply is `Omega(M^6/log^2 M)`.
Deleting all amended hit-containing pairs therefore leaves an infinite
actual balanced distinct-prime literal-selector family with the original
`longBase2` route and original projected `gamma`. In both hidden fields,
EVERY original residual of EVERY retained amended row in EVERY specified
window is nonzero. The same-tag deletion of order `O(M^5)` may be made;
no thinner auxiliary family is intersected.

The complete amended centered norm is classically acquired in soft `O(m)`
by exactly the preserved original target polynomial and monic multipoint
evaluation. It is a unit on this actual counterfamily. Thus this is a new
concrete charge-derived amended family with a false coverage contract,
not merely a state-only lattice gap. The full height-`m` coordinate box,
arbitrary new centers and long original intervals remain outside it.

## 3. Every within-frame skipped current ray is in the catalog

An actual nonterminal Euclidean frame has positive smaller remainder `r`,
positive current denominator `y`, and quotient `q=floor(r0/r)`.
Its determinant invariant gives

    r0*y+r*x=m,    r*y*q<=m.                               (S6)

For every `1<=e<q`, strict positivity and (S6) give `r*y*e<m`.
Consequently the scaled signed current

    (a_e,t_e)=e*(a1,t1)=(s*e*r,e*y)                         (S7)

is in `D_m`, has coordinates strictly smaller than `m`, and is legal at
the current's actual tag. This includes all differences between two
intermediate positions in that frame, at FULL source height. When `q=1`
there are no such skipped multiples; the separately emitted current is
already in `C_m`. No arbitrary difference between distinct frames or tags
is asserted to lie in `D_m`.

## 4. Exact full-N relift and source midpoint cocycle

Work at one actual tag `j`, with `alpha=gamma^(m^2)`. Let the current row
have centered coefficient `b1`, and write its uncentered target as

    x1=gamma^(t1*N+a1+m*b1-2*a1*j).

Let `A_int,B_int` be the literal integer sums of square roots appearing
in twice the rectangle midpoint; reflectedShift swaps them. These
coefficients are independent of the sign of `a`, because the source
lower/upper endpoint choices exchange before being added. Put

    H1=A_int*a1+B_int*t1+2*(m*b1-2*a1*j),
    D=2*m^2, z1=floor(H1/D), xi=H1/D-z1 in [0,1),
    eta=x1*alpha^(-z1).                                   (S8)

This is the preserved actual pure-stride normalization, not an auxiliary
root of unity. The centered coefficient of the literal scaled row (S7)
has the form `b_e=e*b1-m*B_e` for an integer `B_e`, because its exact
quotient numerator and inverse-centering residue are `e` times those
of the current. Its original target is `x1^e*alpha^(-B_e)`, and its
literal midpoint is

    kappa_e=floor((e*H1+m^2)/D)-B_e.

Thus its ACTUAL original centered target is exactly

    w_e=x1^e*alpha^(-floor((e*H1+m^2)/D)),
    eta^e=w_e*alpha^(h_e),
    h_e=floor(e*xi+1/2),    0<=h_e<=e.                    (S9)

The centered-b carry cancels against the source center after relifting.
There is no unknown offset, and the bound works for signed `H1`.

For original intermediate targets at positions `k<l`, put `e=l-k`.
The exact progression formula is

    y_k=x0*x1^k*alpha^(-floor((H0+k*H1)/D)).

The current midpoint convention is already included in `H0`. Comparing
the floor increment with the rounded midpoint in (S9) gives

    y_l/y_k=w_e*alpha^epsilon, epsilon in {-1,0,1}.         (S10)

Indeed if `e*H1/D=n+v` with integer `n` and `0<=v<1`, both the floor
increment and `floor(e*H1/D+1/2)` are `n` or `n+1`. This proves the
claim also when the original integer `H1` is negative.

## 5. Arithmetic exclusion of short full-frame mixed relations

On the amended actual counterfamily, the centered miss for its emitted
scaled row states, in BOTH hidden fields,

    w_e != alpha^r for every |r|<=W,    1<=e<q.             (S11)

Therefore (S9)--(S10) imply

    eta^e != alpha^d          for |d|<=W-e,
    eta^e != alpha^d          for |d|<=W-m,
    y_l/y_k != alpha^d        for |d|<=W-1.                 (S12)

The second bound is a convenient uniform weaker version. Width constants
or fixed polylogarithmic padding may be enlarged so that `W-m` has any
prescribed soft-linear size. The negative-half stride is
`eta_minus=eta*alpha^-1` with baby base `beta=alpha^-1`. It also has

    eta_minus^e != beta^d     for |d|<=W-m,                 (S13)

because `eta_minus^e=w_e*alpha^(h_e-e)` and `0<=e-h_e<=e`.

This is stronger than the original current-only alignment: ALL integer
advances inside a full-height frame are covered. It also closes the
earlier tall skipped-difference gap with an explicitly amended, paid
legal source rather than silently treating an un-emitted difference as
an original Euclidean row.

For a local field with exact prime alpha order `R`, let

    P_L(T)=product_(0<=i<L)(T-alpha^i), 2L<R.

The root-overlap criterion for `P_L(eta^e*T)` and `P_L(T)` is
`eta^e=alpha^d` with `|d|<=L-1`. Such a `d` is unique and the overlap
has `L-|d|` members. Otherwise there is no overlap. If `L>W-m`, (S12)
therefore makes both reduced rational-template degrees exceed `W-m`.
The corresponding statement holds for the ratio `y_l/y_k`, with degree
exceeding `W-1` when `L>W-1`, and for the negative-half base and stride
by (S13) under its corresponding length bound.

Consequently low-degree endpoint templates cannot be rescued by
skipping intermediate positions, blocking several positions at once,
or passing to the inverse baby base. More generally a folding that needs
a mixed relation `eta^e*alpha^d=1` with `1<=e<q` and `|d|<=W-m` has no
such relation in either hidden field on this actual family. This is an
arithmetic obstruction to that concrete short-commensurability mechanism.

The known common-gamma equality `eta^(m^2)=alpha^E`, when
`eta=gamma^E`, remains true. Its horizontal advance `m^2` lies far
outside `e<q<=m`; no short within-frame relation follows from it.
Integer Bezout relations among known exponents may likewise have large
advances or large vertical shifts. This proof does not forbid using
such relations with a separately priced algorithm.

## 6. Exact remaining rectangle question

The long scalar

    S(q,L;z,eta,alpha)=product_(0<=k<q,0<=i<L)
                                      (z*eta^k-alpha^i)

is still unpaid at the required whole-family bound. The new theorem
does NOT lower-bound arbitrary algorithms for that scalar, its value at
one supplied point, implicit high-degree circuits or additive observations.
It does not exclude special relations with large vertical shift, shifts
between different frames, right-endpoint observations or an efficient
non-transport evaluator. The separately emitted current singleton targets
remain part of the actual long query and cannot be omitted.

All prime supply and asymptotic counting above remain classical; the
finite native charge and hit/state lemmas are preserved rather than
replaced by analytic axioms. No full all-input factorization, saturation
recovery, native bit clock or peak-memory theorem is claimed.
