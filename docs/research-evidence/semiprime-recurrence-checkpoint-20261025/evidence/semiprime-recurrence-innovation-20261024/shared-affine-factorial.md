# Shared affine factorial: executed menu and Euclidean-fold test

23 October 2026. Scratch only. No soft-m aggregate or exponent below
m^1.5 was obtained from this attempt. The scalar menu is actually
initialized, and the proposed double-factorial cancellation is tested
with its full integer carries. No scalar-output lower bound is asserted.

## 1. Paid scalar and complete-menu computation

Use the prepared source of `complementary-linear-channel.md`, SHA256
`c623ae1dfc05000ab46fea3f48247764160e579d35e17407b9edd592316a6ec9`,
in `/tmp/semiprime-residue-construction-20261023/`.
Set H=m^2 and

    c_j=m b_j-a_j j,
    T_j(h)=c_j+m a_j h,
    G(K)=prod_(j=1)^(m-1) prod_(h=0)^(m-1)(T_j(h)+H K).

The m,a_j and eta_j=m a_j are certified units modulo N. With
`z_j=c_j/eta_j` and `v_j=m/a_j` in Z/N, the exact scalar formula is

    G(K)=prod_j eta_j^m B_m(z_j+v_j K),
    B_m(X)=prod_(h=0)^(m-1)(X+h).                           (1)

Construct B_m by a product tree, acquire the m-1 shifted nodes, apply
monic MPE, and multiply. This executes any scalar K in soft m operations,
with the usual residue-bit factor. No difference between evaluation
nodes or B_m-value is inverted. The same procedure handles row and
h restrictions, so a nonunit scalar G(K) has paid soft-m localization.

The full known menu is -m-2<=K<=m+2, with 2m+5 labels. Enumerating all
scalar calls costs soft m^2 with soft m active storage. Alternatively
one batched MPE on the explicit O(m^2) shifted nodes has that same soft
bound and returns all values. This is an executed upper bound, not a
claim that scalar aggregation needs those values. Constructing the
degree-m(m-1) polynomial G itself has not been supplied at a smaller
cost and is not treated as acquired input.

## 2. Coverage and every nonunit branch remain lawful

The earlier bijection `(j,h)->T_j(h) mod H` covers H-units once, and the
supplied menu represents P among the lifted integers after clipping to
16H<n<=floor(sqrt N). Thus the UNCLIPPED box in (1) also covers P; it
need not invert or divide away a clipped complementary product.

All these additional leaves are safe for gcd localization. For every
integer K in the menu,

    T_j(h)+H K = -N/j mod m !=0,
    |T_j(h)+H K| < 2m^3+(5/2)H < N.                      (2)

The hard branch N>256m^4, m>=17 makes the final bound immediate from
the source envelope. Consequently no leaf is literally zero or a
multiple of N; every nonunit leaf yields a proper factor. A product gcd
equal to N requires descent, not an annihilator assumption. Enumerating
the menu using (1) is therefore a complete factor search, but costs
soft m^2 in its worst-case ledger. No earlier-stop bound is proved.

For the factor-only objective, the covering CLIPPED subset has an old
faster acquisition: its product is exactly the integer factor-interval
factorial with m-multiples removed. Acquiring that product and its
localization costs soft m^1.5. This does not compute the entire uncut
box norm G-menu, but it is already a sufficient covered factor query.
No new exponent is claimed for that fallback.

## 3. Concrete Euclidean/multiple-factorial cancellation attempt

For one row write a=a_j, c=c_j. A potentially useful period block has
h in [0,m) and K=K0+k with k in [0,a). Its leaves are

    c'=c+H K0,
    c'+m(a h+m k).                                       (3)

Since gcd(a,m)=1, the map `(h,k)->a h+m k mod(a m)` is a bijection onto
all a m residue classes. Indeed reduction modulo m fixes h, and
reduction modulo a fixes k. This is precisely where a multiplication-
formula or Euclidean folding might have converted the whole rectangle
to one rising factorial.

But the actual integer a h+m k lies in [0,2a m-a-m], not just [0,a m).
Writing r for its residue modulo a m therefore gives the exact form

    a h+m k=r+a m epsilon_r,   epsilon_r in {0,1}.

The rectangle norm is thus

    prod_(0<=r<a m)(c'+m r+m^2 a epsilon_r).                (4)

The epsilon mask is public and determined by a,m, but it is a genuine
integer carry. Replacing (4) by the single factorial
`prod_(r<a m)(c'+m r)` discards the shift m^2 a at every carried residue.
That shift is not zero modulo N. Formal gamma or double-gamma notation
does not evaluate this correction.

For clarity, the attempted cancellation would require the ratio

    prod_(epsilon_r=1)(c'+m(r+a m))
       /prod_(epsilon_r=1)(c'+m r).                        (5)

Its denominator is not promised a unit. If it were acquired and a
proper gcd appeared, that would finish factoring; if it is a unit,
division is legal. But the carry-subset products have not been acquired
in soft m across all rows. Neither the known residue permutation nor
Euclidean metadata supplies their values. This is the exact stopping
point of this cancellation proposal, not a claim against other
reciprocity identities or implicit norm algorithms.

Completing whole row intervals instead of retaining the mask produces
ordinary arithmetic-progression overcovers of length O(m^2) per row.
Their common-step factorial evaluation falls back to the inherited
soft m^1.5 many-target/long-interval scale, or the explicit global
integer factorial cover above. It does not establish the requested
sub-m^1.5 aggregate. No inverse of the unacquired carry products is
used in either executed algorithm.

## Outcome and bit ledger

Acquired: O(m) row metadata, B_m, one scalar G(K) and its factor
localization in soft m; the full scalar menu by direct batching in soft
m^2; and the already-known sufficient clipped factor query in soft
m^1.5. Integer leaves remain nonzero and strictly smaller than N.
All displayed exponents have O(log N) bits and residue operation costs
add soft log N. Full exact integer gamma values are never constructed.

Still missing: a shared acquisition of the carry-corrected complete
menu, or a smaller N-dependent menu with proved coverage, at soft m
or rigorously below m^1.5. None is asserted here. No examples, external
algorithm oracle, backend, repository edit, general lower bound or
new all-input factoring rate is used.
