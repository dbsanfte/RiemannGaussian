# Native Euclidean centers do not remove the geometric-carrier obstruction

2026-10-16. New classical arithmetic proof. It removes the earlier
polylogarithmic-relative-origin restriction for the actual publicShift
and reflectedShift centers, including all literal Euclidean intermediate
rays and higher-digit/factor-advised choices. A quantitative version also
covers arbitrary origin spans with an explicit wrap factor.

No nearlinear long-query algorithm, arithmetic-operation lower bound,
collision coverage after tag trimming, or Lean sixth-rate proof is
obtained. The obstruction is to a specified few-small-geometric-carrier
route. Other shared computations and implicit scalar algorithms remain
open. All qualified inputs, literal public bases and source/selector
premises below are inherited, rather than replaced by arbitrary nodes.

## 1. Source, light tags, and statement

Let m>=5 be an odd prime and n=N mod m nonzero. Deduplicate the triples
(j,a,t) from the native complete publicPairs source at all 1<=j<m.
Every current/intermediate pair satisfies

 0<|a|<m, 1<=t<m, a*j^2=n*t mod m.

The compiled packet budget bounds this triple set by 8mL_m^2, where
L_m=floor(log_2 m)+1. As in the frozen adaptive-Euclid proof, call tags
with more than C_m=64L_m^4 triples heavy and retain the others as light.
There are at least 2m/3 light tags. This coordinate catalog and the
light/heavy decision depend only on n, not on higher digits or centers.
Write C=C_m and R for the light catalog size; R<=Cm. The same argument
also applies to the primitive hyperbolic catalog with its stated
logarithmic per-tag bound and no heavy-tag removal.

For a triple r=(j,a,t), keep its exact native centered lift

 D_r=(N*t-a*j^2)/m,
 b_r=centered(m,-j^(-1)*D_r),
 delta_r=a+m*b_r-2*a*j.

This uses the signed a. It is periodic in N modulo d=m^2, and
|delta_r|<3d. Put S=P+Q-1 for actual N=P*Q. Our new raw quantity is

 E_mod(P,Q) = # ordered light-catalog quadruples with
             sum_signed(t*S+delta_r) = 0 mod d.          (1)

Unlike the preceding proof, we do NOT impose an integer t-sum equality.
We average both higher factor digits, and also the low factor residue
at fixed low product n. Over all ordered unit residue pairs modulo d
with P!=Q mod m, we prove

 sum E_mod(P,Q) <=10*C^4*m^(13/2).                       (2)

Thus at most 10m^4/lambda ordered factor-residue pairs have
E_mod>lambda*C^4*m^(5/2). The SAME original selector argument removes
O(K_*M^6/lambda) actual pairs, plus O(K_*M^5) for P=Q mod m. On the
retained original majority, the bound holds at every current m before
ANY advised row or center policy is chosen.

For the actual native public/reflected centers, every full-tag choice
of one current/intermediate row and either center at each tag has a
light selected MULTISET with at least 2m/3 labeled entries and weighted
GLOBAL multiplicative energy at most lambda*C^4*m^(5/2). Repeated values
are counted with their source multiplicity. Therefore every cover of
the COMPLETE chosen target family by k geometric progressions with
total listed length T satisfies

 k^2*T >= m^(3/2)/(162*lambda*C^4).                      (3)

The same cover obstruction holds for the full packet union containing
both centers and every intermediate ray, by choosing a light witness.
An energy bound for that entire untrimmed/multicenter union is not
asserted. No distinct-target lower bound J>=m/3 is used: the old proof
of that bound depended on integer t separation, which is absent here.

## 2. Inherited weighted cone energy

Write u=a*j in F_m. A row gives a point A_r=(a,t,u) on

 Q(a,t,u)=u^2-n*a*t=0.

Color the light triples into at most C colors, with at most one row
per tag in a color. Within a color, a!=0 and u/a=j give distinct cone
generators. The frozen polar/projective-incidence argument proves
E(A_color)<=4m^(5/2). Weighted convolution and Cauchy--Schwarz give

 E_cone <=4*C^4*m^(5/2),                                (4)

for the ENTIRE labeled light catalog. Duplicate field points across
colors are retained, not deduplicated. This exact source/weighted lemma
is already proved in the predecessor packet; its all-advice use below
is at the catalog level before a policy chooses rows.

## 3. Factor digits and the exact phase equation

Let p,q in {1,...,m-1} be the low factor residues, n=p*q mod m, and
s=p+q-1 mod m. Write the factor residues modulo d as

 P=p+m*U, Q=q+m*V, U,V in F_m.

If h_N,h_S are the next digits of N and S, respectively, then

 h_N = floor(p*q/m)+q*U+p*V mod m,
 h_S = floor((p+q-1)/m)+U+V mod m.

The affine map (U,V)->(h_N,h_S) has matrix [[q,p],[1,1]], determinant
q-p. It is a bijection exactly when p!=q. We exclude that singular
low-residue case separately, with the counted loss in section 6.

For fixed n and a catalog row, exact centering gives

 delta_r(n+m*h_N)=delta_r(n)-m*h_N*t/j mod d.

Also t/j=u/n modulo m. For a quadruple let Delta a, Delta t, Delta u
denote signed sums in F_m. Reducing (1) modulo m gives

 Delta a-2*Delta u+s*Delta t=0.                         (5)

If this low equation holds, the remaining high equation has the form

 kappa+Delta t*h_S-(Delta u/n)*h_N=0 mod m,              (6)

with kappa depending only on the low data and the chosen quadruple.
Its value is not required as algorithm input. The coordinate order in
(6) is explicit: h_S has coefficient Delta t, h_N has coefficient
-Delta u/n. With p!=q we count its solutions over all m^2 independent
higher-digit pairs. Row policies and origins have not entered this count.

## 4. Three cases give the whole residue-pair bound

Fix n and its R<=Cm light triples. Sum over low p!=q with q=n/p, and
over all higher digits. All catalog quadruples are ordered and labeled.

Case A: Delta t!=0. Equation (5) fixes s uniquely. The low factor p
then satisfies p^2-(s+1)p+n=0, with at most two possibilities. Equation
(6) is nonzero and admits exactly m higher-digit pairs. This case
contributes at most 2mR^4. We have averaged low p rather than assuming
that a single plane projection has a small fiber.

Case B: Delta t=0 and Delta u!=0. The low condition is now
Delta a-2*Delta u=0. Consider the projection

 A_r -> (t,a-2u) in F_m^2.

Every fiber of this map contains at most FOUR catalog triples. Indeed
fixed t (its integer representative 1<=t<m is unique) and v=a-2u give

 u^2-n*t*(v+2u)=0.

This monic quadratic has at most two u values. Each fixes a modulo m
and j=u/a, while a has at most two signed representatives in (-m,m).
Spurious roots with a=0 or j=0 are simply not catalog entries. The
catalog was deduplicated in (j,a,t), so no extra derivation labels are
counted in this fiber. Fixing three rows in an additive projected
quadruple thus leaves at most four fourth rows, for at most 4R^3
quadruples. For each, there are at most m low choices p and exactly m
solutions of the nonzero high equation. The contribution is at most
4m^2R^3.

Case C: Delta t=Delta u=0. Equation (5) also requires Delta a=0.
These are precisely weighted cone additive quadruples, bounded by (4).
Each has at most m low choices p and at most m^2 higher-digit pairs.
Its contribution is at most 4C^4*m^(11/2). No claimed cancellation of
the unknown higher constant kappa is needed for this upper bound.

The total for fixed n is at most

 2mR^4+4m^2R^3+4C^4*m^(11/2) <=10C^4*m^(11/2).

Summing at most m values of n proves (2). Markov with threshold
lambda*C^4*m^(5/2) gives at most 10m^4/lambda bad ORDERED factor-
residue pairs modulo d. This is a proof-side exceptional-set statement
about (P,Q) mod d, not a public N-only test or an executable exclusion
oracle for a factoring algorithm.

## 5. Native public and reflected centers have no global wrap

On the inherited original balanced supply, the literal projected public
gamma has GLOBAL order D dividing (P-1)(Q-1)=N-S, with D>16m^4. Also
N<=m^6 and S<=3m^3. Thus a centered target has effective phase

 F_r=t*S+delta_r-d*k_r mod D.

All hidden-order facts here are proof-side properties of the SAME actual
gamma, not algorithm advice or a CRT-selected generator.

Let ell_r=m*b_r-2*a*j and define the exact half-integer quantities

 A_N=(Nat.sqrt(N/2)+Nat.sqrt N)/2,
 B_N=(Nat.sqrt N+Nat.sqrt(2N))/2.

The displayed divisions by 2 here are rational, while N/2 in Nat.sqrt
uses the native integer quotient. Expanding the native lowerSum and
upperSum shows

 publicShift=floor((ell_r+a*A_N+t*B_N)/d+1/2).

For reflectedShift, A_N and B_N swap. This holds for either sign of a,
because the signed endpoint terms swap before their sum is taken.
Consequently for either center there are alpha,beta in {A_N,B_N} and
an error e with |e|<=d/2 such that

 d*k_r=ell_r+a*alpha+t*beta+e,
 F_r=t*(S-beta)+a*(1-alpha)-e.                           (7)

The entire centered b term has canceled exactly. Since N>=4,
1<=alpha,beta<=(3/2)*sqrt N<=(3/2)m^3. Also
S>=2sqrt N-1 implies S-beta>=0. Using |a|<m, t<m and S<=3m^3,
EVERY such phase, including mixed public/reflected choices, lies in

 [-(3/2)m^4-d/2, (9/2)m^4+d/2].

Pair-sum differences have absolute value at most 12m^4+2d<16m^4<D.
Thus equality of target products modulo N forces an EXACT integer phase
equality, which in particular implies (1) modulo d. We do not force
integer t-sum equality. The raw weighted global energy of any selected
light-tag family is therefore bounded by E_mod(P,Q), uniformly in all
higher-digit/factor-advised ray and native-center choices.

For a cover of the full multicenter packet union, choose one actual
row and one center at each light tag as a witness. This avoids claiming
that every emitted center copy has been charged in the catalog energy.
At no stage is collision coverage after trimming assumed.

## 6. Transfer to the SAME original supply and varying selector

Put m=Theta(M) on the inherited original Omega(M^6/log^2 M) balanced
prime-pair supply, with allowed candidate envelope K_*. For fixed P,m
the selector strip contains O(G_m+1) half-open Q boxes of width d, with
sum_m(G_m+1)=O(K_*M). This sum is over the varying selector, not a free
fixed set of m values.

For fixed m, each factor residue P mod d has O(M^3/d+1)=O(M) integer
lifts in the original P range. In each selector Q box there is at most
one integer per prescribed Q residue modulo d. The bad ordered residue-
pair bound from section 4 therefore gives at most

 O(M*(G_m+1)*m^4/lambda)

actual ordered pairs at this m. Summing gives O(K_*M^6/lambda). No prime
equidistribution in boxes or residue classes is assumed. In particular
we do not incorrectly apply the previous N-residue-only count to this
new exceptional set.

For p=q, use Q=P mod m. At fixed P,m a width-d box contains at most m
such Q integers. Multiplying O(M^3) possible P by the selector sum
gives the separate singular loss O(K_*M^5). It is negligible for the
allowed envelopes. Remove these inputs at ANY current candidate, along
with the bad-energy pairs. All losses are unioned against the SAME
original supply, not intersected across unrelated thin families.

For K_*=polylog M and lambda=K_*log^4 M the new energy loss is
O(M^6/log^4 M), hence negligible against the original supply. Earlier
soft O(M^5.994) losses and separately invoked o(M^6/log^2 M) exceptions
may also be unioned. For K_*=O(M^.020), lambda_m=m^.04 gives new energy
loss O(M^5.980), and the singular loss is only O(M^5.020).

## 7. Weighted carriers retain source multiplicities

There are g>=2m/3 selected light TAG entries, but centering can identify
targets from different t values. We do not infer g distinct values.
Retain the indices and let E_global count ordered equal-product
quadruples WITH source multiplicity. Section 5 bounds it by
lambda*C^4*m^(5/2).

Suppose the values are covered by k geometric progressions of listed
lengths T_i and total T. Assign every source index to one covering
progression; duplicate values retain their index multiplicity. If g_i
indices are assigned to progression i, their pair products take at most
2T_i-1 values. Weighted Cauchy--Schwarz gives

 E_global >=sum_i g_i^4/(2T_i).

The assigned source groups are disjoint, so these quadruple counts do
not overlap even when the values do. Holder gives

 g^4 <=2E_global*(sum_i T_i^(1/3))^3 <=2E_global*k^2*T.

Since g>=2m/3, the weaker convenient bound (3) follows. Ratios may lie
outside the gamma subgroup; overlap, repetitions, holes, cyclic wrap and
privately advised starts/ratios do not change the product-set count.

For polylogarithmic menus, (3) is soft Omega(m^(3/2)). For the frozen
K_*=O(M^.020), lambda_m=m^.04 gives m^1.46/(162*C^4). This excludes
polylogarithmically many progressions of total nearlinear length for the
full native-centered family. It does not exclude other shared operations.

## 8. Arbitrary origins: explicit wrap penalty

More generally choose ONE integer origin k_r per retained source entry,
with range H=max k-min k. A huge common origin cancels in all product
equalities. For effective phases F_r=t*S+delta_r-d*k_r a safe span is

 V=(m-2)*S+6d+dH.

An equal-product quadruple has signed phase difference ell*D with
|ell|<=floor(2V/D). Put W=2floor(2V/D)+1. Reducing modulo d gives the
raw congruence difference ell*D. Every off-zero congruence energy is
bounded by the zero one: if r(x) counts labeled catalog pairs with phase
sum x in Z/d, then

 E_c=sum_x r(x)*r(x-c) <=sum_x r(x)^2=E_mod.

This is translated Cauchy--Schwarz and includes repeated phase values.
Different ell yielding the same residue only overcount. Therefore,
uniformly over arbitrarily advised origins,

 E_global <=W*E_mod,
 k^2*T >=m^(3/2)/(162*W*lambda*C^4).                    (8)

The weighted representative injection uses one chosen origin per source
entry. Multiple distinct origin copies are not silently identified.
For the actual native centers section 5 gives W=1 from their sharper
phase envelope, without needing a relative-span hypothesis.

Since S<=3m^3 and D>16m^4, the general W above is
O(1+dH/D). Thus with polylogarithmic lambda,C and a polylogarithmic
number of progressions, a total nearlinear listed length would require

 H >=D/(m^(3/2)*polylog m),

eventually. Already D>16m^4 makes this at least m^(5/2)/polylog m.
The stronger inherited actual D>c*m^4.062 gives m^2.562/polylog m.
This is a numerical span requirement, not a lower bound on the bit cost
of acquiring an origin: large integers can still have short encodings.
Finding suitable very wide origins cheaply remains an open possibility.

## 9. Exact scope and remaining acquisition gap

The original source, public gamma, published prime supply and compiled
total packet budget are unchanged. The new arithmetic step is the low-
factor and two-high-digit averaging with the three-case projection count.
It handles the native centers that the preceding one-digit argument left
open. Weighted tag counting replaces the invalid distinct-target shortcut.
The general wrap inequality states precisely how an arbitrary-origin
escape weakens the obstruction instead of claiming it impossible.

Heavy-tag trimming is only a witness device for a carrier obstruction;
no useful collision is asserted in the light subset. A policy retaining
only a tiny privately chosen tag subset is outside the full-tag conclusion.
Zero-leading or denominator-m redesigns, which are not these native
Euclidean rays, are outside the source contract. Full multicenter union
energy, free materialization of all progressions, and runtime hardness
of implicit operations are not asserted. Source construction remains
the inherited nearlinear setup; this theorem does not evaluate its long
products. No new numerical examples, native edits, Lean declarations or
broad builds are used. A restriction-stable soft O(m) sufficient factor
query, complete bit/controller proof and Lean sixth-rate composition
remain unfinished.
