# A uniform carrier obstruction for the full primitive hyperbolic row catalog

2026-10-16. Classical proof, not a new Lean declaration. This extends the
frozen fixed-row short-source obstruction to ALL primitive rows with
0<|a|,t<m and |a|t<m, simultaneously. It permits higher-digit-dependent
and factor-advised row choices, and polylogarithmically varying relative
origins. It also gives an explicit nearlinear public catalog constructor.
It does not acquire the long collision query or prove an operation lower
bound. The new scope closes an adaptive-choice escape from one proposed
few-geometric-carrier method; it does not close the overall sixth-rate gap.

## 1. Literal source and statement

Let m be an odd prime, n=N mod m nonzero. Define the low-digit-dependent
list of triples

 C_(m,n)={(j,a,t): 1<=j<m, 0<|a|<m, 1<=t<m,
                     gcd(|a|,t)=1, |a|t<m, a*j^2=n*t mod m}.

For each triple use the exact native lift

 D_r=(N*t-a*j^2)/m,
 b_r=centered(m,-j^(-1)*D_r),
 delta_r=a+m*b_r-2*a*j,
 z_r=gamma^(-N*t-delta_r), q=gamma^(m^2).

The signed a is retained. The integer division defining D_r is exact.
Public inverse representatives give the same centered b_r. Since m is
odd, |b_r|<m/2 and |delta_r|<3m^2. The canonical denominator-one rows
(positive a, t=1) belong to this catalog, so every tag has a row.

Put C_m=81*ceil(log_2 m). We prove a bound for the ENTIRE raw catalog:

 sum_(h=0)^(m-1) Ecat(n,h) <= 8*C_m^4*m^(7/2),             (1)

where Ecat counts ordered catalog quadruples satisfying the INTEGER
t-sum equality and the delta-sum congruence modulo m^2 at N=n+m*h.
The catalog depends only on n; the chosen row at each tag may depend
arbitrarily on the higher digit, the full N, or privately supplied factors.

On the SAME inherited balanced prime-pair supply, deleting at most
O(K_* M^6/lambda) original pairs gives, simultaneously at every current m,

 E_times(Z) <= lambda*C_m^4*m^(5/2),                       (2)

for EVERY advised choice of one catalog row at each tag. Here Z is the
set of distinct GLOBAL targets, and lambda>=1 is the chosen threshold.
There are at least m/3 distinct targets. Thus ANY cover by k finite
ambient geometric progressions with total listed length T satisfies

 k^2*T >= m^(3/2)/(162*lambda*C_m^4).                      (3)

No union over advice, chosen rows, progressions or origins is needed.
For a polylogarithmic candidate envelope and lambda=K_* log^4 M, the
right side is soft Omega(m^(3/2)) on a majority of the SAME original
Omega(M^6/log^2 M) supply. Polylogarithmically many progressions with
nearlinear total length cannot represent these full-tag families.

The result concerns global targets in the unit group modulo N. It does
not claim the corresponding local-field energy bound, a query-operation
lower bound, or collision completeness for every advised row selection.

## 2. Only logarithmically many primitive candidates per tag

Fix n,j. Divide possible |a| into the ceil(log_2 m) bins

 2^s <= |a| < 2^(s+1),  t < m/2^s.

Any two vectors v=(a,t), w=(a',t') in one bin have determinant divisible
by m, by their common modular relation. Also |det(v,w)|<4m. If all
vectors in the bin are parallel, positive t and primitivity make them
identical: a primitive integer vector has only itself on its positive
primitive ray.

Otherwise choose independent v,w from the bin. Every vector x in the
bin maps to the two integers

 (det(v,x)/m, det(w,x)/m).

Both lie in [-4,4]. This map is injective because v,w are independent
over Q. There are at most 81 pairs, whether or not v,w span the entire
index-m lattice. Therefore each tag has at most C_m catalog entries and
the full list has R<=C_m*(m-1) entries. No lattice-basis or square-root
oracle is used in this argument.

## 3. Nearlinear public acquisition of the complete source catalog

This cardinality estimate alone would not pay for enumeration. The
following separate algorithm does.

1. Tabulate the nonzero modular inverses modulo the public prime m.
   Tabulate, by enumerating j=1,...,m-1, the tags for each square j^2.
   Every nonzero square has two tags, and nonsquares have none.
2. For A=1,...,m-1, both signed choices a=+A,-A, and
   t=1,...,floor((m-1)/A), retain only gcd(A,t)=1.
3. Look up j in the square table at n*t/a mod m, and emit the triples.

These are exactly all catalog triples. The number of loop pairs is at
most 2*sum_(A<m)floor((m-1)/A)=O(m log m), and each has at most two
outputs. Square-table construction is O(m); no quadratic-residue root
finding or hidden-field representation is assumed. Extended gcd can
build each inverse with polylogarithmic cost if a simultaneous inverse
method is not used. The gcd filter, exact lift, centering and scalar
powers for every output have polylogarithmic cost in m and log N. In the
factorization regime m is polynomially bounded in N and the exponents
N*t+delta have O(log N) bits. Put ell=ceil(log_2(N+1)). Given the public
N,m,gamma, ordinary binary modular powering gives soft O(m*ell^2) bit
work with fast integer arithmetic, and soft O(m*ell) bit storage; the
O(log m) catalog factor is included in the soft notation. In the sixth
scale ell=O(log m), so this is softly linear in m. The inherited public
gamma setup is a separate earlier input charge, and no long row-product
evaluation is included in this catalog construction bound.

## 4. Weighted cone energy handles the whole catalog

Map a catalog entry to A_r=(a,t,a*j) in F_m^3. It lies on
Q(a,t,u)=u^2-n*a*t=0. The coordinates a,t are nonzero in the field.
Color the entries with at most C_m colors, so each color has at most one
entry per tag; choose this coloring from the low-digit catalog alone.
Within each color the directions u/a=j are distinct, and

 Q((1-s)A_j+s*A_k)=-s*(1-s)*a_j*a_k*(j-k)^2.

Thus a color class is a cap: no line contains three of its points.
The self-contained polar/projective-incidence proof in the frozen
shortrow-cone-energy report gives E(A_color)<=4*m^(5/2).

Different colors can contain IDENTICAL field points. They must not be
discarded: signed a and a-m can have the same field representative.
Let f be the sum of the color indicators, retaining these multiplicities.
For nonnegative finite functions define E(f)=||f*f||_2^2. For indicators
g_i,g_j, the difference-correlation identity and Cauchy--Schwarz give

 ||g_i*g_j||_2^2 <= sqrt(E(g_i)*E(g_j)).

The triangle inequality then yields

 E(sum_i g_i)^(1/4) <= sum_i E(g_i)^(1/4).

Indeed sqrt(E(sum_i g_i))=||sum_(i,j)g_i*g_j||_2 is at most
(sum_i E(g_i)^(1/4))^2. Consequently the raw weighted catalog energy is

 E(f) <= 4*C_m^4*m^(5/2).                                (4)

This is a finite-sum inequality, not an algorithm requiring Fourier
transforms or field extensions. It counts all catalog-entry quadruples
whose cone points add, even when representatives repeat across colors.

## 5. Average over the higher input digit

For N_h=n+m*h, exact centering gives

 delta_r(h)=delta_r(0)-m*h*t/j mod m^2.                   (5)

The same delta depends only on N modulo m^2. Count Ecat(n,h) before
choosing any row policy. Fix three catalog entries in a quadruple. The
integer t-sum equality fixes t_4, and the low delta equation fixes c.
If 1<=t_4<m, a possible fourth tag must satisfy

 c*j_4^2+2*n*t_4*j_4-n*t_4=0 mod m.                     (6)

This nonzero polynomial has at most two roots: even when c=0 its linear
coefficient is nonzero. At fixed j_4,t_4 there are at most TWO signed
integer representatives a_4 in (-m,m). Thus there are at most four
fourth entries, and at most 4*R^3 low-compatible quadruples.

For a nonzero signed slope sum of t/j, (5) admits at most one h. For
zero slope, use t/j=a*j/n modulo m. This gives zero signed sum of a*j;
the low delta equation then gives zero signed sum of a. Together with
the integer t-sum condition, this is a weighted additive quadruple on
the cone. Bound it by (4), and allow all m higher digits. Therefore

 sum_h Ecat(n,h)
   <=4*C_m^3*m^3+4*C_m^4*m^(7/2)
   <=8*C_m^4*m^(7/2),

proving (1). With threshold lambda*C_m^4*m^(5/2), at most 8m/lambda
digits h per n are bad, hence at most 8m^2/lambda coprime product
residues modulo m^2 are bad. The condition uses only the public residue,
not the eventual advice, gamma order, or unknown factors.

## 6. Actual global transfer, including advised origins

On the inherited original supply, let S=P+Q-1. The actual public gamma
has GLOBAL order D dividing (P-1)(Q-1)=N-S. Eventually at each current m,

 12m^2<S<=3m^3,  D>16m^4.

The upper sum bound follows from the balanced source and N<=m^6; the
lower bound follows from P,Q=Theta(m^3). The order and literal public
gamma are the already qualified source, with no CRT-selected substitute.
Thus the effective phase of z_r is t*S+delta_r modulo D. For an ordered
quadruple its absolute signed phase difference is less than

 2*(m-2)*S+12m^2 < 16m^4 < D.

Global product equality therefore forces exact integer phase equality.
As S>12m^2, this first forces the INTEGER t sums equal, and then the
delta sums equal. Distinct-target multiplicative energy is bounded by
Ecat: choose one catalog representative per target and inject its
quadruples into the raw count. This works for EVERY chosen subset of
catalog entries, even when the choices depend on h and the factors.

For one chosen entry at every tag, equal global targets force equal t
and delta. At fixed t,delta the quadratic (6) gives at most two tags.
Therefore J>= (m-1)/2 >=m/3. No assertion that such an arbitrary chosen
row family must still contain a usable collision is needed or made.
The full catalog target set contains any such selected family and obeys
the same energy upper bound by representative injection.

There is a uniform extension to chosen q-origins. Assign ONE integer
e_r to each retained catalog entry, with span max e-min e<=H, and replace
delta_r by delta_r+m^2*e_r. A huge common origin cancels from all single
and pair phase differences. The raw congruence modulo m^2 is unchanged.
The proof still works whenever

 S>(12+2H)*m^2,
 2*(m-2)*S+(12+2H)*m^2<D.                                (7)

In particular H=polylog(m) satisfies these inequalities eventually on
the SAME actual supply. Advice may choose both rows and these relative
origins after seeing the full input or the factors. No union over choices
is required. We do not place all H shifted copies of one entry into the
raw catalog without charging their multiplicities. There is at most one
chosen origin per source entry in each assignment covered by this claim.

## 7. Selector accounting and the carrier consequence

Use exactly the previous varying-selector box argument. At fixed P,m,
the allowed Q strip is a union of O(G_m+1) half-open boxes of width m^2.
Since P is invertible modulo m^2, each box contains at most one Q for
each bad product residue. There are O(m^2/lambda) bad residues, O(M^3)
possible integer P, and sum_m(G_m+1)=O(K_* M). Hence the absolute new
loss is O(K_* M^6/lambda), measured against the SAME original prime-pair
supply. If lambda/(K_* log^2 M) tends to infinity, this and all preceding
soft O(M^5.994) losses have negligible union. This proves (2) simultaneously
at all current candidates, with all row/origin advice still quantified.

For completeness, partition distinct targets among k covering geometric
progressions, with assigned sizes J_i and listed lengths T_i. Products
of the i-th assigned set have at most 2T_i-1 values, so
sum_i J_i^4/T_i<=2E_times(Z). Holder gives
J^4<=2E_times(Z)*(sum_i T_i^(1/3))^3<=2E_times(Z)*k^2*T.
This proves (3). Starts, ratios and chosen covers may be privately advised;
holes, overlaps, repetitions, cyclic wrap and ratios outside the gamma
subgroup do not affect the argument. Any containing finite carrier C
also has |CC|>=m^(3/2)/(81*lambda*C_m^4).

For K_*=polylog M choose lambda=K_*log^4 M to obtain the stated soft
Omega(m^(3/2)) tradeoff. For the larger frozen envelope K_*=O(M^.020),
choosing the comparable candidate threshold lambda_m=m^.04 gives absolute
loss O(M^5.980) and k^2*T>=m^1.46/(162*C_m^4). Both exclude a few nearlinear
progressions; neither is an operation lower bound.

## 8. Native inclusion and precise limits

The native CURRENT Euclidean frame has m=r0*y+r*x with r0>r>0 and y>0.
Its emitted signed remainder and denominator satisfy |a|=r,t=y. Thus
r*y<r0*y<=m. Also gcd(r,y) divides m; since m is prime and 0<r,y<m,
the gcd is one. The native determinant update preserves the frame from
the initial (m,u,0,1). Consequently every nonzero current convergent,
including publicRow at its fixed square-root threshold and every nonzero
output at another admissible positive threshold, belongs to the primitive
hyperbolic catalog. Its higher-digit-adaptive selection
is now covered. This primitivity conclusion is a classical inference
from the pinned compiled invariant; it is not a newly compiled lemma.

Arbitrary intermediate rays can have |a|t>=m and are outside this catalog.
So are nonprimitive multiples and denominator-m redesigns. Algorithms
discarding all but a privately chosen tiny tag subset are outside the
full-tag size conclusion. Unbounded relative origins can defeat the
integer phase separation and are outside (7). Many carriers with shared
computation, high-productset carriers, norm-only methods and other
factor-selective algorithms remain open. The theorem does not turn an
arbitrary advised row selection into a collision-complete factorizer.

The previous shortrow-cone-energy theorem fixed ONE low-digit-dependent
row per tag. The present result instead dominates the complete primitive
hyperbolic catalog, permits all higher-digit/advised choices simultaneously,
and pays for its public construction. This is the new arithmetic scope;
the cap-incidence lemma, original qualified supply, selector telescope and
energy-to-cover inequality are inherited and explicitly reused. No new
examples, native edits, broad builds or overall query improvement are used.
The soft O(m) sufficient factor query, full bit/controller budget and
Lean sixth-rate composition remain unproved.
