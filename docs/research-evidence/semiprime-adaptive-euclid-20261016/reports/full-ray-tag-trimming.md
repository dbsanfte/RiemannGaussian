# The complete Euclidean intermediate family also obstructs a few small carriers

2026-10-16. Classical corollary of the weighted cone/high-digit argument.
This goes beyond the primitive hyperbolic catalog: some intermediate
rays fail |a|t<m, but the compiled TOTAL Euclidean packet budget lets us
discard a small number of high-occupancy tags for the purpose of proving
a carrier obstruction. No long query, new coverage guarantee, operation
lower bound or Lean sixth-rate result is supplied.

## 1. Complete low-digit source and deterministic tag trimming

For n=N mod m nonzero, let F_(m,n) be the SET of triples (j,a,t) emitted
by native publicPairs n m j, over 1<=j<m. Keep every current and every
intermediate vector, deduplicating only identical triples. Let

 L_m=floor(log_2 m)+1, B_m=64*L_m^4.

The compiled publicPackets_length_le theorem gives, for EVERY n,

 |F_(m,n)| <=8*m*L_m^2.                                  (1)

Each ray emits both center packets, so using the full packet bound for
this deduplicated triple set is conservative. This is a per-input
source-list budget, rather than an unjustified conversion of the
universal coordinate SET bound to an incidence count. The source pairs
depend only on n,m,j because quotientSlope modulo m does.

Call a tag heavy if it has more than B_m distinct triples. Their number
is at most m/(8*L_m^2)=o(m). The remaining light tags are known from n
alone, before any higher digit or factor advice is chosen. For odd m>=5
there are at least 2m/3 light tags: there are m-1 original tags, and
m-1-m/(8L_m^2)>=2m/3. The light source has at most B_m rows at each tag.

All emitted nonzero pairs, including intermediates, satisfy

 0<|a|<m, 1<=t<m, a*j^2=n*t mod m.                       (2)

Here is the exact native reason for the coordinate bounds. A current
Euclidean frame has m=r0*y+r*x, r0>r>0, y>0, x>=0, r0<=m. A proper
intermediate k has a_abs=r0-k*r>0 and t=x+k*y. Thus

 m=r*t+a_abs*y,

so t<m, while 0<a_abs<r0<=m. Current r,y are also strictly below m.
The nonzero and congruence statements are the compiled euclidPairs_correct
and publicPairs_correct contracts. We do not require |a|t<m for this
corollary. In fact the same determinant identity implies primitivity,
but that fact is not needed after the light-tag bound.

## 2. The same energy argument applies without the hyperbolic condition

Use the centered native b, delta=a+m*b-2*a*j, and target
gamma^(-N*t-delta) for each triple. The geometric and higher-digit
parts of the accompanying hyperbolic report, sections 4--7, need only:

* low-digit dependence of the source catalog;
* the bounds and modular relation (2);
* at most a stated number of distinct rows per tag.

They do NOT use the product bound |a|t<m or primitivity after the catalog
occupancy has been established. Apply them to the light triples with
C=B_m. Color them with B_m colors, one point per tag in a color. Retain
weighted occurrences when different colors map to the same field point.
The cap-energy bound gives E_cone<=4*B_m^4*m^(5/2).

For E_light(n,h), impose the integer t-sum equality and delta-sum
congruence modulo m^2, before any advised selection. Fixing three triples
still fixes t_4 and low delta; the fourth tag satisfies the same nonzero
quadratic c*j_4^2+2*n*t_4*j_4-n*t_4=0. Two tags and at most two signed
a representatives per tag give at most four fourth triples. Nonzero
high-digit slopes admit at most one h; zero slopes give weighted cone
quadruples. Therefore, for every n,

 sum_(h<m) E_light(n,h) <=8*B_m^4*m^(7/2).                (3)

With threshold lambda*B_m^4*m^(5/2), there are at most 8m^2/lambda bad
coprime product residues modulo m^2. The SAME original selector telescope
gives absolute pair loss O(K_*M^6/lambda), without a union over source
selection rules. The fixed original balanced prime-pair supply, literal
projected base, and global-order qualification are unchanged.

## 3. Full-family and adaptive-selection conclusion

At every current m on the retained majority, let a policy choose ONE
actual current or intermediate ray at EACH original tag. The choice may
depend on all higher digits or on the hidden factors. Restrict its
targets to the deterministically light tags solely for this proof.
On the original global branch, 12m^2<S=P+Q-1<=3m^3 and D>16m^4.
Exactly the preceding no-wrap argument injects their multiplicative
quadruples into E_light(n,h). Equal targets can belong to at most two
selected tags. Thus the light selected target set Z_light has

 |Z_light|>=m/3,
 E_times(Z_light)<=lambda*B_m^4*m^(5/2).                 (4)

Consequently every k-progression cover of the policy's COMPLETE target
set, of total listed length T, necessarily covers Z_light, and obeys

 k^2*T>=m^(3/2)/(162*lambda*B_m^4).                       (5)

The complete unselected full-ray target union obeys the SAME COVER
obstruction: select any one ray per tag from that union and use its
light subset as a witness. We do not claim that the energy of the full
union, including heavy tags, satisfies (4). Its cover must cover the
low-energy witness; that suffices. This distinction avoids treating
discarded heavy-tag quadruples as if they had been bounded.

For K_*=polylog M and lambda=K_*log^4 M, (5) is soft Omega(m^(3/2)).
For K_*=O(M^.020) and lambda_m=m^.04 the loss is O(M^5.980) and the
tradeoff is m^1.46/(162*B_m^4). In particular the proposed few-carrier
nearlinear representation is impossible on an actual infinite majority
family even when the policy adaptively chooses from ALL literal
Euclidean intermediates. All earlier negligible exceptional sets are
unioned against the SAME original supply, including separately charged
o(M^6/log^2 M) losses when their extra properties are invoked.

One chosen q-origin per source entry is also allowed under the explicit
range-H inequalities in the hyperbolic report. In particular any advised
polylogarithmic relative origin span on the selected light rows is
permitted. A huge common origin cancels. This does not automatically
qualify the native publicShift or reflectedShift list: those rowwise
centers may have a much larger relative span. Multiple origin copies
require a separate multiplicity/occupancy budget.

## 4. Acquisition and limits

The complete native Euclidean list is already constructible within its
compiled O(m log^2 m) emission budget. The Euclidean divisions, pair
sorting/deduplication, per-tag occupancy and the light/heavy labels cost
soft O(m) public operations on polylogarithmic-size integers. The usual
exact centered lifts and binary scalar powers then give the same given-
N,m,gamma soft O(m*ell^2) bit setup bound, ell=ceil(log_2(N+1)), and soft
O(m*ell) bit storage. This is an explicitly paid source acquisition,
not a long residual-query algorithm or a new native time proof.

Trimming is a PROOF device for a carrier obstruction. It is not licensed
as a factoring algorithm: a useful collision could lie at a heavy tag,
and no collision coverage is asserted for the trimmed source. Every
cover of the full target family still contains the light witness. A
policy that retains only a tiny privately chosen tag subset, unrestricted
rowwise center spans, high-productset carriers, many carriers sharing
operations, implicit scalar norms and other sufficient factor queries
remain outside this obstruction. Nonprimitive scalar multiples and
zero-leading/denominator-m redesigns are not emitted source rays here.

This extends the earlier fixed-row cone theorem to the full native
current/intermediate family via a low-digit, deterministic tag-count
argument. No numerical examples or backend lemmas are substituted for
the arithmetic proof. The whole-family soft O(m) collision query and
the guaranteed sixth-rate Lean factorizer remain unfinished.
