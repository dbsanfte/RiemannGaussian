# Retrospective joint-information handoff: native rows to HH rectangles

26 October 2026. Read-only audit of acquired Oct22-26 arithmetic
representations against the NEW joint HH interface. No research code,
numerical examples, tests, campaign or repository edits.

**Executed best pairing:** project the actual native row's stationary
colour and real physical-index bound into a factor rectangle. This is
legitimate and needs no collision first. It does NOT meet the new total-
width budget: the retained axis bank gives a full-width interval at every
unit colour throughout the axis range, and even the factor-correlated
Euclidean first-odd bank has Theta(k) full constant-relative-width
rectangles at a fixed near-axis factor scale. These are exact statements
about these acquired representations, not a lower bound against every
smaller factor-correlated selection. No older already-acquired output
with the required density was found in the concrete sources checked.

## 1. New acceptance criterion and the actual handoff

Read current `README.md` and `joint-information-review.md` in this
scratch packet. The proved recipient accepts A acquired JOINT rectangles

    (sigma mod n, [L,U]), n|k, U<=2L,
    Delta=sum (U-L)/L,

with one rectangle containing the true smaller factor and its correct
residue. A=soft O(k) and Delta/n<=k^(-1/3) suffice for soft k.
The point is not that one interval and some OTHER residue are correct.
All palette/interval acquisition belongs in the bound.

For an original stationary row (a,b,lambda), the factor variable p obeys

    a*p^2+lambda*p+b*N=0 mod H,
    a*j^2=b*N mod k, lambda=-a*j-b*N*jinv mod H,
    |a*p+b*N/p+lambda|<=H*M.                       (1)

Here j=p modk, its inverse has precision H, and the stationary phase
is invariant under changing the lift j by k. The real inequality can
be solved by quadratic root isolation and integer rounding into a
constant number of real intervals, then split into dyadic-ratio pieces.
For the native O(log N)-bit inputs this costs polynomial(log N) per
component. The residue/phase incidence list is already soft k acquired.
Thus the row-to-rectangle projection is a REAL paid possible handoff.
In using HH, retain sigma=j but note its source form is a_HH*Q+b_HH*P;
the coefficients corresponding to (1) are a_HH=b,b_HH=a. No swap of
coefficient orientation or hidden P value is used to initialize a row.

The question is the total relative width, not just the descriptor count.

## 2. Exact density of the retained axis projection

Take positive horizontal rows a=k,b=0, lambda=t*k. On a public factor
bin [B,2B], assume

    2kB+H<=H*M.                                    (2)

Then for EVERY t in [0,k), the entire bin satisfies the real part of
(1). Its stationary colour is exactly j=-t modk. Unit-tag phases give
phi(k)=k/3 distinct public colours. The only positive horizontal row
with E/H integer is t=k-1, j=1; public whole-row deletion removes that
one row. Every other such row survives literal deletion: 0<E<H.
The lambda=0 phase is not a unit-tag phase, and its earlier discharge
does not affect this count. Opposite folding pairs rows of the SAME
colour and does not remove the colours. Optional factor-swap quotient
can change the count by only a constant.

Consequently the actual literal axis projection contains, even at ONE
bin, at least phi(k)-1 full-width joint rectangles

    (j modk, [B,2B]),
    Delta>=phi(k)-1=Theta(k), Delta/k=Theta(1).     (3)

Condition (2) holds throughout B=Theta(k^(2+gamma)), 0<gamma<1/2,
N=Theta(k^6), for sufficiently large k. This covers the actual axis
range under investigation. Added whole-row/full-phase completions are
not needed for the count: these unit-tag rows are present before any
additional collision-dependent unit certificate. A future proven
coverage-preserving pruning might remove many; (3) does not forbid it.

This is NOT a claim that all these colours contain actual divisors of
one N. It shows that the already acquired row's OWN joint real bound
and phase congruence have not supplied narrower factor information.
Applying the new HH recipient to exactly this explicit menu still gives
its old N^(1/5) scale, not soft k.

## 3. First Gauss vector per colour has the same interval issue

The Oct26 stationary Gauss cover already acquires a first vector for
each public colour and dyadic factor scale p0. In the weighted norm
(a*p0,b*N/p0), its length ell satisfies

    ell^2<=2kN/sqrt(3).

For ANY real p in [p0,2p0], Cauchy--Schwarz gives

    |a*p+b*N/p|<=sqrt(5)*ell
               <=sqrt(10/sqrt(3))*sqrt(kN).

Adding 0<=lambda<H remains strictly below 4sqrt(kN), using the native
hard branch, so the original signed M bound holds throughout the ENTIRE
public factor bin. These are not approximate unknown intervals: the
old construction was deliberately uniform on that bin.

Thus substituting its acquired coefficient/phase pair into (1) does
not reveal a narrow subinterval. It simply returns its old full bin
for each colour. Canonical carry correctness is useful provenance,
but is not a new high factor digit. Public literal deletion does not
create a narrow interval: nonaxis E=bN+O(H+k) is outside the old HM
range, and horizontal-axis deletion affects only the exceptional tag
above. A claim about a more aggressively unit-pruned subfamily would
need its own proof; it is not used in this count.

## 4. Stronger test: divisor-correlated Euclidean menus

This pairs the NEW recipient with an older representation that really
used PQ=N, avoiding the independent-tag/scale objection.

Source: `semiprime-knot-fusion-20261026/factor-correlated-cover.md`,
Sections2-4; `first-odd-filter-addendum.md`, Sections1-3. These are the
reviewed Lenstra sign-change construction with exact parity convention.
For j unit, let s=[Nj^(-1)]_k, g=[N*j^(-2)]_k and
P=j+kx,Q=s+ky. Its first odd stage is (a,b)=(g,1), and

    c=g*x+y=(g*P+Q-g*j-s)/k,
    2mu*g<c<mu*(k+g),
    mu=ceil(sqrt(N/k^3)).                          (4)

The phase and c modk are acquired. At an actual factor in the residue,
the factor equation makes that c congruence automatic; it is not a
separately acquired high-digit constraint on P.

Put P0=sqrt(N/k), theta=g/k, and test the FIXED public factor interval

    (5/4)*P0 <= p <= (3/2)*P0,
    1/4<=theta<=1/3.                               (5)

Write p=r*P0, mu0=sqrt(N/k^3). Dividing c by mu0*k gives

    c/(mu0*k)=theta*r+1/r+O(1/mu0),

uniformly in all actual residues j,s; the known offset (gj+s)/k is
O(k), while mu0*k is the main scale. For r in [5/4,3/2], theta in
[1/4,1/3], there are FIXED positive margins

    theta*r+1/r > 2theta,
    theta*r+1/r < 1+theta.

For example the upper margin is at least7/60, and the lower margin
at least1/2. Rounding mu changes endpoints by O(k), so for the actual
asymptotic N=Theta(k^6) the ENTIRE interval (5) lies strictly inside
the acquired first-odd REAL menu. Integer endpoints may be moved
inward by one without changing its constant relative width.

The map j->g runs twice through the odd unit class g=N mod3. Hence
Theta(k) actual public colours have g in [k/4,k/3]. All their b=1 rows
are nonaxis, off the pruned diagonals and survive the original public
zero-row deletion: E=N+g+lambda exceeds HM for sufficiently large k.
Each therefore gives a full interval (5) of relative width1/5. The
resulting JOINT menu has

    A=Theta(k), Delta=Omega(k), Delta/k=Omega(1).   (6)

This proves the new joint density target fails for this literal
factor-correlated first-odd menu projection, not merely that its old
q-clock support was long. The AM--GM/discriminant lower filter already
present in the addendum does not remove (5): it enforces
T>=2sqrt(gN), which the actual hyperbola g*p+N/p always satisfies.
Selecting only later/even stages would need a new sign-crossing
replacement theorem; the acquired Lenstra lemma does not give it.

Equations (3),(6) are constructor-specific density tests. They are not
lower bounds on a fixed-N divisor cover or an implicit interval filter.

## 5. Can old integer-square filtering make those rectangles sparse?

The same source Section5 already acquires the exact bilinear equation

    f(u,v)=k*u*v+q0*u+p0*v+(p0*q0-N)/k=0,
    P=p0+k*u, Q=q0+k*v.

For an unbalanced factor bin around B with relative width epsilon,
the CORRELATED box scales are

    X=Theta(B*epsilon/k),
    Y=Theta((N/B)*epsilon/k),
    X*Y=Theta(N*epsilon^2/k^2),
    scaled height W=Theta(N*epsilon/k).

The linear coefficients give this height in the nontrivial regime;
using W=N would overstate the source theorem. Thus the primary
Coppersmith integer-bilinear XY<W^(2/3) comparison still requires

    epsilon=O(k/N^(1/4))=O(k^(-1/2))

at N~k^6, up to its explicit slack/accuracy factors. The B dependence
cancels: merely specializing to the axis regime does not enlarge the
certified empty-box range. Covering all k colours and a full factor
bin literally requires soft(k^(3/2)) such boxes, already above the new
A budget, before polynomial-time lattice factors. A collision/root
oracle for those boxes was not previously acquired. This is the same
old shifted-height limitation, now checked against the new recipient.

## 6. Oct22 multiplier/analytic and Oct24 inverse-row outputs checked

Two older apparently complementary outputs were examined specifically
for an already acquired factor palette.

1. **Fermat-quotient multiplier cover, Oct22.** Source
`semiprime-fermat-multiplier-20261022/reports/fermat-multiplier-cover.md`,
Sections2-3,6: a soft-k acquired set S covers cP mod H with c<k,
and the greedy witness labels are acquired. But its Section6 bijection
shows restoring (row,multiplier) pairs enumerates ALL unit residues
mod H, with exactly k(k-1) labels at the prime-modulus version. The
small quotient-shift palette is not P mod n. Projecting its labelled
factor residues to a divisor n produces no proved small P palette;
acquiring the true multiplier/quotient is still the old selection task.
The fixed-prime-power analogue in
`semiprime-curvature-acquisition-20261023/reports/dyadic-cover.md`,
Sections1,4,7, explicitly reduces to +/-1 residue classes and their
small-multiplier inverses. Its radix fold represents all candidate
factors, not a newly acquired narrow interval.

2. **Inverse-tag fusion, Oct24.** Source archived in recurrence
checkpoint evidence `semiprime-compact-cover-20261024/
native-cover-combination.md`, Sections3-5: its acquired relation
simplifies EXACTLY to a weighted ordinary candidate ray
`beta^[m*rho_j*(j+m*h-1)]=1`, with h ranging over the full possible
factor quotient. The coefficient rho_j is public, but the actual h
or a smaller factor interval is not. Applying the new HH recipient
before evaluating that query again leaves all tags/full bins. A
located arbitrary modular alias cannot be called the actual tag j;
the old strong decoder or exact source provenance is required.

These are not broad analogy failures: they are the explicit acquired
objects and their precise missing maps to the new joint interface.
Analytic nonsplit/character palettes used elsewhere impose conditional
orientation or constant-density character constraints, not an acquired
same-factor residue palette of density k^(-1/3). This audit does not
stack independent good-orientation assertions on one unknown factor
without a proof of their joint provenance.

## Outcome and narrow next arithmetic target

The genuinely acquired older row/interval objects can be passed to HH
with all coefficients and carries paid, but the tested joint menus
have Delta/n of constant order. The full marginal tag list was not the
only problem: the REAL factor intervals encoded by the actual axis,
Gauss and first-odd Euclidean rows remain wide on those tags.

A substantive next result would be a coverage-safe selection across
those already acquired stage intervals, or an inexpensive global
integer filter shrinking their total relative width by k^(1/3), while
retaining the correct residue and interval in the SAME rectangle.
None of the checked earlier artifacts already supplies that output.
The new consumer remains useful and strictly weaker as an output
specification, but its arithmetic supplier is still open. No general
lower bound, missed all-semiprime theorem or new factoring exponent is
claimed.
