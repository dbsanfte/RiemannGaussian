
## 2026-10-24: uniform quadratic-torus order supply and paid point ideals

This pass acquires a uniform deterministic factor-or-large-odd-order
supplier for the norm-one quadratic torus within soft k BIT operations.
It returns a proper factor or an actual W with BOTH local orders odd
and BOTH ord_p(W^H)>16k^2, H=k^2. This closes the point/order supply
obligation for this quadratic source. It does not make the two primes'
torus orders coprime, include an N+1 projection, or accelerate the long
collision query. The complete covered query remains
soft(J+sqrt(JL))=soft k^(3/2), J=O(k), L=2k^2+2.

Retain the prepared scalar beta, its odd local beta/beta^H order margins,
and B=(Z/N)[tau]/(tau^2-D), with D negative fundamental,
Jacobi(D,N)=-1 and |D|<=k/2. Exactly one unknown local B is a field;
the other is split. For a norm-one R, Norm(R^n-1)=0 at either local
prime if and only if R^n=1 in the WHOLE local algebra. On the split
side this is the identity -(u^n-1)^2/u^n for (u,u^-1). Thus the
supplier's saturated scalar norms are actual two-side identities,
not unpaired split support; no auxiliary value uses the beta decoder.

Maintain a known M<k dividing both p-chi_D(p), initially one. Acquire
the 2M+1 Cayley points R_a=(a+tau)/(a-tau), 1<=a<=2M+1. Their
actual scalar denominators a^2+|D| are below both primes and their
pairwise differences are units. Each local M-kernel has at most M
points. Scanning Norm(R_a^M-1) therefore gives a factor or a selected
R outside BOTH kernels, at soft M actual acquisition/powering cost.
This is an executed palette selection, not a survival assumption.

Kill R's 2-part by 2^ceil(log2(N+1)), set W to that power and q_W=W^H,
then run one actual ordered short-order screen through C=16k^2.
The baby polynomial of degree 4k and 4k giant nodes acquire the exact
consecutive blocks 1,...,C by monic arithmetic. Unit blocks certify
both q_W orders>C; proper gcds factor. Otherwise the FIRST nonunit
block and earliest-child descent give a common EXACT q_W order r<=C.
A saturated block alone is not called an order.

The RAW R then has the actually factored annihilator K=2^v H r,
with O(log N) bits. Public k factors and trial factorization of
r<=16k^2 cost soft k. Guarded prime removal from K yields a factor
or a common EXACT raw order d: unequal local prime valuations would
produce a proper gcd. If d<k, replace M by lcm(M,d). Because R was
outside the old M-kernel, this is a proper integer multiple and at
least doubles M. It remains a common divisor of the two group orders;
no stored element of order M is presumed.

A known common divisor d>=k is itself a paid factor consumer. The
smaller prime belongs to one of the two progressions di+1 or di-1.
Acquire their products over EXACT positive terms between 2 and
floor(sqrt N), using monic baby/giant AP products and literal final
tails. Both signs are searched; d=P+1>sqrt N is allowed. Every term
is below Q, so any nonunit gcd is proper. The number of terms is
O(sqrt N/d+1), whose square root is O(k) since N<=k^6. This AP escape
costs soft k, with no local sign or large-integer factor oracle.
Geometric M growth and O(log k) actual screens give the full soft-k
supplier; there is no unresolved small-order/common-kernel branch.

Use its W in ALL actual targets
V_j=beta^E_j W^[ell_j+chi_D(j)(N+a_j)]. Local norm-one divisibility
still proves the original own-row hit and target norms beta^(2E_j).
RERUN the actual coupled-seed screen for z=(beta W)^H in soft k:
a large q_W order is not a split-coordinate certificate for this z.
The beta norm exclusion at the field side makes a failed coupled
screen a proper factor. At that nonsplit side only, odd beta^H and
W^H orders divide p-1 and p+1 and hence are coprime; ord(z)>C^2
there. This is not cross-prime order coprimality or coordinate
genericity. The original same-leaf saturated beta consumer is retained.

There is also a controlled public row-modulus refinement. In the
N=1 mod 4 character-discovery branch, factor the acquired Jacobi-minus
integer a and select ONE prime divisor ell with Jacobi(ell,N)=-1.
Use D=-ell for ell=3 mod 4, D=-4ell for ell=1 mod 4, and D=-8 for
ell=2; in the N=3 mod 4 branch retain D=-4. For c=|D| choose an odd
public prime q>=max(3,ceil(N^(1/6)/(2c))), q!=ell, by a sieve and
two Bertrand intervals, and set k=2c q. On the continuing asymptotic
branch k=Theta(N^(1/6)); discovery, public factorization/sieve and all
actual new-k scalar/seed guards remain within soft k. The accepted
character-discovery theorem and finite-input fallback are retained.
No least prime in a growing prescribed progression is assumed.

This k has at most two distinct odd prime factors, each exponent one,
and v2(k) in {1,3,4}. The native identity
N^-1 delta_j=(j^-1-1)^2-1 mod k therefore puts at most 16 unit tags
in each EXACT integer-delta fiber: at most four roots at the 2-part
and two at each odd prime. If M is the number of norm fibers, then
M>=phi(k)/16>=k/60. Actual target dedup cannot remove an entire delta
fiber, because equal target norms and the beta margin force equal
integer deltas. Thus the norm projection still has degree Theta(k);
this is a cardinality ledger, not an algorithmic lower bound.

The point-ideal input is now genuinely acquired, including pivot
certificates. After exact target dedup, a saturated difference norm
would give equality at the nonsplit side, then equal integer deltas,
then equal unit norms globally. At the split side equality of either
component with the same unit norm forces the other equality, so it
would be an excluded global duplicate. Acquire F'(V_j) for all j by
monic MPE; unit derivative norms certify ALL target differences units.
One bad row is scanned in soft J to return a proper pair factor.
No J^2 pair scan or assumed simple-root oracle is used.

Group targets by delta, with n_d=beta^[2(N+delta_d)],
G(T)=prod_d(T-n_d), and F_d(U)=prod_(j in d)(U-V_j).
Distinct n_d differences are certified units. CRT selectors give an
actual polynomial mathcalF(T,U) agreeing with F_d(U) at T=n_d.
The controlled modulus gives degree_U<=16, so all 17 coefficient
functions can be interpolated explicitly in soft k, with O(k) slots.
Writing mathcalF(T,X+tau Y)=H0+tau H1 yields the fully acquired
auxiliary-coordinate ideal

    (G(T), T-X^2+DY^2, H0(T,X,Y), H1(T,X,Y)).

It is EXACT, not just a vanishing overcover. After the faithfully flat
quadratic extension, put u=X+tau Y, v=X-tau Y. On one norm fiber uv=n_d,
bar(F_d)(n_d/u) is a unit Laurent multiple of F_d(u); unit-separated
roots give precisely the original points. Descent proves the true
R-point ideal and rank-J quotient. Before T substitution the complete
coefficient arrays cost soft k. Eliminating T can expand to O(k^2)
slots; a balanced original-bivariate Groebner basis is not acquired
merely by displaying this bounded-width norm-coordinate ideal.

A separate coordinate construction gives soft-J exact component
ideals even without a general-position premise. Certify x-node
separation by derivative products, factoring on a nonunit difference;
repeat within x fibers for their y nodes. Group fibers of size d and
coefficientwise interpolate their monic y polynomials. The actual
component is (A_d(X),G_d(X,Y)), with total free coefficients O(J),
and its CRT quotient is exactly the retained points. A measured
rectangular profile with s*d=n and s,d=O(sqrt n) supplies a genuine
two-equation complete intersection of total degree O(sqrt n) in
soft n. Variable fibers have an exact factored union as well. These
are conditional on the ACTUAL profile, not guaranteed by order or
coordinate separation. Public-label rational-univariate data is also
paid soft n but has degree n and no free inverse projection.

The old fixed Cayley choice has a real original-source degeneration:
when D=-3, W=(tau-1)/2 has W^3=1, all native Texp_j are divisible
by three, and 3 divides H. ALL actual old targets/seeds are scalars.
Their exact ideal is (Y,prod(X-beta^E)); every point-vanishing equation
of total degree below n is divisible by Y and leaves the whole line.
This concerns that permitted original configuration, not an infinite
hard-semiprime family or an algorithmic lower bound. The inexpensive
eta=2 repair at D=-3 (eta=1 otherwise) gives a nonintegral rational
trace and excludes characteristic-zero torsion, with all rows and
changed seed actually recomputed/rescreened. That fixed repair alone
is not a finite-field order certificate. The uniform supplier above
is stronger: on its continuing branch it certifies the required large
odd local H-powered orders and excludes this small-torsion supply gap.
Neither result certifies a balanced additive coordinate profile.

Finally, execute the seed-side recurrence startup for TWO supplied
actual degree-d=O(sqrt J) equations, adding their construction cost.
The coordinate substitution in z^i and bar(z)^i has the triangular
spectral support a+b<=d of size O(d^2). Weighted product trees acquire
a scalar constant-one denominator Q(S), both numerators, and ALL
required starts in soft d^2, including coincident spectral bases.
No spectral-node difference is inverted. Simultaneous Pade/gcd in S
cancels spectral poles; it does not decide common zero coefficients
at the SAME seed index. Expanding both sequences through L, scanning
joint gcds and routing every saturated candidate through actual F_B
MPE/original-row localization completes the test in soft(J+L), even
with extraneous ideal intersections. This is worse than the baseline.
The moving norm coordinate is t^i, not a fixed conic parameter.

Primary Popov/interpolation, generic-ideal reduction and 2024/2025
m-adic Groebner algorithms were checked with actual explicit inputs,
field/pivot hypotheses, preprocessing and growing dimensions. Their
fast quotient operations do not supply the long same-index query.
The order supplier, modulus control and ideal acquisition are paid
positive intermediate results; the terminal query remains unacquired
at soft k. No one-sixth factoring theorem, complete bit-cost/Lean
composition, or absolute novelty claim is made. Preserve all earlier
prefixes, frozen entries and concurrent RH work.

Exact sources and independent PASS reviews (scratch evidence):

- [Uniform torus supplier](/tmp/semiprime-quadratic-ideal-20261024/torus-order-supplier.md), SHA256 `1f3033cc85c1b6798a188daa7b7c32d702b87d2cb3401e3e1f1afe6cb3a4e9bc`; [review](/tmp/semiprime-quadratic-ideal-20261024/torus-order-supplier-review.md), SHA256 `f84298cac56e9f028828ab69494e408d3fbe9d288be57b7a3688b14cf7fd4de6`.
- [Native norm-fiber ideal and primary literature](/tmp/semiprime-quadratic-ideal-20261024/ideal-literature.md), SHA256 `90f760d067f9de61a2950289c4f8aceba013cba521a2e4078053c2c2916ef77b`; [review](/tmp/semiprime-quadratic-ideal-20261024/ideal-literature-review.md), SHA256 `b922249b3fa55c5db826a8f86c2019f05ed49b0e41628198721e1c29b0924b1b`.
- [Coordinate point ideal and torsion repair](/tmp/semiprime-quadratic-ideal-20261024/point-ideal.md), SHA256 `eefa209ef7189a374cf3eaefe4fb85b2376d7f85814f72fdc90fe585df504f11`; [review](/tmp/semiprime-quadratic-ideal-20261024/point-ideal-review.md), SHA256 `187bc96f19f9dfa2fec2b6a0abb2c3cad2c50b47e4c5919afab92083a06d3342`.
- [Initialized ideal/seed query](/tmp/semiprime-quadratic-ideal-20261024/ideal-seed-query.md), SHA256 `25b326ed8a0dd0c0b3f81a7b997c130c79baec13b0b68f077ec0643b8f20159a`; [review](/tmp/semiprime-quadratic-ideal-20261024/ideal-seed-query-review.md), SHA256 `5ff414a79da8b0520321b8a192ad5f2a01f4b6f7da4c87818f3d0f3fd7cff6c6`.
