
## 2026-10-24: compact recurrence acquisition and the remaining coverage constraint

This pass paid a concrete quadratic two-list recurrence in soft O(m),
then proved that this particular family fails universal coverage. The
square-LCM projection gives a useful uniform structural refinement, but
neither result reduces the cost of the original guaranteed query. Its
current complete evaluation still costs soft O(m^1.5), and the sixth-rate
factorization theorem and full bit/Lean composition remain open.

Let K=lcm(1,...,m), M=K^2, and rho=beta^M for the prepared beta with
nontrivial coprime odd local orders. Sieve, factored product tree and this
single exponentiation cost soft m. For any d<m^3 and r=d/gcd(d,M), a
surviving prime p<=m would force gcd(d,M)>=p^(2 floor(log_p m))>m,
hence r<m^2. Therefore the existing order screen either factors or
certifies r_P>16m^2 with no prime factor <=m. Its coindex
(P-1)/r_P<m/16 then proves r_P is EXACTLY the full m-rough part of P-1,
with one or two prime factors counted with multiplicity. The larger
factor's order is not assigned this shape. The optional q=rho^(m^2)
interface requires and receives its own paid order screen.

All projection kernels are closed. If beta^M=1 globally, a one-path
descent through the known prime-power factors of M either separates
the primes, retains the old base with a smaller annihilator, or retains
a powered base with nontrivial coprime orders and the complementary
annihilator. A prime-power leaf cannot support two such orders. The
whole descent costs soft(bitlen M), not one full-length power per leaf.
This factored-kernel method and smooth purification were already known;
the square-LCM self-certificate is a refinement at the same asymptotic cost.

The concrete alternate recurrence uses f_N(x)=x(N-x), with two lists
S={f_N(mb):1<=b<=m}, T={f_N(a):0<=a<m}. For h=1,m, actual group values
z_b=gamma'^(f_N(hb)) obey

    z_(b+1)=z_b*R_b,
    R_(b+1)=R_b*gamma'^(-2h^2),
    R_0=gamma'^(hN-h^2).

Thus all inputs and monic cross-evaluation cost soft m. Here gamma' is
the separately guarded full-smooth projection from the candidate report,
not an unguarded new base. Every individual positive gap is

    Delta=(mb-a)(N-mb-a),  0<Delta<=m^2 N.

Its short bit length licenses the unconditional 31/192 annihilator
consumer on gamma' after a saturated leaf. The original exponent M*Delta
is longer and is NOT passed to that short-decoder theorem. For a prime
residual order r>m^2, a hit exists exactly when N mod r belongs to the
interval [m,m^2+m-1] (on the guarded r>16m^2 branch). A composite order
can additionally split across the two factors of this SAME difference.
Different pairs covering different prime factors are not enough.

Universal coverage of these quadratic lists is now DISPROVED, not left
as an open conjecture. The certified input is

    P=900143, Q=909863, N=819006810409, m=97, beta=4;
    ord_P(beta)=450071, ord_Q(beta)=454931.

Both orders are prime, exceed 16m^2, and their product exceeds 256m^4.
The actual full-smooth projection preserves them and the initial screen
has NoHit. All v=mb+a lie in [97,9505], but N has residues 9721 and
445212 modulo the two orders. Neither order divides mb-a or N-v, so
EVERY cross-difference is a unit. A fixed exact certificate verifies
primality, preparation, projection and these interval bounds; no matrix
scan or successful-example campaign is used. This refutes only the
specified construction, not other recurrences or factoring algorithms.

The inverse-tag combination was also evaluated exactly. With native
AB=1+m*rho_j and phase kappa_j, define
csharp=(kappa_j+rho_j*(j-1))/m. Its acquired target simplifies to
beta^(m*kappa_j)*q^(-csharp)=beta^(-m*rho_j*(j-1)). The own hit is
therefore beta^[m*rho_j*(j+mh-1)]=1, the ordinary weighted Fermat ray.
The h range is still m^2 and the bases vary by row. Zero-multiplier
exceptions retain their cheap original-row queries. This is an exact
algebraic reduction of the chosen fusion, not an algorithmic lower bound.

The two-factor rough branch admits cheap lists {uN:1<=u<=m} and
{v:-m<=v<=m} that cover each rough prime factor separately by circular
Dirichlet approximation. A simultaneous small-order test of all their
ratios would be useful, but remains unacquired; the explicit product
action has soft m^2 bit cost. The prime residual branch needs a separate
coverage theorem. These missing operations are not supplied by the
square-LCM certificate or the paid second-difference recurrence.

Reviewed scratch reports, exact fixed replay and preservation validator
are in /tmp/semiprime-compact-cover-20261024. Candidate report coverage
status is superseded by quadratic-counterexample.md. Preserve all prior
prefixes, 270 frozen entries and concurrent RH work. No broad Lean build,
backend expansion, commit or push was performed in this pass.
