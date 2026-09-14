# RiemannGaussian agent guide

## Project mission

RiemannGaussian is a research project seeking a complete, kernel-checked Lean
proof of the Riemann hypothesis. The target is Mathlib's
`RiemannHypothesis`; finite models, numerical certificates, asymptotic
experiments, and reformulations are useful only when they strengthen a
rigorous chain to that target.

The proof is not complete. The generated dashboard in
`docs/proof-status.svg` is the canonical compact status summary. At present,
the Gaussian/Weil and Suzuki/contour branches prove that the complete
safe-axis logarithmic defect is asymptotic, with `o(1)` error, to its positive
Poisson linearization, which is exactly height-scaled Blaschke derivative
variation. A checked dyadic Tauberian theorem now identifies decay of those
quantities with `H(T) / T → 0`, where `H` is cumulative upper spectral height.
The literal correctly normalized arithmetic Suzuki `Psi` is now identified
with the transport hinge model, and Lean proves it strictly positive on an
unconditional nonzero punctured neighborhood of the origin. Lean also derives
the transport smooth curvature as the second derivative of the literal
Archimedean term on positive time and proves its exact tail normalization with
computed frozen base value and slope. At the canonical first-event base
`t = log 2`, Lean now proves the exact event cut and strict negativity of the
frozen slope, so the literal tail-positivity criterion has no remaining
base-data assumptions. The literal frozen base value is also proved greater
than `7 / 125`, and the first frozen slope is greater than `-3 / 10`. Exact
curvature bounds then prove the synthetic cutoff-one transport gap strictly
positive, so cutoff zero and cutoff one are both discharged. The remaining
criterion begins at cutoff two, where every prefix contains a future
von Mangoldt event. Lean now identifies the mass and log-moment of every such
complete prefix with exact finite Abel transforms of `Chebyshev.psi`, proves
that its canonical transport point solves the literal Archimedean
slope-matching equation, and rewrites the open gap as the Archimedean value
plus a centered Chebyshev log-moment. Lean now evaluates the continuous
`psi(x) = x` part of that moment in closed form and isolates the remainder as
one explicit boundary term and signed integral against `psi(x) - x`. Exact
Chebyshev mass and Archimedean slope bounds now locate every canonical center
at `r >= log N - 2`; consequently the elementary derivative kernel is
nonnegative and strictly decreasing on every unresolved prefix. Its negative
derivative is a second strictly positive kernel. A checked
absolute-continuity argument rewrites the open moment through the cumulative
error `integral_1^x (psi(u) - u) du`, and a finite Abel identity identifies
that primitive with an exact triangular von-Mangoldt sum minus
`(x^2 - 1) / 2`. Further exact curvature and Chebyshev-mass estimates trap
the canonical center at every endpoint `N` in
`log N - 2 <= r_N < log N + 5`; hence the endpoint coefficient left outside
the cumulative moment is at most `5 * N^(-1/2)` in absolute value. The open
arithmetic statement is therefore a uniform two-level cumulative PNT-error
bound against positive kernels, with its endpoint coefficient now controlled.
Lean further proves that the complete cumulative moment is at most
`45 * sqrt N` in absolute value, the direct boundary term is at most
`25 * sqrt N`, and the full centered PNT remainder is at most `70 * sqrt N`.
Consequently that remainder divided by `N` tends to zero along the canonical
centers. The smooth baseline is now split exactly into a nonnegative
exponential convexity reserve and a lower-order term. The latter is bounded
by an explicit logarithmic envelope and is `o(sqrt N)`. Hence Lean proves the
dimensionless asymptotic frontier
`gap_N / sqrt N = 4 * (exp(delta_N/2) - 1 - delta_N/2) +
PNTError(r_N,N) / sqrt N + o(1)`, where `delta_N = r_N - log N`.
The center equation is now coupled to the same arithmetic measure: if
`E_mass` and `E_log` are its weighted mass and log-moment errors, Lean proves
exactly `PNTError(r_N,N) = E_log(N) - r_N * E_mass(N)` and proves
`E_mass(N) / sqrt N = 2 * (exp(delta_N/2) - 1) + o(1)`. Lean now performs the
corresponding Legendre elimination exactly. For the corrected mass ratio
`q_N = exp(delta_N/2)` and relative entropy
`H(q) = q * log q - q + 1 >= 0`, the literal finite gap is
`gap_N = E_endpoint(N) - 4 * sqrt N * H(q_N) + smooth_correction_N`, where
`E_endpoint` is a direct finite weighted von-Mangoldt sum and the source-exact
correction is `o(sqrt N)`. The missing arithmetic theorem must show that this
fixed-endpoint error dominates the entropy cost uniformly and ultimately
derive a genuine global zero-location constraint. Lean further proves the
quantitative upper bound
`4 * sqrt N * H(q_N) <= (E_mass(N) - smooth_slope(r_N))^2 / sqrt N`, so a
specific fixed-endpoint quadratic mass--moment inequality is sufficient for
every gap and for the uniform tail. Its premise is open and may be strictly
stronger than the exact entropy condition. The fixed-endpoint error now also
has a checked discrete work law
`E_endpoint(N+1)-E_endpoint(N) = D_N-log((N+1)/N)E_mass(N)`, with every smooth
drift `D_N >= 0` and strictly positive evaluated initial margin at `N=2`.
Lean telescopes this into initial margin plus cumulative smooth drift minus
cumulative signed mass-error work, and proves a corresponding block-work
inequality sufficient for the literal tail. For the literal weighted
Chebyshev logarithmic-average error `A_N`, Lean now proves exactly
`E_endpoint(N) = -A_N-log(N)-4` and identifies the cumulative signed work as
`A_N+log(N)-log(2)+4*sqrt(2)+sum D_j`. The exact entropy condition and the
sufficient quadratic majorant are therefore explicit quantitative upper
bounds for this single logarithmic average. Lean further proves
`0 <= D(b,b+1) <= b^(-3/2)` for `b >= 1`, so the smooth drift series is
summable and cumulative signed work minus `A_N+log(N)` converges to an
explicit finite constant. The smooth term therefore cannot provide an
unbounded margin. Lean now extends the literal formula for the logarithmic
average to every real endpoint `b >= 1`, proves each real logarithmic Mellin
atom integrable, and evaluates its weighted integral as the corresponding
von-Mangoldt Dirichlet term divided by `(sigma - 1/2)^2`; the square-root main
term is exactly `4/(sigma-1)`. Lean now also proves absolute summability of
the supported atom norm integrals, performs the infinite sum-integral
exchange, and identifies the complete transform on every real `sigma > 1`
with `(zeta'/zeta)(sigma)/(sigma-1/2)^2 + 4/(sigma-1)`. After exposing every
completed-zeta pole and Archimedean term, Lean proves that this same literal
arithmetic integral recovers the genuine spectral-xi negative logarithmic
derivative at `-i(sigma-1/2)`. Lean also proves genuine integrability and the
global substitution `x=exp(t)`, then complexifies the literal one-sided
Laplace transform on `Re z > 1/2`. It proves integrability of the parameter
derivative, differentiation under the infinite integral, and holomorphy. The
real-ray zeta response extends by the identity theorem throughout that same
half-plane, where the transform recovers the genuine spectral-xi negative
logarithmic derivative at every corresponding complex spectral point. Lean
now cancels the apparent pole at `z=1/2` and constructs a zero-adaptive
completed continuation whose open holomorphy domain contains the closed safe
half-plane and genuinely crosses to `Re z<1/2`. It agrees with the literal
integral on `Re z>1/2`, recovers spectral xi throughout its holomorphic
domain, and has residue `m_rho/(rho-1/2)^2` at every nonzero shifted zeta-zero
coordinate. The original integral is not asserted to converge in the
continued region. Lean now removes the inherited `z^(-2)` normalization and
proves that the pole-cleared response has residue `m_rho` at every shifted
nontrivial zero, without an exceptional-coordinate hypothesis. Applying the
fixed-positive-time heat weights to these arithmetic residues gives exactly
the genuine spectral-xi heat residues, and their absolutely convergent series
sums to the complete existing fixed-time heat. In the same shifted coordinate,
Lean now derives the smooth boundary heat kernel and its full real derivative,
proves its Cauchy--Green source is nonzero on the critical boundary, and proves
an exact arithmetic area--boundary identity for the heat-weighted pole-cleared
response on every zero-free rectangle. Lean also isolates each xi-zero
puncture and proves its shrinking circle integral recovers the exact
moving-kernel residue. It now proves the rectangular base case for excision:
four zero-free rectangles glue around one shrinking square, the square
boundary has the same exact residue limit, and the resulting improper
four-piece area integral converges to the outer boundary minus that residue.
It now proves the same fixed-radius and improper identities for the smooth
heat kernel times an arbitrary principal part `L / (z-c)`, providing the
termwise interface needed for finite principal-part regularization. Lean now
constructs that finite regularization unconditionally on every positive
shifted-coordinate slab of bounded imaginary height: the finite window is
proved complete for the xi divisor, every local multiplicity-weighted
principal part is subtracted, and one analytic representative patches the raw
remainder across all selected zeros. The heat-weighted response is therefore
a proved finite sum of the exact weighted principal parts plus one weighted
analytic remainder away from the divisor. Lean proves the integrability
prerequisite: every weighted principal-part source is locally Lebesgue
integrable through its pole, the project's iterated rectangular area equals a
genuine complex-plane set integral, and the actual finite-window arithmetic
source is integrable through its complete finite xi divisor. Lean also
constructs a single rectangle minus the finite union of common-radius complex
balls and proves its actual-source integral converges to the full planar area.
A checked half-open-square decomposition now identifies the termwise
shrinking-square approximation with that same ordinary through-divisor limit.
The resulting parameter-free finite Cauchy--Green identity states that the
actual arithmetic area equals the outer boundary minus the complete finite
multiplicity-weighted heat-residue sum; the literal common-ball integral
converges to this value. Lean now also retains exactly the selected off-axis
half-divisor on every eligible negative-real rectangle. The real part of the
selected finite heat sum is nonnegative and is strictly positive when its
window contains an off-axis zero; the sum converges to the existing
RH-equivalent boundary-heat total and equals an explicit arithmetic
boundary-minus-bulk functional. Lean now constructs canonical cofinal
rectangles using explicit finite real-coordinate extrema and the existing
quantitative zero-free heights. The corresponding actual boundary-minus-bulk
sequence converges to `2*pi*i` times the complete detector, and its convergence
to zero is equivalent to RH. Its real part is identically zero, while its
imaginary part is exactly `2*pi` times the selected finite heat sum. Lean proves
this scalar is nonnegative, monotone along the quantitative heights, strictly
positive when a window contains an off-axis zero, and zero exactly when that
window is empty. Lean now also constructs a genuine near-edge half-strip
exhaustion: the horizontal sides converge to `-1/2` and `0` while staying an
explicit positive distance from the bounded-height divisor, the vertical
height tends to infinity, and every fixed selected zero enters eventually.
Each stage satisfies the exact filtered positive Cauchy--Green identity.
Lean now passes those non-nested filtered sums to the complete detector by
dominated convergence and obtains a global near-edge arithmetic
boundary-minus-bulk limit. Lean also splits that functional exactly into four
named oriented boundary sides and one bulk term; its imaginary part is
stagewise nonnegative, strictly positive when a selected zero is present, and
converges without height normalization to the complete detector scalar. Lean
now proves a uniform exponential bound for the pole-cleared response across
both selected horizontal sides, including the Archimedean digamma correction.
The fixed-positive-time Gaussian dominates this bound, so both horizontal
integrals tend to zero unconditionally. The live contour frontier is therefore
exactly the two vertical sides minus the bulk. Lean now also splits both the
weighted response and its source pointwise into the genuine xi logarithmic
derivative and the explicit Archimedean regular correction. The regular
correction is analytic on every selected rectangle, so its boundary equals
its bulk exactly; its horizontal sides vanish by the same Gaussian mechanism,
and its vertical-minus-bulk term tends to zero. Subtracting the entire regular
piece leaves the unnormalized detector limit unchanged. The live three-term
remainder is therefore concentrated in the `xi'/xi` component. Lean now
proves this at the integral level rather than only pointwise: both selected
vertical lines lie in the zero-free pole-cleared domain, their interval
integrals split exactly, the bulk split is justified through genuine planar
integrability, and the regular-subtracted functional equals the two explicit
xi-logarithmic-derivative vertical terms minus the explicit xi source bulk at
every stage. This literal three-term functional retains the unnormalized
detector limit. Lean now takes its imaginary part through every integral using
proved interval and planar integrability. The result is a fully real scalar:
two vertical integrals of the real heat kernel times `Re (xi'/xi)`, minus an
explicit planar integral involving both real and imaginary logarithmic-
derivative components. Lean proves that the bulk coefficients are exactly the
two partial derivatives of the real heat kernel, so the remaining source is a
first-order heat-gradient pairing. Turning that pairing into a Green/Dirichlet
or explicit-formula identity with an unconditional vanishing estimate remains
open arithmetic rigidity. Lean now also defines the shifted xi log-norm
potential `U(a,y) = log |xi(1/2+a+I*y)|` and proves away from the divisor that
`U_a = Re (xi'/xi)` and `U_y = -Im (xi'/xi)`. The finite bounded-height divisor
inside every selected rectangle is proved planar-null, so the off-divisor
identity promotes to an almost-everywhere equality, the gradient pairing is
genuinely integrable, and its ordinary planar integral equals the explicit xi
bulk. Both vertical boundaries are zero-free, making the entire live scalar
exactly a boundary-minus-`grad K · grad U` functional with the same
unnormalized detector limit. The xi functional equation and conjugation
symmetry now prove `U` even in its shifted real coordinate; its horizontal
derivative and the real heat kernel are odd, so their boundary product is
even. Lean uses this to reflect the near-`s = 0` left boundary to positive
shifted coordinates in `(1/4, 1/2)`, equivalently actual xi coordinates in
`(3/4, 1)` tending to `1` from below, without changing any finite scalar or
its detector limit. This does not enter the absolute Dirichlet-series region.
Lean further differentiates the reflection symmetries and proves the complete
pairing `grad K · grad U` odd in the shifted real coordinate. Both boundaries
and the entire bulk are now reflected, with genuine through-divisor planar
integrability proved on the positive rectangles. Thus every finite live
scalar is an exact boundary-plus-gradient functional wholly in actual xi
coordinates `1/2 < Re s < 1`; its inner edge tends to `1/2` from above and its
outer edge to `1` from below. No decay in that open strip has been proved.
Lean now also removes the upper-quadrant restriction from the existing paired
Dirichlet-eta construction. On every point of `1/2 < Re s < 1`, its absolutely
convergent paired series equals `(1-2*2^(-s))*zeta(s)`, the elementary factor
is nonzero, and the paired series therefore retains exactly the zeta divisor.
Lean now differentiates that series by locally uniform holomorphic
convergence and obtains an exact quotient of convergent paired eta series for
`zeta'/zeta` at every nonzero zeta point of the same strip.
Lean also exposes the squared quotient energy without assuming an unproved
through-divisor `L²` estimate and develops a divisor-preserving `L¹` radial
flux. Paired eta has exactly the zeta analytic order at every
nontrivial zero, and its normalized-bilinear flux on shrinking circles tends
to `2*pi` times the positive analytic multiplicity. The remaining frontier is
a global arithmetic cancellation or coercivity estimate for that flux inside
the complete live detector. The actual Gaussian boundary-heat weight is now
inserted into the literal eta quotient: finite selected flux windows recover
their exact heat-residue totals as the puncture radius shrinks, and these
limiting values converge to `2*pi` times the complete detector. Lean now
selects one positive common radius at each natural window height, proves every
selected integrand is simultaneously `L¹`, bounds the radius and flux error by
`1/(n+1)`, and proves the resulting single diagonal eta-flux sequence converges
to the complete detector. The chosen circles are now also proved to stay in
the positive eta half-plane and avoid its complete divisor. On those circles,
Lean proves exactly that the normalized radial quotient is one half the
radius times the radial derivative of `log |E|^2`. Genuine `L¹` integrability
transfers through this identity, and one sequence of finite heat-weighted
paired-eta log-norm variations converges to the detector. No arithmetic bound
forcing that variation to vanish has been proved. Lean now also constructs
the explicit finite paired-eta polynomials `E_N` and derivative polynomials
`D_N`, proves both converge locally uniformly on `Re s > 0`, and proves
`D_N / E_N` converges locally uniformly to the literal eta logarithmic
derivative on its exact zero-free domain. Lean now transfers this convergence
uniformly to every selected compact detector circle, proves the finite
denominators eventually stay nonzero and the finite radial integrands are
genuinely `L¹`, and selects growing truncations `N_n ≥ n`. The resulting
single sequence of finite paired-eta Dirichlet-polynomial flux windows
converges to the complete detector. On every selected finite denominator,
Lean now also proves the exact radial identity
`d/dr log |E_N|^2 = 2 Re(exp(i theta) D_N / E_N)`, transfers genuine `L¹`
integrability, and rewrites the complete diagonal limit as entirely finite
log-norm variations. No quantitative convergence rate or arithmetic bound
forcing that finite sequence to vanish is currently claimed.
Lean now also proves a domain-local Rouché comparison. Every nontrivial zeta
zero has an arbitrarily small positive-half-plane isolating circle on which
all sufficiently long finite eta sums are boundary-nonzero and their exact
logarithmic-derivative winding equals the genuine analytic zeta-zero
multiplicity. This preserves local divisor mass but supplies no global bound.
The nonzero winding is now converted into actual finite arithmetic roots:
for every nontrivial zeta zero, Lean selects growing indices `N_n ≥ n` and
zeros of `E_(N_n)` converging to that zeta zero with distance below
`1 / (n + 1)`. This is divisor persistence, not a zero-location estimate.
Lean now also identifies `E_N(s) / s` exactly with a finite positive-measure
Laplace partition function. Every positive-real-part finite eta zero obeys
exact exponentially tilted cosine and sine moment cancellations, and every
nonempty such zero has, after centering its support, total phase spread
strictly greater than `pi`. These constraints hold eventually along the
verified finite-root sequence converging to each nontrivial zeta zero. The
open problem is a global rigidity estimate strong enough to turn those
positive-measure cancellations into a zero-location restriction; the phase
bound alone decays like `1 / log N` and does not do so.
Lean now removes the truncation completely. It constructs the fixed measure
obtained by restricting Lebesgue measure to the disjoint union of all
`(log(2n+1), log(2n+2)]`, proves the complex Laplace kernel genuinely
integrable against it throughout `Re s > 0`, and proves its transform is
exactly paired eta divided by `s`. Thus every nontrivial zeta zero is an exact
zero of this one infinite positive-measure transform, and both of its complete
tilted Fourier moments vanish there. The live zero-location problem is now
literal rigidity of this explicit arithmetic measure, not passage from finite
roots to a limiting transform.
Lean now extracts the first direct zero-location inequality from that fixed
measure. The first interval gives an explicit tilted-mass lower bound, measure
domination gives the exact complete first-moment upper bound, and the
Lipschitz estimate for cosine turns exact cancellation into
`rho.re * (1 - exp (-rho.re * log 2)) <= |rho.im|` for every nontrivial zeta
zero. This unconditionally excludes real nontrivial zeros, but is far too weak
to force the critical line. The live task is to exploit more of the interval
arithmetic than this first-moment bound retains.
Lean now retains the quadratic cosine remainder and the complete second
exponential moment. It proves the strictly stronger threshold
`rho.re * sqrt (1 - exp (-rho.re * log 2)) <= |rho.im|`, together with its
equivalent squared form, at every nontrivial zeta zero. This is verified direct
progress beyond the first-moment estimate, but it remains vertical rather than
horizontal and therefore gives no approach to `rho.re = 1/2` by itself.
Lean now uses the functional-equation partner to reach the horizontal
direction. The same ordinate annihilates the fixed eta measure at tilts
`rho.re` and `1 - rho.re`. Their difference factors as an exponentially
damped hyperbolic sine. If `rho.re != 1/2`, sign normalization produces an
explicit density strictly positive on the complete eta support whose cosine
and sine moments both vanish at the zero's ordinate. This is a conditional
off-critical certificate, not an exclusion theorem. The live arithmetic task
is no longer left as a generic positive-measure question. Lean now partitions
the full positive half-line exactly into the eta support and its omitted
logarithmic gaps, identifies the complex horizontal kernel with that positive
density times its Fourier phase, and computes its full transform as
`2*a^2 / (((1/2+a)+I*y)*((1/2-a)+I*y))`. At every zeta zero the support
transform vanishes, so the gap transform must equal this rational value; it is
nonzero for an off-critical zero. The live task is a quantitative estimate
from the alternating logarithmic-gap geometry that contradicts this exact
target. No such estimate is currently proved.
The abstract gaps are now eliminated as well. Lean identifies them exactly as
the pairwise-disjoint intervals `(log(2n+2), log(2n+3)]`, proves the associated
interval Laplace series absolutely summable on `Re s > 0`, and proves that its
literal even-odd Dirichlet series is `1 - pairedEtaCore(s)`. Every nontrivial
zero and its functional-equation partner therefore make this gap series equal
exactly `1`; the horizontal gap transform is the complementary difference of
the two interval series and remains nonzero off the line. The live task is now
a termwise arithmetic estimate on these explicit intervals, not an abstract
support-complement argument.
Lean now has the first such finite estimate. For the first `N` support and gap
sums it proves exactly `E_N(s)+G_N(s)=1-(2N+1)^(-s)`. It realizes the remaining
eta tail as a restricted positive measure and obtains the closed bound
`||G_N(rho)-1|| <= (||rho||/rho.re+1)*(2N+1)^(-rho.re)` at every nontrivial
zero. Applying the same theorem to the functional-equation partner replaces
the exponent by `1-rho.re`; these decay exponents are distinct under the
off-critical hypothesis. This remains an upper-bound certificate, not an
exclusion. The live task is to prove a lower bound or sharp asymptotic that
couples the two complementary rates and cannot hold when they differ.
Lean now also extracts the Euler cancellation hidden by that absolute tail
bound. The support-minus-gap summand is the consecutive second difference
`(2n+1)^(-s)-2(2n+2)^(-s)+(2n+3)^(-s)`, its complete series is exactly
`2*E(s)-1`, and it equals `-1` at every nontrivial zeta zero. Solving this
identity together with the finite telescope gives exactly
`G_N(rho)-1=-(2N+1)^(-rho)/2+(-1-D_N(rho))/2`. The partner obeys the same
formula at exponent `1-rho.re`. The immediate analytic task is to prove that
the second-difference tail is smaller by one endpoint power. That expected
individual asymptotic is not itself a zero-location contradiction; the live
arithmetic task remains a rigorously proved coupling that cannot accommodate
both complementary off-line evaluations.
Lean now proves the required extra-power estimate rather than assuming it.
For every `Re s>0`, the Euler second-difference tail from cutoff `N` has norm
at most `2*||s||*||s+1||*(2N+1)^(-Re(s)-1)`. Hence every nontrivial zero obeys
the sharp bound
`||G_N(rho)-1+(2N+1)^(-rho)/2|| <=
||rho||*||rho+1||*(2N+1)^(-rho.re-1)`, and the partner obeys the corresponding
bound at real exponent `1-rho.re`. This rigorously confirms the research
warning: unequal raw-tail rates are the expected compatible endpoint
asymptotics, not a contradiction. Lean now packages the exact complex limit
`(2N+1)^s*(G_N(s)-G(s)) -> -1/2` and the corresponding positive scaled-norm
limit. A generic checked theorem proves that independent eventual two-sided
multiplicative comparability of two such raw errors forces their decay
exponents to agree. Applied to a zero and its functional-equation partner,
the explicitly defined complementary eta-gap comparison principle forces
`rho.re=1/2`. Conversely, RH makes every zero equal to its reflected partner,
so Lean proves that the global comparison principle is exactly equivalent to
Mathlib's literal `RiemannHypothesis`. No theorem proves either open direction;
comparability is conjecture-strength, not a routine estimate. The raw
cutoff-tail analysis is therefore exhausted as a source of contradiction.
Lean now begins the symmetry-aware pivot by proving an exact finite Gaussian
Gram identity for the actual first `2N` alternating eta atoms. Their genuine
Gaussian `L²` norm equals a completely explicit arithmetic double sum, and
the same checked theorem proves that sum real and nonnegative. This is generic
finite Gram structure and does not relate `sigma` to `1-sigma`. Lean now also
constructs the finite positive logarithmic eta measure and proves its Laplace
transform exactly equals `E_N(s)/s` away from the origin. A checked Fubini
exchange and Gaussian Fourier evaluation identify the Gaussian norm of this
normalized finite eta polynomial with the strictly positive double kernel
`sqrt(pi/tau)*exp(-sigma*(t+u))*exp(-(t-u)^2/(4*tau))` over two copies of the
eta measure. Lean proves all integrability hypotheses, nonnegativity, and the
fully expanded finite sum over pairs of support intervals. This remains
generic positive-Laplace structure and does not relate `sigma` to `1-sigma`.
Lean now differentiates that genuine double integral twice in `sigma`. Its
first derivative is exactly the negative first logarithmic-time moment and its
second derivative is exactly the positive second moment. For every nonempty
truncation at positive Gaussian time, both moments are strictly positive; the
raw Gram profile is therefore strictly decreasing and strictly convex. Lean
also proves the exact Cauchy--Schwarz moment determinant
`M_1(sigma)^2 <= G(sigma)*M_2(sigma)`, identifies the second derivative of
`log G` with its normalized nonnegative determinant, and proves global
log-convexity of the raw profile. These remain generic positive-Laplace facts.
Lean also proves that its values at `sigma` and `1-sigma` are equal exactly when
`sigma=1/2`. This is a closure interface, not the missing coupling: no theorem
derives the complementary equality from zeta, xi, or the finite eta zero
condition.
Lean now derives the correct completion rather than postulating it. For
`C(s)=s*(1-s)*GammaR(s)/(1-2*2^(-s))`, the actual function `C(s)*E(s)` is
proved locally equal to the entire xi normalization throughout
`0 < Re(s) < 1`, and the previously exposed regular correction is exactly
`C'/C`. Every iterated derivative inherits xi's functional-equation parity
and conjugation. At each nontrivial zero of arbitrary multiplicity `m`, Lean
uses the exact analytic order to eliminate every lower Leibniz term and proves
the completion-weighted leading eta derivatives at `rho` and
`1-conj(rho)` are exact conjugates up to `(-1)^m`. The corresponding norm
identity is also checked. This is the genuine completed local coupling, but it
is compatible with off-critical zeros and supplies no inequality between the
unweighted arithmetic moments.
Lean now proves that every logarithmic-time moment
`integral t^n*exp(-s*t) dmu(t)` of the fixed infinite eta measure is integrable
for `Re(s)>0`, and that it is exactly `(-1)^n` times the `n`th derivative of
the eta Laplace partition. At every nontrivial zero, that partition has the
full genuine zeta-zero multiplicity, all lower derivatives vanish, and the
leading moment is nonzero. The completed local coupling is therefore proved
as an explicit completion- and spectral-parameter-weighted relation between
the leading moments at `rho` and `1-conj(rho)` for arbitrary multiplicity.
Lean now splits every such moment into the explicit eta support and its
omitted logarithmic gaps, and proves the full positive-half-line value exactly
as `n!/s^(n+1)`. At a zero of multiplicity `m`, the gap moments equal the full
moment for every `k<m` and differ for the first time at `k=m`. The completed
partner identity is checked as an exact relation between these first nonzero
gap-moment defects. The next hard input must prove an independent quantitative
inequality for those explicit gap-interval defects that cannot hold at
complementary off-critical tilts.
Lean now expands every gap moment as an absolutely convergent sum over the
literal intervals `(log(2n+2),log(2n+3)]`. The positive real envelope is
computed as `n!/sigma^(n+1)`, and the first gap gives the strict saving
`(log 3-log 2)*(log 2)^n*exp(-sigma*log 3)`. This yields a checked one-sided
upper bound for the first nonzero defect at every zeta zero. It is not the
missing rigidity: the next hard input is a complementary-tilt comparison or
lower bound that combines with this saving to force `sigma=1/2`.
Lean now packages that nonzero leading defect canonically and combines its
first-gap bound with the exact completed partner symmetry. The two raw defect
norms have the exact reciprocal completion-weight ratio, while their common
positive completed magnitude is bounded by the explicit first-gap envelope at
both complementary tilts. This closes the purely symmetry-driven comparison;
the remaining hard input must be an independent matching lower bound or strict
tilt incompatibility that excludes `sigma != 1/2`.
Lean now retains phase through arbitrary finite support prefixes. For every
`0<theta<1`, it splits the full order-`m` moment exactly at any cutoff `N` and
bounds the literal tail by
`exp(-(1-theta)*sigma*log(2N+1))*m!/(theta*sigma)^(m+1)`. The resulting
nonnegative finite lower certificates converge to the exact nonzero defect
norm and are eventually positive. Their completed versions at complementary
zeros converge to the same positive magnitude while satisfying the opposite
first-gap upper bounds. The remaining hard input is now a uniform
tilt-separating estimate on these finite phase-sensitive prefixes; convergence
alone is compatible with an off-critical pair.
Lean now proves those finite order-`m` prefixes are signed iterated derivatives
of the genuine finite positive eta Laplace partition. It defines their full
complex completed partner residual, including parity and conjugation, and
rewrites it exactly as the two discarded support-tail errors. Its norm is
bounded by the sum of the two explicit completion-weighted `theta`-split tail
envelopes, so the complex residual tends to zero. This is the phase-sensitive
finite arithmetic target; the next hard input must obstruct that decay
uniformly away from `sigma=1/2`. The proved decay itself is compatible with a
hypothetical off-critical zero and is not such an obstruction.
Lean now also chooses the split as
`theta_N=(m+1)/(sigma*log(2N+1))` after its explicit admissibility threshold.
The resulting checked tail envelope retains the full exponent `sigma` with
only a `log(2N+1)^(m+1)` loss and tends to zero. Lean propagates this sharper
bound to the finite lower certificates and to the complete complex partner
residual at both complementary tilts. This improves the quantitative
interface but supplies no independent lower or phase incompatibility.
Lean now inserts the exact derived eta completion into the infinite positive-
measure Laplace energy. Pointwise in the open strip, the resulting weighted
energy is exactly `|xi(s)|^2`; hence the functional equation gives a checked
complementary equality between explicit weighted sums of squared tilted
cosine and sine moments of the same arithmetic measure. Arbitrary finite
Gaussian windows of this energy are genuinely integrable, nonnegative, and
exactly symmetric under `sigma ↔ 1-sigma`. The completion weight depends on
the ordinate, and both sides vanish at a zero, so a new eta-specific
coercivity or phase estimate is still required.
Lean now proves the corresponding Gaussian Gram identity directly for the
fixed infinite eta measure, including sigma-finiteness, joint domination,
both Fubini orders, and the Gaussian Fourier evaluation. The raw infinite
Gram is an explicit nonnegative double integral with kernel
`exp(-sigma*(t+u))*exp(-(t-u)^2/(4*tau))`. Combining it with the completed
symmetry gives an exact balance law: the raw Gram at `sigma` minus the raw
Gram at `1-sigma` is the common completed energy integrated against the
difference of the two reciprocal completion weights. There is no remainder;
the measure is nonzero and supported at strictly positive logarithmic time,
so Lean now proves this raw Gram is strictly decreasing in `sigma`. It follows
that the global distortion is positive left of `1/2`, zero exactly at `1/2`,
and negative right of `1/2`. This zero-centered sign law is unconditional but
does not constrain a zero. Lean now localizes the infinite Gram at an arbitrary
ordinate `gamma` and proves the exact arithmetic kernel is the positive
zero-centered envelope multiplied by `cos(gamma*(u-t))`. It connects the
localized complementary norm difference, the reciprocal-completion-weight
distortion, and the difference of the two oscillatory arithmetic kernels in
one checked identity. Positive cosine phase preserves strict antitonicity in
`sigma`; negative phase strictly reverses it. At every nontrivial zeta zero
the localized energy integrand vanishes at its center, but the full integral
has no automatic sign. Lean now quantitatively controls the phase loss:
`|cos x-1| <= x^2/2` and the Gaussian estimate
`d^2*exp(-d^2/(4*tau)) <= 4*tau` give an explicit product-measure bound
`|G_(sigma,gamma)(tau)-G_(sigma,0)(tau)| <=
sqrt(pi/tau)*2*gamma^2*tau*M_sigma^2`. Hence localization is an
`O(sqrt tau)` perturbation at short proper time, and the localized completion
distortion converges to the signed zero-centered distortion. This is genuine
phase control. Lean now also handles the zero-sensitive opposite limit: after
division by `sqrt(pi/tau)`, dominated convergence identifies the localized
norm at `tau -> infinity` with the exact squared eta partition value at its
center ordinate. At every nontrivial zero this limit vanishes at both
complementary tilts, and so does the normalized localized completion
distortion. This leading vanishing is compatible with off-critical zeros. The
first multiplicity-sensitive asymptotic is now complete. If the zero has exact
multiplicity `m`, Lean proves every product difference moment below order `2m`
vanishes and the order-`2m` moment is exactly
`(-1)^m * choose(2m,m) * |M_m(rho)|^2`. The Gaussian Taylor sign cancels this
sign, giving the explicit strictly positive coefficient
`choose(2m,m) * |M_m(rho)|^2 / (4^m*m!)`. A sharp global exponential Taylor
remainder, an integrable product-measure majorant, and dominated convergence
prove that this is the actual limit of `tau^m` times the normalized localized
eta Gram. The corresponding actual scaled completion-distortion limit is the
difference of the coefficients at complementary zeros. Lean proves that this
difference vanishes exactly when their explicit completion weights agree.
Lean now packages those weights into a nonvanishing analytic reflection
multiplier `B(s)` for the literal positive eta Laplace partition. It proves
`P(1-s) = B(s)P(s)`, the exact reciprocal and conjugation laws, and the
explicit spectral--Gamma--eta factorization of `B`. Its squared norm is the
complementary weight ratio, so the actual distortion coefficient vanishes
exactly when `|B(rho)|^2 = 1`; the critical line implies this condition. The
horizontal logarithmic derivative of `B` is now computed throughout the open
strip. Lean cancels its apparent endpoint poles using the digamma recurrence
and rewrites it as a symmetric shifted-digamma term plus two explicit dyadic
resolvents. The same-ordinate log norm is antisymmetric about `1/2`, and its
horizontal derivative is exactly the real part of this pole-free expression.
Lean now proves that real part strictly positive throughout the whole open
strip at every absolute ordinate at least `8`. Hence the same-ordinate log
norm is strictly increasing there, and `|B(s)|^2 = 1` is equivalent to
`Re s = 1/2` in this high-ordinate region. For every nontrivial zero satisfying
that explicit height hypothesis, vanishing of the actual first localized
distortion coefficient is therefore equivalent to the critical-line
equation. Lean now also computes the exact squared norm of `B(1+it)` on the
outer boundary. Away from `t=0` and the explicit dyadic resonances, it proves
that norm strictly greater than one for every positive or negative ordinate.
The low-height proof uses exact Taylor and hyperbolic inequalities plus a
rational polynomial certificate; the high-height proof is elementary. Lean
then constructs a holomorphic reciprocal extension `F` with `F=1/B` in the
open strip. The eta zeros fill every dyadic outer-boundary singularity, and
Lean proves `|F(1+it)|<1` for every real `t`. The high-ordinate multiplier
estimate controls the horizontal sides of the low-height rectangle. A checked
maximum-modulus argument, with strictness forced by `F(1)=0`, proves throughout
the entire open strip that `|B(s)|<1`, `=1`, or `>1` exactly as `Re s<1/2`,
`=1/2`, or `>1/2`. Thus the low-ordinate rigidity gap is closed. At every
nontrivial zero, vanishing of the actual first localized distortion
coefficient is now equivalent to the critical-line equation without a height
hypothesis. The remaining work must derive that vanishing, or equivalently
unit norm at zeros, from an independent arithmetic or phase constraint. That
open input may not be assumed.
Lean now transfers this complete multiplier sign law back to the literal
leading Gaussian coefficients. At every nontrivial zero `rho`, the partner-to-
original coefficient ratio is exactly `|B(rho)|^2`; consequently the partner
coefficient is smaller, equal, or larger exactly when `Re(rho)` is left of, on,
or right of `1/2`. The remaining target is therefore the independent equality
of these two positive arithmetic coefficients. The exact ratio and its sign
classification do not supply that equality.
The high-ordinate analytic estimate is now quantitative. Lean sharpens the
horizontal derivative of `log |B(s)|` to the uniform lower bound `1/200` when
`|Im(s)|>=8`, and the real mean-value theorem transfers it to
`(1/100)*|Re(rho)-1/2| <= |log(a(rho#)/a(rho))|` for the two positive leading
coefficients. This is a coercive interface: an independent arithmetic upper
bound on the logarithmic ratio would control zero displacement. No such upper
bound, and no independent equality, is currently proved.
Lean now supplies a first non-circular finite upper bound for that same ratio.
A phase-sensitive finite eta moment prefix minus its rigorous tail envelope is
a lower certificate `L_N(rho)`, while the first-gap estimate gives an explicit
upper envelope `U(rho#)`. Whenever `L_N(rho)>0`, Lean proves directly from the
raw moment definition that `a(rho#)/a(rho) <= (U(rho#)/L_N(rho))^2`; existing
convergence makes the positivity condition eventual. For a right-half zero at
absolute ordinate at least `8`, this yields
`Re(rho)-1/2 <= 100*log((U(rho#)/L_N(rho))^2)` eventually. This is a genuine
finite arithmetic certificate, but no theorem yet makes its right side zero
or asymptotically small enough to imply RH.
Lean now replaces the coarse partner envelope by a phase-sensitive
prefix-plus-tail upper certificate `V_N` as well. The two squared quotients
`(L_N(rho#)/V_N(rho))^2` and `(V_N(rho#)/L_N(rho))^2` eventually enclose the
exact coefficient ratio; both converge to it and their width tends to zero.
The cutoff-balanced near-sharp version retains the full horizontal exponent.
Lean then proves a necessary correction: every valid finite upper enclosure
is strictly above `1` for a right-half zero, including an on-line zero, because
prefix-plus-tail is strictly larger than prefix-minus-tail. Thus the proposed
one-cutoff target `upper_N<=1` is vacuous and must not be pursued. Define the
intrinsic self-slack
`delta_N=(V_N(rho)/L_N(rho))^2-1`; Lean proves `delta_N -> 0` and proves that
`upper_N(rho,rho#)<=1+delta_N` is exactly the finite comparison
`V_N(rho#)<=V_N(rho)`. For a zero in the closed right half-strip, eventual
validity of this near-sharp finite-upper monotonicity is equivalent to the
critical-line equation. No theorem currently proves the arithmetic direction
of that equivalence.
Lean now also exploits a fact absent from those uncentered certificates: at a
zero of multiplicity `m`, every eta logarithmic moment below `m` vanishes.
Recentring the leading moment at `a_N=log(2N+1)` therefore preserves it exactly
while changing the literal tail integrand from `t^m` to `(t-a_N)^m`. A checked
translation of the Gamma integral yields the unconditional envelope
`exp(-Re(rho)*a_N)*m!/Re(rho)^(m+1)`, with no logarithmic-power loss and no
cutoff condition. It is strictly smaller than the balanced near-sharp bound
whenever the latter is valid. The centered finite lower and upper certificates
enclose the exact nonzero defect for every cutoff, converge to it, and have
width at most twice this new envelope. This sharpens the arithmetic interface;
it does not provide the missing complementary sign constraint.
The centered prefixes are now also coupled through the completed functional
equation. Lean defines their full complex finite partner residual and rewrites
it exactly as a signed sum of the two literal centered support tails, retaining
completion factors, parity, conjugation, and phase. Its unconditional envelope
is the sum of the two completion-weighted centered Gamma tails, tends to zero,
and is strictly below the older near-sharp completed-residual envelope whenever
both former cutoffs apply. This closes the representation step; decay alone is
compatible with an off-line zero, so the open step is an independent
eta-specific phase or sign theorem for this exact residual.
Lean also polarizes the completed finite prefix norm defect exactly as the
residual norm square plus twice the real cross-phase between the original
completed conjugate prefix and the residual. Consequently a negative norm
defect requires a strictly negative cross-phase; the nonnegative
residual-energy term cannot supply it.
Lean now translates every discarded centered tail by
`a_N=log(2N+1)`. The resulting measure is proved almost everywhere supported
on `u>0`, and the relevant Laplace and separated Fourier--Laplace integrands
are proved absolutely integrable. At `rho` and `1-conj(rho)`, the two tails are
exact complementary real tilts `rho.re` and `1-rho.re` of this same measure at
one Fourier frequency. Conjugation is reduced to frequency reversal and the
single relative cutoff phase `exp(2*I*rho.im*a_N)`. The completed residual is
exactly a common unit phase times one named coupled core, so their norms are
equal. Lean further combines the two moments into one absolutely integrable
function on that common measure. After extracting the critical half-tilt its
pointwise form is
`u^m*exp(-u/2)*(A_N*exp(delta*u)*exp(-I*gamma*u)
+B_N*exp(-delta*u)*exp(I*gamma*u))`, where
`delta=rho.re-1/2`. The residual norm is exactly the norm of this single
interference integral.
Lean now exploits the literal alternating interval geometry across cutoffs.
Writing `Delta_N=log(2N+3)-log(2N+1)`, the shifted tail measure at `N` is
exactly Lebesgue measure on its first interval `(0,w_N]` plus the shifted tail
at `N+1` translated by `Delta_N`, with `0<w_N<Delta_N`. Every shifted moment
therefore obeys an exact finite binomial transport formula. The completion and
phase factors align across both complementary tilts, producing a triangular
work law for the actual residual. Lean now closes that lower-order hierarchy:
for every `j<m`, vanishing of all complete eta moments through order `j`
forces the centered tail to be exactly the negative of its literal finite
centered prefix, at both complementary zeros. Hence
`R_N-R_(N+1)=head_(m,N)+sum_(j<m) choose(m,j)*Delta_N^(m-j)*P_(j,N+1)`,
where the head is supported on the single explicit interval `(0,w_N]` and
every `P_j` is a finite eta-prefix coupling with the original completion,
parity, conjugation, and phase data. No lower-order infinite tail remains.
The present sign-bearing target is an eta-specific coercive estimate or
cancellation law for this completely finite arithmetic identity. A valid next
step must retain the distributional zero contributions in any Green or
integration-by-parts argument; erasing them would merely erase the detector.
These estimates are not RH and do not exclude a finite or sparse off-line
divisor; a restatement, hidden limit interchange, or conditional implication
is not a substitute.
Lean has since isolated the top transported term, represented its remaining
prefix as one shifted-tail interference integral, and squared it into an exact
Hermitian Gram identity. Splitting that integral into the two complementary
components proves that the cross-phase defect is already bounded at the full
endpoint scale; the sole remaining target is the squared difference of their
magnitudes. The sharp centered-tail theorem now gives both component limits.
For every hypothetical zero with `Re(rho)>1/2`, the slower partner-normalized
amplitude difference tends to an explicit positive constant, and Lean proves
that the exact endpoint-scaled squared difference tends to positive infinity.
Thus the current frontier is an independent eta-arithmetic theorem forcing
that endpoint-scaled difference to remain bounded. Its off-line divergence is
proved; the required arithmetic boundedness is not.
Lean now also packages a Hilbert-space alternative. The squared magnitude
mismatch is invariant under the reflected partner, is identically zero at
every critical-line zero, and is nonsummable over cutoffs at every off-line
zero by the sharp odd-endpoint p-series threshold. Its local summability is
therefore equivalent to `Re(rho)=1/2`, and universal summability is explicitly
proved equivalent to RH. This is an equivalence, not progress on its open
direction. The concrete new research target is an eta-specific Gram, Bessel,
or orthogonality argument establishing that literal finite-arithmetic
summability without using zero locations.
Lean now removes the apparent infinite-tail and nonlinear-norm barriers from
that target. Lower-moment vanishing rewrites both component magnitudes as
literal completion-weighted finite centered prefixes. Their magnitude
difference is exactly the signed difference of their squared energies divided
by their total amplitude, even when that denominator is zero. The signed
energy numerator also equals the nonnegative top-prefix Gram energy plus one
explicit polarized cross phase. Hence the live target is square-summability of
this normalized signed finite energy defect; its arithmetic proof remains
open.
Lean now further collapses every binomially defined centered finite prefix to
one literal centered integral over the finite positive eta logarithmic
measure. The two completion-weighted complementary finite terms are integrals
of explicit integrable features on that common measure. Their signed energy
difference is exactly one integrable real rank-one Gram kernel over the product
measure, with every Fubini and conjugation step checked. Thus the live target
is square-summability of this signed finite eta Gram integral divided by the
total finite amplitude. The representation is unconditional; the summability
estimate remains conjecture-strength.
Lean now gives this finite Gram energy an exact consecutive-cutoff transport.
Its one-step work is the signed energy of the partner and conjugate increments
plus two explicit cross-flux terms against the successor features. A checked
absolute estimate contains only those increment energies and flux norm
products. Both component amplitudes tend to zero, so the work telescopes and
its ordered tail sums recover the signed energy, the normalized defect, and
the amplitude mismatch. The open target is a weighted eta-specific
summability or coercivity estimate for this local ledger; no sign for the flux
is currently proved.
Lean now removes the abstract consecutive differences from that ledger. Every
absolute-coordinate centered eta tail satisfies the exact head-interval plus
binomial successor-tail transport. Below the analytic zero multiplicity,
complete-moment vanishing changes all successor tails into literal finite
prefixes and cancels the top order. Both partner and conjugate energy
increments are therefore explicit completion-weighted works containing one
negative new support interval and only strictly lower-order successor
prefixes. The checked absolute energy-work bound has been rewritten entirely
in terms of these finite arithmetic increments and their successor fluxes.
Lean now proves those two component-increment series absolutely summable at
every nontrivial zero. The exact cutoff-shift asymptotic supplies the additional
endpoint power for the head and every lower-prefix transport term. Consequently
the increment energies, successor cross-flux products, and absolute signed
energy work are summable, and every energy tail has a genuine `HasSum`
reconstruction. This unconditional result is not the RH criterion: the total
amplitude in the normalized defect tends to zero. The current frontier is a
weighted coercivity or cancellation estimate that controls the quotient
`E_N / S_N` strongly enough to make its square summable without assuming zero
locations.
Lean now isolates the exact first weight needed for that strengthening. A
generic weighted-tail theorem applied to the absolute `HasSum` reconstruction
shows that summability of `(2N+1) * |J_N|` forces
`(2N+1) * |E_N| -> 0`. The amplitude imbalance is pointwise bounded by
`|E_N|`, while its checked sharp asymptotic diverges at this endpoint scale for
every off-line zero. Hence the weighted work series is summable exactly on the
critical line, and its universal summability is equivalent to RH. Treat this
as a reduction: the live arithmetic task is to prove the first-moment bound
without assuming zero locations, not to cite the equivalence as progress on
that open direction. Lean now discharges the local increment-energy portion
of that task. The literal extra cutoff-shift power proves both component
increments have summable `(2N+1)`-weighted squared norms, hence their signed
increment energy has a finite first absolute moment unconditionally. Since
`J_N` is exactly that increment energy plus the successor cross flux `F_N`,
the weighted flux series is summable exactly when the weighted work series is.
Thus the remaining RH-equivalent arithmetic target is specifically
`sum_N (2N+1) * |F_N| < infinity`: an eta-specific cancellation or coercivity
estimate for the successor coupling. Lean now realizes `F_N` exactly as the
integral of one explicit real Hermitian kernel over the finite positive eta
logarithmic measure. The kernel pairs the head-plus-lower-prefix arithmetic
increment with its completed successor feature. Its phase-free envelope is
integrable, dominates it pointwise, and gives a nonnegative cancellation
reserve satisfying `|F_N| + reserve_N = integral envelope_N`. Partner
reflection swaps the components and makes the signed energy, increment
energy, work, and flux odd; the absolute flux is invariant. The open estimate
is therefore the first moment of these literal finite kernel integrals. Do not
replace it by summability of the phase-free envelope: that loses precisely the
cross-component and within-integral phase cancellation that the proof needs.
Lean now splits each explicit finite work into its unique slow term and a
remainder. At multiplicity one the negative head is the slow term. At every
higher multiplicity it is the single top lower-order transport term, with
exactly one factor of `Delta_N`; the head and every strict lower term left in
the remainder have shift degree at least two. The two endpoint decays then
prove unconditionally that `sum_N (2N+1) * |R_N| < infinity` for the completed
remainder flux. Since `F_N = L_N + R_N`, Lean proves that the leading-flux
first moment is summable exactly when the full flux first moment is, locally
exactly on the critical line and universally exactly under RH. This is still
a reduction. The current open theorem is the eta-specific cancellation or
coercivity estimate for the isolated degree-one leading current `L_N`.
Lean now realizes that current by an exhaustive literal kernel construction,
without a simplicity assumption. If the analytic multiplicity is one, `L_N`
is the integral of a real kernel on the translated new-head measure times the
successor finite eta measure. If the multiplicity is at least two, `L_N` is
the integral of the degree-one-shifted Hermitian kernel coupling the order
`m-2` and order `m-1` centered features on two copies of the successor finite
eta measure. Integrability and both exact integral identities are checked.
The multiplicity-selected integral equals `L_N` for every zero and cutoff;
its first-moment summability is locally equivalent to the critical line and
universally equivalent to RH. The live arithmetic task is therefore to
control these explicit boundary-head and adjacent-moment kernels, not a hidden
abstract increment. Lean now factors the higher-multiplicity adjacent kernel
pointwise into a strictly positive cutoff scale, an almost-everywhere strictly
negative odd centered monomial, one cosine phase, and one complementary
horizontal-tilt bracket. The bracket is identically zero on the critical line;
off the line it has one explicit crossover, with its sign completely fixed by
the oriented distance from that point. The sum coordinate of the finite
product support lies in the proved window `(0, 2*a_(N+2))`. Consequently the
remaining higher-multiplicity cancellation can only come from the cosine and
this single horizontal crossover. Controlling their integral arithmetically,
without importing zero-location information, remains open.
Lean now also places the two completed finite-prefix terms in an exact
two-dimensional hyperbolic coordinate system. After the existing parity is
aligned, partner reflection swaps the two terms through conjugation; the even
coordinate is conjugation-even and `I` times the odd coordinate is likewise
sent to its componentwise conjugate. The signed finite eta energy is exactly
the Hermitian quadratic form of this feature against one fixed `2 x 2`
signature matrix. The corresponding complex-symmetric conjugate-pair block is
proved to be a positive rank-one real block minus a positive rank-one
imaginary block. Lean separately proves that the ordinary Hermitian Gram pair
has a plus sign and is positive semidefinite, preventing those two
constructions from being conflated. This is the eta-specific seam for the
finite-window rank/inertia strategy suggested by the zeta23 architecture.
The next legitimate step is to aggregate these features over finite cutoff and
zero windows and derive trace/Frobenius information from the literal eta
arithmetic; abstract rank bounds alone do not control the open current.
Lean now performs that first aggregation without introducing abstract zero
data. Any finite cutoff family is packed into one feature on `d × Fin 2`, every
cutoff slice retains the exact signed eta energy, and the packed feature obeys
the literal conjugate-partner law. Over the project's genuine symmetric
finite spectral zero windows, with analytic multiplicity, the resulting
complex-symmetric matrix splits exactly as
`onLine + (offReal - offImag)`. The three named blocks are proved positive
semidefinite where appropriate, and the complete matrix is Hermitian. The
rank layer is now also internal: each literal outer-product summand has rank
at most one, giving separate bounds for the full, on-line, off-line real, and
off-line imaginary blocks by their genuine zero-window cardinalities.
Reflection proves the exact count `#full = #critical + 2 * #upper` on every
nonnegative symmetric window. Lean now closes the corresponding inertia
layer as well. A directly checked positive-spectral-subspace argument proves
`n₊(P-N) ≤ rank(P)` for positive semidefinite `P,N`. Hence the actual
off-line hyperbolic block has positive index at most `#upper`, and the complete
eta window satisfies `n₊(full) ≤ #critical + #upper`. The next sharply
separated layer now has exact scalar identities as well. The on-line real
trace is the multiplicity-weighted squared norm of the packed eta features;
the off-line trace is the explicit real-coordinate mass minus
imaginary-coordinate mass. The complete squared Frobenius mass is an
entrywise sum of squared norms of coherent multiplicity-weighted zero sums.
All are finite and literal. Lean now also adapts the attributed Apache-2.0
rank--trace theorem from Anthropic's zeta23 development and applies it to the
actual decomposition with the on-line block as `P` and the off-line
difference as `Q`. For every `c > 0`, the resulting checked inequality is
`c*M_on - (c^2/4)*#critical + 2*c*M_off - c^2*#upper ≤ F`, where `F` is the
literal coherent Frobenius mass. At `c=2` this becomes
`2*M_on + 4*M_off - 4*#upper - F ≤ #critical`. Thus the finite zero-side
linear-algebra closure is instantiated, not merely abstract. The remaining
obligation is to obtain estimates for this ledger from the eta arithmetic
without replacing the coherent sums by phase-free termwise bounds. The
rank--trace theorem itself is still infrastructure, not the missing
arithmetic estimate. Lean now also specializes the multiplicity-aware
rank--trace refinement. Critical-line reflection makes the on-line
complex-symmetric block exactly the required positive Gram matrix. For
`x_rho = m_rho*||v_rho||^2` and
`k_c(x)=c^2-max(c-x,0)^2`, the checked literal ledger is
`2*c*(M_on+M_off)-F ≤ sum_(rho critical) k_c(x_rho)+c^2*#upper`.
At `c=2` this retains one nonlinear term for every actual critical zero,
including its analytic multiplicity and packed eta feature norm. No bound on
that sum or on `F` is inferred. This exhausts the imported finite-dimensional
rank--trace layer. Lean now expands the literal coherent Frobenius mass exactly
as the double genuine-zero sum
`sum_(rho,sigma) m_rho*m_sigma*Re(<v_sigma,v_rho>^2)`. This is a signed
phase-preserving pair correlation, not a sum of absolute squares. It exposes
the diagonal and cross-zero interference on which an eta-arithmetic estimate
must act, but supplies no such estimate. Further progress must prove
cancellation or coercivity for this named finite pair correlation without
discarding its complex phase, or connect it to an independently controlled
arithmetic form. Lean now separates that sum exactly as `F=D+O`, where
`D=sum_rho m_rho^2*||v_rho||^4` is nonnegative and `O` is the same signed
phase-bearing correlation restricted to distinct ordered pairs. Frobenius
positivity gives the sharp formal floor `O >= -D`. The multiplicity-aware
`c=2` ledger is now written directly with `-D-O`, so `O` is the only
cross-zero term left in the finite inequality. The required aggregate bound
on this ledger remains open; the algebraic floor alone gives no zero-location
constraint. Lean now opens each packed-feature correlation into the two
literal completed finite-prefix channels `P` and `Q`. The even/odd
hyperbolic construction proves exactly
`<v_sigma,v_rho>=2*sum_j(conj(P_sigma,j)P_rho,j+
conj(Q_sigma,j)Q_rho,j)`; every mixed `P`--`Q` term cancels algebraically.
Consequently both `D` and `O`, and the full multiplicity ledger, are expressed
in same-channel completed eta-prefix variables. This is the first
eta-arithmetic refinement of the zero-pair ledger, but it remains an identity:
no signed distinct-zero estimate is inferred. The two surviving channels are
now further compressed to one original completed finite-prefix channel
`A_rho,j`. Its ordinary Gram kernel
`H_sigma,rho=sum_j conj(A_sigma,j)A_rho,j` satisfies Hermitian swap symmetry.
Lean proves the partner channel is `A_(rho#),j`, the aligned channel is
`conj(A_rho,j)`, and hence the packed correlation is exactly
`2*(H_(sigma#),(rho#)+conj(H_sigma,rho))`. The diagonal, off-diagonal,
coherent mass, and multiplicity ledger are all rewritten through this one
kernel and its reflected copy. Controlling the signed squares of that
reflection coupling remains open. Lean now factors the original channel as
`A_rho,j=W_rho*M_rho,j`, where `W_rho=C(rho)*rho` is the fixed completed
spectral weight and `M_rho,j` is the literal order-`m_rho-1` cutoff-centered
finite eta moment. Its Gram kernel is therefore
`H_sigma,rho=conj(W_sigma)W_rho*B_sigma,rho`, with the purely finite
arithmetic kernel `B_sigma,rho=sum_j conj(M_sigma,j)M_rho,j`. The complete
feature correlation, diagonal, off-diagonal mass, and ledger are rewritten
with the `W` factors explicit. The live estimate is now concentrated in the
reflection coupling of the finite arithmetic kernels `B`. Every centered
moment is now also expanded exactly into its retained logarithmic interval
integrals, making `B` a literal finite cutoff/interval triple sum. The same
expansion is propagated through both masses and the terminal ledger; the open
problem is a signed estimate for this explicit interval correlation, not an
additional algebraic unpacking step. Lean now also evaluates each interval by
an explicit finite integration-by-parts polynomial: every atom is an
odd-endpoint complex power minus an even-endpoint complex power with literal
logarithmic coefficients. The terminal ledger therefore has a fully finite
arithmetic endpoint form. The next live experiment is an aggregate
separated-frequency estimate on that form, while retaining the signed
zero-pair phase. Lean now proves the full generalized Montgomery--Vaughan
weighted Hilbert inequality internally: `mvDiag_thirteen` gives the diagonal
constant `13`, and `mvHilbert_twentySix` gives the bilinear constant `26`.
Lean further proves that the first `K` literal eta frequencies `log(k+1)` are
injective with admissible uniform gap `1/K`, and specializes the bilinear
theorem as `pairedEtaFiniteLog_mvHilbert_twentySix`. This closes the elementary
frequency-spacing side but is not yet an estimate for the eta ledger. The next
matrix-hybrid layer is now concrete as well. Advancing every member of an
arbitrary packed cutoff family by one gives an exact matrix work identity for
the genuine multiplicity-weighted zero-window block: the block difference is
the arithmetic feature-increment outer product plus both successor cross
terms, entry by entry. Lean identifies that feature increment with the existing
head-plus-prefix arithmetic increment and proves its leading/remainder split
in both hyperbolic coordinates. Lean now transports this split through the
full matrix current. For each genuine zero, both the leading current and the
collection of all terms containing a remainder factor as a sum of two literal
outer products, hence have rank at most two even after analytic multiplicity.
Their complete window sums have rank at most twice the number of represented
zeros, and their sum is exactly the original matrix work. The outer products
remain the project's complex-symmetric transpose products; no complex-linear
Hermitian compression is inferred. Lean now adds a continuous Gaussian
proper-time layer without making that identification. The kernel matrix
`exp(-u*(lambda_i-lambda_j)^2)` is proved positive semidefinite for `u>0`, and
its quadratic form is exactly the previously checked finite Gaussian
arithmetic double sum after the proved positive rescaling. Schur compression
therefore preserves every positive eta constituent. At the literal packed
cutoff nodes `log(2*N+1)`, Lean proves the explicit entrywise heat derivative,
commutation with the genuine multiplicity-weighted zero sum, preservation of
the on-line plus off-line-real minus off-line-imaginary decomposition and
Hermitian symmetry, and commutation with the complete leading/remainder matrix
work law. These are finite identities; no infinite operator or cancellation
estimate is inferred at that stage. Lean now closes the finite kernel-transform
bridge in two exactly equivalent parameterizations. For every nonzero gap
`Delta`, both the oriented square-root heat integral and the direct odd
proper-time integral `integral Delta*exp(-u*Delta^2) du` are proved exactly
equal to `Delta⁻¹`; coincident-frequency entries are explicitly zeroed before
integration, so the nonintegrable diagonal is not silently totalized. The
direct kernel reverses sign under index swap. Applied to any complex-symmetric
matrix it therefore yields a checked skew-symmetric transform, retaining the
ordered channel colour. The Gaussian kernels and compressions obey their
exact additive semigroup laws. The first `K` centered eta cutoff nodes
`log(2*N+1)` are injective and uniformly separated by `1/(2*K)`, and the
checked Montgomery--Vaughan constant-26 bound is proved directly for both heat
representations. Lean now applies that inequality blockwise to the two literal
transpose outer products in each genuine zero's leading current, including
analytic multiplicity. The complete finite-window block is the exact complex
signed zero sum before the triangle inequality, with an explicit sum of
constant-26 envelopes. The aggregate transform is skew-symmetric: both
same-colour block sums vanish and the two mixed-colour blocks are negatives.
Lean now opens the surviving `0,1` block back into the literal completed eta
colours. If `p,q` are the partner and aligned leading increments and `P,Q`
their successor features, every zero contributes exactly
`2*I*m_rho*(H(q,p)+H(q,P)+H(Q,p))`, where `H` is the direct odd-heat transpose
form. All partner--partner and aligned--aligned terms cancel algebraically.
The same reduction is now proved before time integration. At every proper
time, the complete window is the exact complex signed sum of the corresponding
three-colour forms; the full matrix trajectory is pointwise skew, and the
same-colour blocks vanish pointwise. Lean then proves that the reciprocal-gap
Hilbert block is the positive-time integral of this richer scale-resolved zero
sum. Thus the Gaussian--Hilbert bridge and rank-two coefficient interface are
closed without discarding orientation, phase, channel, or heat-scale data.
The abstract finite Hermitian spectral layer now has its own continuous
signed heat carrier. Lean proves the `u^(-1/2)`-weighted signed current
integrable, its normalized integral exactly equal to `n_+ - n_-`, and the
ordinary heat trace convergent to the zero index. Positive inertia is therefore
reconstructed exactly from the continuous observables. This is not yet an eta
or zeta theorem. The finite projection layer now names the ordered cross-scale
leakage before any inequality, factors it as a transition Gram, and proves
that adjunction reverses scale order. A second projection retains two distinct
loss channels: compressed first-projection leakage and finite-compression
leakage. Their exact two-stage matrix and trace ledgers, same-scale positivity,
and transition Frobenius identities are checked. The next hybrid interface
now feeds the literal multiplicity-weighted eta zero-window matrix into the
complete spectral heat and signed spectral heat flows. Lean proves the exact
signature integral, nullity limit, positive-inertia reconstruction, and the
continuous form of the existing `#critical + #upper` eta inertia bound. This
does not yet improve the zero proportion. The next slice must wrap the checked
cross-scale carrier around this literal eta heat flow. That finite coordinate
instantiation is now checked: every decidable packed cutoff/colour selection
is a Hermitian idempotent projection, the ordered leakage is opened into the
literal sum over omitted coordinates, and the same matrix remains an exact
transition Gram with scale-reversing adjoint, same-scale positivity, Frobenius
trace identity, zero criterion, and mass-balance ledger. This is not the
infinite eta-support projection. The next work must evaluate the retained
spectral-heat path entries arithmetically and measure their effect on the
multi-scale certificate ceiling before any further collapse.
The literal eta window now also carries every matrix-valued spectral heat
moment `A^k exp(-uA^2)`. Lean proves the exact order/scale product law,
even-order positivity, the derivative hierarchy `dH_k/du=-H_(k+2)`, and a
positive-semidefinite Gram matrix for arbitrary finite families of orders and
scales. Each Gram entry is simultaneously a combined higher moment and the
trace product of the two separate flows. Their zero-scale boundary is now
connected exactly to the existing eta arithmetic ledger: `H₀(0)` is the
packed coordinate dimension, `H₁(0)` is the on-line plus signed off-line
trace mass, and `H₂(0)` is the fully evaluated endpoint diagonal plus signed
off-diagonal correlation. The last quantity is also the negative initial
derivative of the ordinary eta heat trace. Positive heat times, genuinely
mixed scales, and the transition paths remain unevaluated. The next gate is
to evaluate or sharply bound those retained quantities, then solve the
resulting certificate extremal problem without assuming the desired
zero-location conclusion.
The abstract degree-four ceiling experiment is now exact. For any finite
nonnegative weighted spectral model with moments `(1, 1, 4/3, 2, 13/4)`, Lean
uses the explicit Christoffel witness `1-(7/4)x+(2/3)x²` to prove zero mass at
most `5/36` and certificate at least `13/18`. A checked nonnegative three-atom
model attains equality, so those five moments alone have a sharp ceiling below
one. They are also exposed as the zero-scale jet of a continuous weighted heat
hierarchy. This is not an eta instantiation. Future work must derive the extra
moments or positive-scale heat data from literal eta arithmetic and show that
they exclude the sharp model before claiming a stronger zeta-zero proportion.
The quadratic witness is now also transported through heat time as the exact
linear combination of orders zero through four at one common scale. Its
certificate is monotone from `13/18` and converges to the exact model
certificate. The sharp three-atom model nevertheless remains exactly at
`13/18` for every nonnegative scale because both nonzero atoms are roots of
the witness. Therefore reweighting the same collapsed channel by heat is not
new information. The next observable must be eta-backed and nonvanishing on
at least one sharp root channel; a separate heat trace, signed current, or
genuine cross-scale correlation is admissible, but its arithmetic value must
be proved rather than postulated.
The independent ordinary heat channel now has an exact separator theorem.
The first-moment normalization forces `H₀(u)` strictly above zero mass at
every finite scale, while `H₀(u)` converges to zero mass at infinity. Hence
the certificate is strictly above `13/18` exactly when some nonnegative scale
has `H₀(u)<5/36`. The sharp three-atom model stays strictly above this
threshold at every finite scale. The next arithmetic gate is therefore not
another abstract reweighting: it is construction of the correct normalized
eta model plus a proved ordinary-heat crossing, or another independent
observable with a comparably explicit separator criterion.
The literal eta positive-time hierarchy now retains its complete matrix-power
carrier. Lean proves a genuine convergent `HasSum` expansion
`H_k(u) = sum_m (-u)^m/m! * rtrace(A^(k+2m))` for every Hermitian matrix and
instantiates it on the multiplicity-weighted eta zero-window block. In
particular, the independent ordinary eta heat trace is the exact series of all
even coherent matrix-power traces. This removes any hidden positive-time
spectral collapse, but only powers zero through two currently have explicit
eta arithmetic evaluations. The next information-preserving step is to open
the higher powers as literal closed eta paths and obtain a normalized crossing
or obstruction from those signed correlations.
That path expansion is now checked. For every finite matrix Lean recursively
retains every ordered intermediate coordinate and proves the closed-path sum
equal to the corresponding power trace. Each eta edge is then opened as the
literal complex multiplicity-weighted zero-window sum of completed finite eta
features. The ordinary eta heat trace is a genuine convergent series of all
even closed path correlations, with cutoff, colour, phase, multiplicity, and
path order intact. Its length-two coefficient is proved exactly equal to the
existing endpoint diagonal plus signed off-diagonal arithmetic mass. Higher
path estimates remain open; applying absolute values edgewise would discard
the new information and is not an acceptable substitute.
The first higher projection path is now explicit as well. The product of three
coordinate-compressed eta heat flows is the longer-time compressed flow minus
three separately named channels: first-gap, second-gap, and two-gap. Lean
opens each entry as its ordered retained/omitted double path sum. At equal
scale the two one-gap paths are adjoints with equal real trace, while the
two-gap path factors through the complementary compressed heat as a positive
weighted transition Gram and is positive semidefinite. The live estimate must
use cancellation in the paired one-gap trace together with the nonnegative
two-gap reserve; bounding both one-gap paths separately by norms would undo
the purpose of this slice.
The phase-separation route now has its first checked rigidity theorem. For any
finite set of distinct unit-modulus complex modes, Lean proves that a linear
combination of their geometric sequences can converge to zero only when every
coefficient vanishes; equivalently, those full sequences are linearly
independent. The proof uses repeated shift differences and preserves the
complex phase. Lean now connects this abstraction to literal eta arithmetic:
for every odd base `q > 1`, the cutoff `(q^n-1)/2` tends to infinity, its odd
endpoint is exactly `q^n`, and the sharp complex eta-tail normalization becomes
the `n`th power of one fixed mode. At every nontrivial zero the literal
multiplicity-minus-one centered prefix inherits an explicit nonzero complex
geometric asymptotic. Lean now proves that any two distinct frequencies can
collide at at most one prime base. Thus every finite injective frequency family
admits an odd prime base at which all normalized modes are distinct, with a
specialization to every finite same-real-part zeta-zero layer. The raw inverse
decay mode now restores the real coordinate as its exact norm. Lean proves that
one odd prime separates these raw modes across an arbitrary finite zeta-zero
window, and that their first window-cardinality coordinates form a
nonsingular Vandermonde matrix. Lean now transfers that finite limiting block
through the sharp complex asymptotics. For every finite zeta-zero window, one
odd prime base makes all sufficiently late square matrices of literal
multiplicity-aware centered eta prefixes nonsingular. This establishes a 100%
raw finite information-separation carrier. Lean now transports that carrier
into the actual completed two-channel hyperbolic features: the original
channel is a nonzero completion-row scaling of the literal prefix matrix, the
aligned channel is its entrywise conjugate, and one fixed complex-linear
projection recovers the aligned channel from every packed even/odd feature.
Consequently, for every finite zeta-zero window, one odd prime makes all
sufficiently late packed certificate features linearly independent. Lean now
retains analytic multiplicity by scaling every zero column with its positive
square-root multiplicity and forms the corresponding coordinate matrix times
its conjugate transpose. This matrix is exactly the sum of the literal
multiplicity-weighted Hermitian outer products `v v*`, is positive
semidefinite, and eventually has rank equal to the number of represented
distinct zeros. It remains rigorously distinct from the complex-symmetric
`v vᵀ` block used by the signed inertia certificate. Lean now couples the
two without identifying them. On every nonnegative symmetric spectral window,
the Hermitian Gram is exactly `onLine + offReal + offImag`, whereas the signed
block is `onLine + offReal - offImag`. Hence their difference is exactly twice
the positive imaginary off-line block and their sum is twice the positive
on-line-plus-real block; both are positive semidefinite. At the same eventual
geometric blocks, the Hermitian Gram retains full represented rank. Pulling the
same multiplicity-weighted synthesis matrix `C` back to zero-index space now
gives the square metric `K = Cᴴ C`. Actual packed-feature linear independence
makes `C` injective, so Lean proves that `K` and `K⁻¹` are both positive
definite for one odd prime and every sufficiently late block. Lean now pulls
the signed coordinate block back as `B = Cᴴ Signed C`. Congruence gives
`K² - B` and `K² + B` positive semidefinite, and normalization by `K⁻¹`
produces a Hermitian matrix `A = K⁻¹ B K⁻¹` with both `I - A` and `I + A`
positive semidefinite. One odd prime makes this contraction conclusion hold
at every sufficiently late block of each nonnegative finite spectral window.
Lean now determines this normalization exactly. Critical-line reflection
induces a permutation matrix `P` on the enumerated window, the actual synthesis
obeys `P Cᴴ = Cᵀ`, and the signed coordinate block is `C Cᵀ`. Therefore
`B = K P K` and complete two-sided whitening gives `A = P`. In particular,
`A² = I` and its trace is the number of fixed reflection indices. This proves
that full whitening cancels all eta amplitudes and cannot be the arithmetic
observable by itself. The next obligation is to retain the coupled pair
`(K,P)` through mixed traces, one-sided normalization, or an equivalent
information-preserving construction. Lean now checks the first scalar layer:
`m₀ = Re tr(K)` is exactly the positive Hermitian eta trace and
`m₁ = Re tr(PK)` is exactly the signed eta trace. Their difference is twice
the imaginary off-line mass and their sum is twice the on-line-plus-real mass,
so `-m₀ ≤ m₁ ≤ m₀`; on nonempty separated windows `m₁/m₀ ∈ [-1,1]`.
Lean now retains the higher powers and first cross-scale version as well. For
geometric blocks `n,m`, the carrier `Mₙₘ = P(Cₙᴴ Cₘ)` is exactly `Cₙᵀ Cₘ`,
has `Mₙₘᵀ = Mₘₙ`, and exposes literal multiplicity-weighted eta correlations
entrywise. At equal scales every `Re tr((PK)^r)` is the real part of a complete
ordered closed zero-index path sum; order zero is the distinct-zero count and
order one is `m₁`. The two-step cross-scale word is a checked symmetric
double-edge sum. The next obligation is to prove the positive normalization
needed to place these moments inside the finite certificate model. Lean now
constructs the exact packed-coordinate support for that step. The literal
Hermitian carrier is `S=CPCᴴ`, while `Q=CK⁻¹Cᴴ` is positive semidefinite,
Hermitian, and idempotent whenever `K` is positive definite. Lean proves
`QS=SQ=S`, `tr(Q)` equals the represented distinct-zero count, and
`Re tr(QS^r)=Re tr((PK)^r)` for every order including zero. Thus the packed
realization no longer pads the mixed moment model with a spurious zero
eigenspace, and it still retains the amplitudes in `K`. Lean now flattens every
finite family of supported powers `QS^k`; their column Gram is positive
semidefinite and its entries are exactly the mixed moments at summed orders.
It then normalizes by the distinct-zero count `N` and mean positive eta mass
`m₀/N`. The resulting dimensionless moments
`ν_r=N⁻¹(N/m₀)^r Re tr((PK)^r)` form a positive-semidefinite Hankel matrix for
every finite order family, with `ν₀=1`, `ν₁=m₁/m₀`, and
`ν_(a+b)^2≤ν_(2a)ν_(2b)`. Lean now also proves why this mixed spectrum cannot
by itself supply the certificate's distinguished zero atom: positive `K` makes
`PK` invertible. The semantically correct count channel is instead the pair of
reflection projections `E₊=(I+P)/2` and `E₋=(I-P)/2`. They are orthogonal
positive-semidefinite idempotents; `tr(E₋)` is exactly the upper off-line-pair
count, and `1-2 tr(E₋)/N` is exactly the critical-zero proportion. Compressing
the actual eta metric gives positive carriers `E₊KE₊` and `E₋KE₋`. Under the
already checked positive-definiteness hypothesis, `ker(E₊KE₊)` is exactly the
reflection-odd subspace, its nullity is the upper off-line count, and the two
compressed traces are exactly the on-line-plus-real and off-line-imaginary eta
masses. Lean now extracts the literal uniform eigenvalue-atom model of
`E₊KE₊`: its nonnegative nodes are the eigenvalues divided by their positive
mean, its ordinary and heat moments are exact normalized matrix traces, and
its zero mass is exactly the upper off-line-pair fraction. Its certificate is
therefore the literal critical-zero fraction. Lean also proves that this
fraction is strictly greater than `13/18` exactly when the normalized ordinary
heat trace of `E₊KE₊` crosses below `5/36` at some nonnegative scale. The next
bridge now writes `W=C E₊`, proves `WᴴW=E₊KE₊`, and transports its nonzero
spectrum to `WWᴴ=C E₊ Cᴴ`. The latter is exactly the positive on-line plus
off-line-real eta block. All positive moments transfer without loss, while
ordinary heat has one exact ambient-cardinality padding correction. Lean also
expands that coordinate heat into a convergent series of ordered even paths
whose intermediate packed coordinates and on-line/off-line-real edge colours
remain explicit. Lean now proves that the coordinate carrier has rank exactly
`#critical + #upper-off-line` and derives
`rtrace(A)^2 ≤ rank(A) * frobSq(A)` from finite Cauchy--Schwarz on its nonzero
eigenvalues. Its first two moments are exactly the real length-one and
length-two coloured path sums. Therefore
`31*N*Re(path₂) < 36*Re(path₁)^2` is a checked sufficient premise for a
critical-zero proportion above `13/18`, while
`N*Re(path₂) ≤ Re(path₁)^2` is a checked sufficient premise for the
finite-window `18/18` conclusion. These implications do not prove either
premise. The existing geometric feature-separation theorem discharges the
positive-definiteness condition for one odd prime base at every sufficiently
late block. Lean now opens those two paths one step further as a literal
reflection-even eta frame, indexed by critical zeros and upper off-line pairs.
Its length-one mass is the weighted sum of squared atom norms; its length-two
frame potential is the complete weighted double sum of squared real eta
correlations. Every pair term is checked nonnegative, with both atom colours
retained through the proof. Lean now splits that potential into diagonal
self-mass and distinct-pair correlation and defines the complementary
decorrelation reserve as the weighted sum of
`norm_a²*norm_b²-correlation(a,b)²` over ordered distinct coloured atoms.
Complex Euclidean Cauchy--Schwarz proves every reserve summand nonnegative,
and Lean proves the exact conservation law `mass²=potential+reserve`. The
`13/18` premise is therefore exactly
`(31*N-36)*potential < 36*reserve`; the finite-window `18/18` premise is
exactly `(N-1)*potential ≤ reserve`. Lean now builds the corresponding
square-root-weighted frame synthesis, identifies its Gram with the coordinate
carrier, and uses the checked carrier rank to prove all literal frame atoms
linearly independent at every separated block. Hence every distinct pair has
strictly positive Gram-determinant reserve. The total reserve is positive
exactly when the frame has at least two atoms, and one odd prime base makes
this characterization hold at every sufficiently late block. Lean now also
retains the exact complex correlation of length-`M` unit geometric mode blocks
and proves `|corr|²|conj(w)z-1|²≤4`. Every finite injective unit-mode family
has a checked positive minimum phase gap, giving a uniform `O(M⁻²)` bound
for all distinct-pair squared coherences; one collision-free odd prime
instantiates this on any same-real-part zeta-zero layer and on the critical
window. Lean now performs the first arithmetic transport: explicitly
normalized literal eta-prefix vectors converge to the unit-mode vectors, and
their complex correlations, squared norms, and squared coherences converge as
well. Hence one prime and one positive gap give the eventual simultaneous
bound `literalCoherenceSq*gap² < 4/M²+ε` for every distinct pair in a finite
same-real-part layer, including the critical window. Lean now proves that the
two hyperbolic coordinates are an injective realification of this complex
channel, with an exact inverse, correlation law, and norm law. The literal
critical-line packed cutoff feature is exactly the realification of the
completed original eta channel. Consequently the phase-normalized packed
same-layer coherence is bounded by the full complex coherence and inherits
the eventual simultaneous `4/M²+ε` estimate. Lean now removes the same-layer
restriction from the convergence interface: under one common tilt `σ`, every
literal block converges to a geometric mode of exact radius
`q^(σ-Re(rho))`, and correlations, norms, absolute coherence, and packed real
coherence converge without erasing that radius. At `σ=1/2`, critical modes
have radius one, while an upper off-line representative and its reflected
partner retain one shared unit phase and strictly reciprocal radii. The actual
upper off-line frame atom is exactly half the injective realification of the
sum of those two completed channels, and its coordinates reconstruct that sum.
Lean now identifies the two underlying literal critical-shifted modes with the
abstract reciprocal-radius pair. Their cross-correlation is exactly the window
length; their full two-coefficient norm square retains the signed interference
term; no nontrivial coefficient pair cancels; and every off-line pair has
strictly positive Gram reserve at each length greater than one. Lean now turns
that reserve into an explicit quantitative lower bound: every complex
combination is bounded below by `(A*B-M^2)/(A+B)` times the squared coefficient
norm, and this determinant-over-trace constant is proved positive for the
literal shifted zero/reflection modes. The actual cutoff-dependent completion
coefficients must also reach this inequality. Lean now completes the exact
algebraic part of that transport: after common
coordinate tilt, each completed channel is its normalized literal prefix times
one explicit nonzero coefficient containing the completion weight, sharp
prefix limit, and inverse cutoff row scale. After lossless coordinate recovery,
the actual upper frame atom is exactly the sum of the two normalized reflected
prefix columns with both coefficients retained. Lean now closes the uniform
perturbative step: a generic signed two-vector Gram ledger gives the
determinant-over-trace bound, the literal finite-prefix coefficient converges
to the positive reciprocal-mode constant, and one eventual half-limit estimate
holds simultaneously for all complex coefficient pairs. Substitution of the
actual moving completion coefficients yields an explicit positive lower bound
and strict noncollapse for every sufficiently late recovered upper frame
channel. Lean now also discharges the conditioning gap between that recovered
channel and the certificate metric. Pointwise multiplication by the common
critical coordinate tilt is bounded by its explicit finite weight energy,
that energy is strictly positive, and the half-scaled two-coordinate
realification of an actual upper atom is proved to have exactly the norm square
of its unweighted recovered complex reflection sum. Dividing by the tilt
energy therefore transfers the coercive lower bound and strict noncollapse to
the literal packed upper frame atom itself. Lean now opens the next
cross-atom interface without discarding complex phase. The packed correlation
of two literal upper atoms is exactly the real part of their recovered complex
reflection-sum correlation, and that complex carrier is expanded into the
four completed original-channel eta Gram kernels at the two zeros and their
reflections. For arbitrary finite complex vectors, the real-correlation
reserve is proved exactly equal to the full Hermitian Gram reserve plus the
square of the imaginary correlation. Thus every actual
multiplicity-weighted upper--upper reserve summand has a checked two-part
nonnegative ledger with all four arithmetic channels retained. Lean now also
preserves the nonunitary critical tilt at correlation level. Its inverse
squared-modulus diagonal recovery metric makes the correlation of tilted
vectors exactly equal to the original Hermitian correlation. The two
reflected/original prefix colours of each upper atom therefore form a literal
`2 × 2` metric correlation matrix, contracted against the exact moving
completion-coefficient vectors. That contraction is the unweighted
upper--upper correlation, every matrix entry converges to the corresponding
explicit shifted-mode metric correlation, and the full weighted certificate
summand is exactly the contraction Gram reserve plus its imaginary square
times the positive multiplicity weight. Lean now evaluates the limiting
metric matrix itself. The inverse squared-modulus metric cancels the common
critical tilt entrywise, leaving four explicit finite geometric sums of the
raw eta decay modes. Every relevant relative mode lies strictly inside the
unit disk, and Lean proves the phase-and-radius estimate
`norm(entry)*norm(relativeMode-1)≤2`. With arbitrary positive slack this bound
holds eventually and simultaneously over the complete finite upper window
and all four colour entries of the literal prefix matrix. Lean now contracts
these estimates against the exact moving completion coefficients. The norm of
the actual unweighted complex upper--upper reflection-sum correlation is
eventually bounded, simultaneously over the entire finite upper window, by
the four-term sum of coefficient-norm products times `(2+epsilon)/gap`; every
gap is proved strictly positive. The literal packed real correlation inherits
the same envelope. Lean now names the transported atom-coercivity lower bound
and proves it strictly positive. Combining the two atom bounds with the square
of the correlation envelope gives an unconditional eventual lower bound for
every actual multiplicity-weighted upper--upper reserve:
`weight_rho*weight_zeta*(lower_rho*lower_zeta-envelope^2)`. The conclusion is
simultaneous over the complete upper window and is summed without loss over
all ordered distinct upper pairs. The difference need not yet be positive.
Lean now proves the exact complete colour decomposition: critical--critical,
critical--upper, upper--critical, and upper--upper. Every sector is
nonnegative, the diagonal terms vanish exactly, and the upper sector is the
ordered-distinct aggregate above. Thus the explicit upper lower bound reaches
the complete certificate reserve, and combining it with global reserve
nonnegativity gives the eventual certified floor `max 0 upperLower`. Lean now
substitutes that floor into both certificate theorems. One checked odd-prime
choice simultaneously makes the literal eta Gram positive definite, so at all
sufficiently late blocks the strict floor inequality implies `>13/18` and the
endpoint floor inequality implies `18/18`. Those two inequalities remain open
antecedents. Lean has now audited the longer-block behavior and proved that the
current pointwise coercivity-minus-triangle floor eventually vanishes
uniformly in the block start. It therefore moves upstream: the exact signed
four-colour contraction retains all sixteen ordered interactions, and its
complete window aggregate is the literal upper--upper reserve. The natural
original-colour normalization is proved to collapse to one colour, so Lean
now supplies an exact polar--hyperbolic alternative. Each completion pair is
factored into a common positive geometric mean, two reciprocal positive radial
colours, and two unit phases; every raw contraction is reconstructed exactly.
Each literal signed pair reserve is a strictly positive scale times a
nonnegative balanced reserve, and the complete signed window is exactly the
corresponding scale-weighted balanced aggregate. The existing eventual
odd-prime `>13/18` and `18/18` interfaces transport unchanged. Reflection now
also exposes one universal cutoff scale: the two coefficient norms in every
completion pair have product equal to a fixed leading product times
`q^(-n)`, so every ordered-pair reserve contains the same `q^(-2n)` factor.
Lean removes it from the complete reserve and multiplies the frame potential
by the matching positive factor, proving both certificate targets equivalent
to their coefficient-normalized forms. The reflected radial colour still has
square equal to the exact coefficient-ratio norm and tends to zero, so the
true reciprocal hyperbolic imbalance remains visible. The live obligation is
an eta-arithmetic bound on this scale-free carrier strong enough to prove one
of the threshold antecedents; neither is yet proved.
Lean now prevents that shrinking colour from being erased by a one-scale
contraction. The two reflected completion coefficients advance by distinct
complex step modes for every `q > 1`, so their adjacent-start `2 × 2` matrix
is nonsingular. Two coefficient probes recover an arbitrary colour vector,
and four left/right probes recover the entire literal normalized-prefix colour
metric exactly. The `(0,0)` probe is the existing eta contraction; the other
three vary the adjacent coefficient rows against that same fixed-start metric,
not a silently frozen prefix at `n + 1`. No conditioning or arithmetic bound
follows from inversion alone. The live obligation is a quantitative estimate
on this scale-free multi-start carrier that yields `13/18`, then `18/18`.
Lean now removes the cutoff-dependent inverse from that interface. The moving
adjacent-start matrix factors exactly as `D_n*V`, with every completion
coefficient in `D_n` and only the zeroth/first step modes in `V`. Distinct
reflection modes make `V` nonsingular for `q > 1`, independently of `n`.
Inverting the four probes through `V` recovers `D_zeta^* K D_rho`, whose
entries are exactly the literal coefficient-weighted signed-colour terms.
This recovery propagates through all sixteen interactions, the complete
upper reserve, universal scale removal, and both certificate interfaces. It
still supplies no bound on the probes. The live task is a finite-window
conditioning bound and eta-arithmetic estimate for this scale-free carrier.
Lean now also rechecks the complete pinned multiplicity-aware Zeta23 chain.
The exact external `HD(1)` theorem is instantiated for the literal simple
critical-line count over the analytic-multiplicity denominator and bridged to
the project-native simple dyadic window. Beyond that external baseline, the
project now proves two ordered unconditional literal constants
`HD(1) < C₀ < C₁`; the stronger one uses uncapped three-column coercivity and
strictly improves the preceding project certificate. No `13/18` theorem is
claimed.

## Current theorem-push commit gate

On 2026-09-05 the user explicitly changed the objective to an overnight Lean
theorem push using phase colour, Gaussian heat, the literal eta support, and
finite/continuous representations. This supersedes the former requirement
that every commit improve a literal zero-proportion certificate above `17/25`.
On 2026-09-06 the user authorized the next full theorem package: actual
overlap averaging, complex weighted endpoint corrections, signed Gaussian
reflection, mixed matrices, and an exact completed-current audit. The active
mathematical targets and implementation ledger were recorded in
`docs/eta-signed-endpoint-theorem-plan.md`; that package is complete at its
stated scope. The user then authorized the full objective: reconstruct the
original leading current and prove the uniform weighted arithmetic estimate.
The active ledger is `docs/eta-current-reconstruction-plan.md`. The completed
first program remains recorded in `docs/rh-overnight-theorem-plan.md`.

A qualifying slice must prove a concrete target from that program, with all
analytic hypotheses discharged for the actual carrier. Retain exact phase,
tail, and mixed-kernel identities alongside their estimates. Generic models,
unproved premises, numerical experiments, and merely renamed obstructions
do not establish these targets. Document the compiled terminal theorem and
the precise remaining obligation before staging.

Commit and push each coherent passing theorem slice with its necessary
documentation and generated inventory. Auxiliary heat or matrix estimates
must not be reported as proving RH, an RH-equivalent open direction, or an
improved zero-count certificate. The soundness and exact-commit CI gates
below continue to apply.

## Soundness invariant

The repository must remain a continuous, bottom-up Lean proof chain after
every commit.

- Do not use `sorry`, `admit`, introduce custom axioms, use compiler-trusting
  proof shortcuts, or add declarations whose purpose is to assume the missing
  mathematics.
- Do not weaken `RiemannHypothesis`, redefine a frontier quantity to make it
  trivial, hide the frontier in a typeclass or hypothesis, or report a
  conditional reduction as a proof of its premise.
- Lean's standard logical axioms `propext`, `Classical.choice`, and
  `Quot.sound` are permitted. Any other transitive axiom dependency is a
  failed gate unless the user has explicitly approved and documented it.
- Every mathematical progress claim must name a compiled theorem. Comments,
  Markdown, Python output, numerical evidence, and successful examples are
  not proof.
- A zero-proportion threshold counts as achieved only when a compiled theorem
  is stated for the literal zeta counting functions and every arithmetic or
  analytic antecedent is discharged. Generic moment models, toy measures,
  conditional implications, equivalent criteria, and method ceilings are not
  certificates and must not appear as achieved dashboard milestones.
- Decimal labels are descriptive unless Lean proves exact enclosing
  inequalities. State the exact checked constant in theorem claims.
- External research notes are leads, not trusted inputs. A pinned external
  Lean proof may be used only with attribution, license provenance, a strict
  build, and a complete transitive axiom audit; it must be labeled an external
  baseline rather than original project progress.
- Numerical and symbolic computation may explore conjectures, find constants,
  or produce exact certificates. The final theorem must check in Lean without
  trusting Python or floating-point output.
- Preserve genuine definitions and all analytic side conditions, including
  convergence, integrability, zero avoidance, multiplicity, domains, and
  limit hypotheses. Never silently totalize a singular expression and then
  reason as though the original identity held there.

The compiled project must contain no project-defined axioms. The status
generator rejects any such axiom, even when it is disconnected from a
displayed frontier theorem.

## Information-flow invariant

Treat every theorem interface as a transport decision. Before applying a
lossy operation such as a norm, absolute value, trace, determinant, scalar
integration, asymptotic limit, or channel sum, identify which phase, sign,
orientation, multiplicity, scale, correlation, and cutoff data it forgets.

- Fork, do not discard: retain the richer source object and prove the lossy
  summary as a named downstream theorem.
- Keep sign-bearing odd and even channels, completion phases, reflected-zero
  colours, and the full heat-time family available until a proved estimate
  uses their cancellation or ordering leverage.
- Prefer commuting-diagram theorems that connect the rich carrier to each
  compressed view, so later work can move back upstream without rebuilding it.
- Before investing in a compressed statistic, test whether distinct
  on-line/off-line or positive/negative configurations can share that
  statistic. If so, add a companion channel or stronger carrier first.
- Collapse information at the latest theorem where it produces a concrete
  estimate. Never replace an exact signed identity by only its triangle bound.

For the current ordinary-prime tail, the compiled all-filter obstruction in
`docs/zeta-prime-window-obstruction.md` rules out source-scale norm bounds on
every raw interval for any fixed normalized polynomial, including the actual
pole-jet filter. Its windows lie beyond both current arithmetic cutoffs.
Retain cancellation between windows or identify a centered error before
invoking interval estimates. The complementary-tail relative limit uses the
hypothetical zero's source theorem and is not an independent arithmetic bound.

The adaptive Gaussian region in `docs/zeta-gaussian-all-height.md` now has
an explicit starting height and no upper height ceiling. Its arithmetic
transport supplies a radius greater than one at every eligible center,
but its response constant may depend on that center. Do not extend the
older compact-band uniform constant to the unbounded center domain without
a new proof. The exact literature comparisons retain their plateau scope.

The refinement in `docs/zeta-gaussian-multiplicity-depth.md` keeps the
actual multiplicity in the Gaussian source. Its larger layer excludes
multiple zeros and discharges simplicity and the full eta head-current
identity there. It does not exclude simple zeros in that added layer,
enlarge the universal zero-free curve, or give separation throughout that
whole simplicity layer.
The comparison with the older simplicity width requires enlarged
logarithmic height at least 100. Keep these distinctions in status and
explorer descriptions.

The finite-group refinement in `docs/zeta-gaussian-zero-separation.md`
counts at most one zero with multiplicity in each boundary rectangle of
horizontal depth `2*d(t)` and vertical radius `d(t)/2`, at central heights
at least one million. It also isolates zeros within `(3/2)*d(t)` of either
edge from every other zero by distance greater than `d(t)/2`. Keep these
horizontal scopes separate from the larger simplicity-only layer.
The inverse-distance estimate alone controls individual factors. The
subsequent `docs/zeta-zero-filter-cost.md` controls the whole original
pole-jet filter in the right isolation layer: exact Mahler identities remove
the inverse-coordinate denominators, and a global Poisson count pays for
every factor. Its height-dependent weighted coefficient bound also controls
the exact density primitive and the finite-band reduction error. This is
not a bound for arbitrary order-dependent augmented filters or the signed
bulk. A rectangle may contain one simple zero; the same centered source
tends to minus one under that hypothesis. The independent signed prime
floor and an enlarged universal zero-free curve remain open.

The source-level audit in
`docs/signed-prime-carrier-information-audit-2026-09-12.md` records the
current carrier's correlations and exact loss points. Distinguish its
compiled identities from diagnostic mode calculations and proposed
interfaces. Keep the three Gaussian prime responses on their common
prime measure; separate finite block floors may not be added when they
each bound the same full sum. Test any growing-block improvement at the
actual dilation and source scale before treating strict positivity as
a quantitative advance.

`docs/zeta-gaussian-prime-blocks.md` now proves the complete common prime
measure, disjoint triangular-block floors and a ceiling for that whole
minorant class. It includes the stronger weighted recurrence, arbitrary
distinct prime sets and lengths, and moving coefficient families. Their
guaranteed reserve divided by unbounded dilation tends to zero. This is
not an upper bound on actual mixed prime work or a classification of every
possible recurrence. Do not extend the same triangular-minorant route in
the hope of a leading-scale gain; retain cross-prime and signed-boundary
correlations or establish a new arithmetic property instead.

`docs/zeta-gaussian-prime-correlation.md` gives the anchored Schur test on
the complete Gaussian prime measure. Retain both logarithmic ratios and
products: their average is the exact cosine energy, while the excess in
the ratio-only test is a nonnegative sine energy. The actual finite-zero
constraint retains the full squared source surplus and removes the
constant phase from the energy exactly. It is proved, but the independent
energy gap in the arithmetic floor criterion remains a premise. Do not
describe this classical matrix
transport as a proved cancellation estimate, a new region or historical
novelty. Test its complete real pair energy with all product phases and
the signed boundary mean before claiming a gain at the source scale.

`docs/zeta-gaussian-prime-reduction.md` now proves the complete remainder
reduction at the current fixed-strip dilation. Proper prime powers and
both auxiliary responses share one fixed summable majorant; an explicit
Young allowance pays every mixed term in the real energy. At reciprocal
dilation tuning, that allowance divided by the squared dilation tends to
zero for moving families of bounded nonconstant mass. The actual squared
source constraint now targets ordinary Gaussian-prime energy. Preserve
its product and ratio phases, diagonal and signed boundary mean. Do not
claim that decay of the remainder proves the ordinary-prime bound or a
new exclusion; the actual source surplus must still be positive and beat
the complete remaining energy cost.

`docs/zeta-gaussian-prime-energy-bound.md` supplies the first independent
complete-energy bound and the exact complete-prime-prefix source transport.
Its sufficient decay condition `log(abs(t)+26)/q -> 0` was not supplied
by the current dilation. The stronger argument in
`docs/zeta-gaussian-prime-energy-decay.md` now proves actual decay at that
dilation: signed Poisson differences use the already proved log-log gap
to give every positive logarithmic coefficient for the real pole-removed
Euler response, uniformly on `1 <= sigma <= 3`. The full Gaussian
response inherits the small coefficient uniformly in all `q >= 1`.
For moving nonnegative summable families of bounded mass and first
logarithmic frequency cost, normalized ordinary-prime energy tends to
zero when absolute height diverges and `log(abs(t)+26)/q` is bounded.
The current schedule has ratio at most `320000+log(13)`, so it qualifies.
The complete auxiliary cost and actual positive squared source surplus
over the original signed budget have the same normalized zero limit.
Do not continue describing that energy decay as open. The signed
boundary budget and a source-beating inequality remain open; this is
not an RH proof or a larger zero-free region. Keep the `+26` and `+2`
height smoothings distinct, the unevaluated coefficient-dependent
thresholds explicit, and the arbitrary moving finite-zero windows,
multiplicities and clipping depths in the source theorem. The complete
prime-sum bounds do not apply to sign-selected prime subsets or supply
the independent floor for the separate centered prime carrier.

`docs/zeta-gaussian-signed-budget-reduction.md` now isolates the original
signed clipped left mean. The actual right-response multiplier is bounded
by `1/(50000*q^2)`, rather than only the earlier uniform cap. The complete
budget difference has absolute value at most
`109*m+3*(m*log(abs(t)+26)+F)/(50000*q^2)` for `q>=1`, `abs(t)>=10^6`.
It vanishes after division by the current dilation, and the actual
positive squared source surplus over the left mean has a vanishing
normalized limit. Do not keep listing the non-left terms as an unresolved
source-scale cost in this regime. The original left mean, all finite
negative-depth clipping and all coefficient/frequency dependence remain.
No unclipped integral limit, source-beating left-mean bound, new region
or RH proof follows yet. The right response contains the logarithmic
completion; it must not be treated as a bounded Euler prime sum before
its inverse-square multiplier is applied.

`docs/zeta-gaussian-source-support.md` audits the source side before further
normalization. The exact nearby condition is
`(t-gamma)^2 < (beta-line(k))*(2*(1+x)-beta-line(k))` for positive shift.
The order-nine source is identically zero for `beta<=2035/2046`, at every
dilation and frequency. All currently admissible orders `k>=2` leave
`beta<=5/7` outside this source. Those are visibility cutoffs, not zero-free
boundaries. The original complex contribution is retained in the far term;
its norm estimate is the later information loss. Every fixed finite zero
window also has exactly zero source once diverging detector height leaves
its bounded ordinate range, even with arbitrary scalar reweighting. Do not
present the source-surplus limit for such a window as a contradiction: it
then controls only the negative part of the left mean. Before another decay
push, exhibit a nonzero source for the fixed hypothetical zero at the chosen
scale, or state precisely the new region being targeted. The centered
prime carrier retains such a source; its independent cofinal floor is open.
The same source-support module now supplies a constructive alternative in
the existing general strip identity. For a hypothetical zero with
`h=beta-1/2>0`, choose `sigma=1+h/4` and `eta=1/2-h/4`; the right edge is
exactly `3/2`, the left edge is `1/2+h/2`, and the zero lies strictly inside
the source ball at its own ordinate. The aligned compensated source is
strictly positive for every `B>0`. The original full signed strip inequality
is instantiated with all geometric premises discharged and every finite
`M>=0` retained. This repairs coverage, not the independent arithmetic
estimate. Do not claim the fixed-order-nine height-decay theorems apply to
this adaptive geometry without a new proof. A larger growth domain is not
needed for this construction.

The general envelope audit in `docs/zeta-prime-envelope-rate.md` also rules
out direct absolute integration of subexponential full-density errors for
every fixed normalized filter, even with the entire complex derivative
kept together. Do not report such an allowance as tending to zero at the
selected source scale. This does not bound the actual signed error or rule
out order-dependent filters with separately proved source/error control.

`docs/zeta-prime-discrepancy-work.md` now supplies exact integer Chebyshev
drift/jump and complex-weighted square identities, with all preceding prime
pairs, block boundaries and test increments. For the full factorial kernel
divided by its positive integer coordinate, the complete local forcing
diagonal is bounded by `C(p)*(4/5)^N`, uniformly over all finite index sets
and heights. Thus normalized `2*work+flux` tends to zero for every fixed
filter and `0<=u<=1`, even on moving blocks. This is a quadratic correlation
tool, not a bound for the original linear carrier. The signed squared-error
flux and its connection to a source-beating linear estimate remain open.
Do not discard its boundary or weight-variation terms, apply the monotone
real-weight bound to an oscillatory test without its hypotheses, or use the
zero-source theorem as an independent estimate. No new zero-free region or
historical novelty is claimed by this slice.

`docs/zeta-prime-lattice-carrier.md` now transports the original linear
carrier to the complete finite sum of `(lambda(n)-1)*K(s,n)`, where lambda
is the ordinary-prime logarithm. Exact first error increments connect it
to the actual integer Chebyshev recurrence without inserting an extra
discrepancy. The signed sawtooth identity keeps both unrounded endpoints;
its full sampling error is at most `C(p,y)*(4/5)^N` at positive orders.
The comparison with the original carrier adds only the old geometric
boundary cost and requires no pole-cancellation condition on the fixed
polynomial. The actual right-half-zero source remains `-m_rho`. The
independent cofinal floor for this full signed lattice sum remains open;
this does not make the separate quadratic work a bound for it. The
sampling constant may depend on the fixed ordinate and coefficient budget.

## Proof-slice workflow

`docs/zeta-vaughan-log-average.md` now evaluates the genuine logarithmic
Vaughan floor-cutoff integral, with its measurable finite cell partition,
unit probability mass and full von Mangoldt endpoint. The same convolution
identity holds for every arithmetic profile. At
`L_N=log((floor(u^(-N)/(N+1))+2)^2)`, every actual cell has square-root
product budget at most `2*(D_N+2)`, and the complete normalized average
budget independently tends to zero. The exact composite squarefree Riesz
band retains the original conditional source `-m_rho`. Completing its
prime deletion restores `log(p)*min(L,log(p))/L`; keep this correction.

For nonunit squarefree composites the full Riesz profile obeys
`R_(log(n)-L)(n)=mu(n)*R_L(n)`. Odd parity gives exact midpoint cancellation
and opposite endpoint values. This is a structural sign identity, not an
independent bound for the full signed band. The reflected cutoff depends
on `n`; replacing the common length by `log(n)/2` inside the source sum
requires a new source-error estimate. The current mixture theorem keeps
its weights independent of the tested integer. The cofinal signed floor,
RH and any further zero-free improvement remain open. No historical
novelty claim is made for these convolution identities.

`docs/zeta-squarefree-vaughan-budget.md` now keeps the physical and divisor
logarithms together before estimating the projected head. Their leading
local derivatives cancel exactly; the remaining prime incidence contains
two local Euler atoms and has a summable prime cost after averaging.
For every bounded complex divisor-weight family, the complete filtered
head has bound `C_y*sqrt(U)*sum norm(p_k)`, with no moment-order or cutoff
logarithm factor. The entire projected small part has the original
`C_y*sqrt(U+1)*sqrt(V+1)*sum norm(p_k)` budget for every cutoff pair.
Independent nonsquarefree deletion now holds for all schedules whose
normalized product budget vanishes. Every moving finite probability
mixture in `(U+1)*(V+1)<=(D_N+1)^2`, with
`D_N=floor(u^(-N)/(N+1))`, preserves the original conditional source in
the full squarefree finite band. Keep the exact weights, product phases,
unit total mass, squarefree support and budget. This does not cover
arbitrary signed mixtures, moving filters without a coefficient budget,
height-uniform constants, or the simultaneous undamped symmetric cutoff.
The exact logarithmic hyperbola average is now compiled in the subsequent
modules above; its independent signed floor remains open.
No larger zero-free region or historical novelty is claimed.

`docs/zeta-squarefree-vaughan-projection.md` now removes the entire
nonsquarefree part of the original finite Vaughan band at
`D_N=floor(u^(-N)/(N+1))`, for every fixed polynomial, `0<u<1` and
`abs(y)>1`, without a zero hypothesis. The literal squarefree projection
retains the conditional source `-m_rho`. The proof averages the full
reciprocal Euler correction at `Re(s)>=1/2` against the summable
`sum tau(d)^2*d^(-3/2)`, pays the exact coprime Mobius--prime cross term,
and separately pays the logged and finite-prime prefixes. This is decay
of the complete signed nonsquarefree sum, not its total variation. Keep
the remaining squarefree support, factor coprimality, Mobius signs and
product phases. The cofinal signed lower bound and RH remain open.
The logged projected prefix alone permits the undamped inverse-source
ceiling; do not extend that statement to the full cross term or entire
Vaughan band. No larger zero-free region or historical novelty is claimed.

`docs/zeta-vaughan-cutoff-budget.md` improves the complete classical
Vaughan reduction from a cutoff-product cost to
`C_y*sqrt(U+1)*sqrt(V+1)*sum_k norm(p_k)`. Actual Chebyshev prime-power
density pays for the entire von Mangoldt prefix without a cutoff logarithm.
For every fixed polynomial, `0<u<1` and `abs(y)>1`, both cutoffs may reach
`floor(u^(-N)/(N+1))` with normalized allowance
`C(p,y)*(u/(N+1)+u^(N+1))`, which tends to zero independently.
Every positive denominator tending to infinity is also allowed, with its
explicit reciprocal cost. General asymmetric cutoff pairs retain the
complete product budget; do not assign both factors the full asymmetric
budget separately. The new concrete cutoff eventually exceeds every
geometric cutoff with base `r>=1` and `u*r<1`, including the preceding
`floor(u^(-N/4))` cutoff. This is not an optimal-cutoff theorem and does
not justify the undamped ceiling `floor(u^(-N))`. The cofactor
`kappa_V(n)=sum_(d|n,d>V) Lambda(d)` is nonnegative, at most `log n`, and
additive on coprime products. The literal bilinear coefficient has the
original divisor-log majorant, so the existing finite-band error applies
uniformly in both cutoffs. At every hypothetical right-half zero, the
complete finite two-large-factor sum retains source `-m_rho`.
The independent cofinal signed lower bound is still open. Do not treat
the conditional negative limit as an independent estimate, call these
factors comparable in size, infer arbitrary-coefficient Type II estimates,
or discard their product phases and shared-prime terms. This is an
application of a classical identity, not a claimed novel identity or a
larger zero-free region. Constants may depend on the fixed filter and
ordinate; no moving-filter or height-uniform estimate is supplied.

The current explicit endpoint is `ZetaUnifiedZeroFree.exact_strip`, described
in `docs/zeta-unified-zero-free.md`. It retains the maximum of the earlier
signed-pole/reserve width and the two Gaussian widths at every ordinate.
The Gaussian analytic estimates still start at absolute height 1000000;
below that height their physical cap is proved strictly smaller than the
older reserve, so the combined elementary maximum needs no height premise.
Preserve both containment theorems when changing the displayed region. A
better large-height coefficient must never silently remove older coverage
at modest heights. Literal nonvanishing includes the closed right edge and
explicitly excludes the pole at one.

With L=log(abs(t)+2), the four elementary widths are
792/(7625*L-2000), min(4/39,4752/(45750*max(13/10,L)-35725)),
min(1/450000,221/(250*(L+2052*log(L)+30240))), and
min(1/40500,1547/(1800*(L+1995*log(L)+29400))). The two Gaussian
branches pay their full q>=1 and q>=9/100 costs, respectively.
`SquarefreeUnifiedRegion` transports the combined width through the full
doubled window and gives the original response radius for abs(y)>=3,
preserving every Gaussian radius and the complete signed prime envelope.
Constants may depend on the center. Keep older multiplicity, separation,
filter-cost and energy theorems at their stated widths; a new radius cannot
be silently substituted into them. The eventual log-log component retains
its original unevaluated threshold.

The active benchmark target is pointwise coverage of every applicable
region in the audited literature table, with height ranges and edge
conventions preserved. This has not been achieved: lower-height
classical/Littlewood and eventual VK gaps remain. Do not describe the
restored endpoint as unbeaten at every height, or the external proofs as
imported. `ZetaGaussianExpandedComparison.nonvanishing_and_comparison`
now extends the strict headline comparison to `(L_*,480000]`, where
`L=log(abs(t))` and `L_*` is the earlier exact crossover. The new interval
is certified, not asserted maximal. The proof pays the plus-two scale
correction and bounds the actual complete width below by `18/(25*L)`
on `[300000,480000]`. It covers the generic classical, Littlewood and VK
denominators and the full intermediate/Ford expressions there; the older
proof covers the remaining overlap down to `L_*`. The earlier exact
constant-plateau ceiling remains a separate historical theorem. The graph
must use the new checked endpoint while showing all remaining global gaps;
its default theorem stays the complete all-height proved region.

`docs/vinogradov-korobov-framework.md` records the proved signed finite
logarithmic expansion, its transport to the full weighted product sum,
actual product-shift averaging and damping transport, and the exact
all-order torus-moment/equal-frequency tuple-count identity. The
monomial instance is the literal unit-cube Vinogradov integral, and its
first moment is exactly N. Preserve the full weighted complex Gram form.
The exact remainder identity holds for every nonnegative ratio. The unit
base phase, parity sign, both factor monomials and all complex weights
survive before the perturbation estimate. `VinogradovKorobovBlock` keeps
the signed boundary and the outer base phases in the complex approximation.
Its boundary majorant uses the actual mean shifts; do not silently replace
this by the largest product or round integer endpoints. The error bound
controls the difference between actual complex prefixes and their
approximation, which transports through Abel summation.
`VinogradovKorobovDamping.feature_approximation_error_le` pays the actual
damping mass for the original `zetaPrimeFeature` at positive integer starts
and nonnegative real parts. `VinogradovShiftedMoment` now bounds every
shifted frequency-difference count by its homogeneous count and proves the
even-moment majorant for bounded complex weights. `VinogradovMomentReduction`
proves the two-Hölder reduction with exact frequency multiplicity mass and
energy. `VinogradovKorobovMoment` applies it to the actual product polynomial
at its exact real sampling coordinates. Keep the joint attainable tuple-
frequency support and the explicitly defined phase-dependent alignment
weights in `two_holder_bound` until an explicit estimate uses them; a rectangular support enlargement is a separate loss.
`VinogradovGaussianKernel` now proves genuine lattice summability,
multivariate Gaussian Poisson summation and the complete signed Gram
identity. Its dual-moment majorant pays the exact maximum exponent cost on
the attainable joint support. Gaussian majorization adds frequencies
outside that support, so retain the exact restricted `dualMoment` upstream;
the maximum cost alone does not preserve its holes or multiplicities.
`VinogradovKorobovMoment.interval_gaussian_bound` applies it to the actual
interval sum with the canonical alignment weights. A positive spatial
kernel does not make the individual complex cross terms positive. Keep
all integer translates, coordinate differences and tuple-weight products
until an explicit estimate uses them. A quantitative saving for this Gaussian
Gram form and the homogeneous mean value remains open.
`VinogradovGaussianResonance` now groups the exact signed Gram form by the
full integer power-sum difference vector. Its bounded-weight majorant uses
the homogeneous moment on each complete fibre and retains the entire joint
resonance support and every Gaussian translate. The actual interval product
sum reaches both homogeneous moments and this resonance sum in
`VinogradovKorobovMoment.interval_resonance_bound`. Keep the signed fibre
identity upstream of the norm bound; removing its weights is a documented
loss, not a proof that the actual phase correlations are irrelevant.
`VinogradovGaussianBounds` pays every translated Gaussian tail with a
uniform fractional-phase envelope and an explicit geometric denominator.
Its distance estimate works for moving phases; do not substitute a
fixed-phase asymptotic. `VinogradovGaussianCentering` preserves the complete
complex sample under an integer frequency translation by retaining the
exact unit phase twists of every original weight. The canonical interval
midpoint pays all rounding and gives at most one quarter of the origin's
Gaussian exponent cost, proved in `interval_centered_cost_le_quarter` for
positive tuple order and a nonempty interval. The actual product sum uses
this in `interval_quarter_envelope_bound`. This is a quartering of the
exponent cost, not of the whole product bound or a new zero-free width.
`VinogradovPowerSumRigidity` now evaluates Newton identities for arbitrary
integer tuples and retains repeated entries in the resulting multiset
equality. For every finite set of distinct integers, collisions at `r<=k`
are exactly permutations, giving `J_(r,k)<=r!*N^r`. At every order the
elementary bound is `min(r,k)!*N^(2*r-min(r,k))`. Both moment factors are
paid explicitly in `interval_explicit_moment_bound`, with the same quartered
Gaussian cost and complete joint resonance envelope. These are classical
base estimates, not historical novelty or the full VK saving. Do not keep
listing every homogeneous moment estimate as unproved. Keep the exact
signed centred Gram identity upstream.
`VinogradovPrimePowerRigidity` now proves the full power-sum Jacobian,
its nonsingularity for distinct residues modulo p>k, exact nonlinear
prime-power lifting, permutation rigidity and the at-most-k! complete
nonsingular fibre bound. Newton identities share one general domain proof
with the existing integer theorem. Arbitrary correlated target families
retain their actual cardinality before taking coordinate products.
`VinogradovAnisotropicCongruence` pays separate precisions e_i<=n with
p^(sum(n-e_i))*k!, and instantiates the actual degree moduli p^b,...,p^(kb)
with p^(b*k*(k-1)/2)*k!. The unsigned count is for canonical residue tuples with
distinct residues modulo p. `VinogradovSignedRigidity` now reconstructs
any complete signed moment fibre over a domain as exactly the permutations
within its two sign classes, with cardinality r+!*r-! for distinct reference
entries. `VinogradovWeightedLifting` pays all nonlinear remainders with
arbitrary integer weights nonzero modulo p. `VinogradovSignedCongruence`
retains the signs and any common integer translation at all precisions,
with correlated-target cost T.card*r+!*r-! and degree-modulus cost
p^(b*k*(k-1)/2)*r+!*r-!. `VinogradovConditionedMoment` retains the complete
binomial translation and derives the actual degree congruences when both
tail tuples lie in eta modulo p^b. Its `conditioned_block_card_le` bounds
the nonsingular residue-block projection of those original moment equations.
It does not count tail completions or the whole moment. Keep the exact
sign partition and correlated targets upstream of their product bounds.
`VinogradovCoarseCongruence` now pays the full coarse precision cost.
For 1<=k<p, a<=b, a common residue xi modulo p^a, and distinct normalized
next digits, `conditioned_residue_card_le` bounds the original canonical
tuples by p^((a+b)*k*(k-1)/2)*r+!*r-!. Full weighted translation retains
all lower degrees; integer quotient reconstruction and its injectivity
connect the normalized count back to the actual tuples. Quotient division
must occur in Nat before casting to ZMod; field division by p is not this
condition. Correlated complete targets remain upstream. The proved
colour-factorial comparison supplies the classical k! allowance, and
`conditioned_moment_card_le` gives the corresponding actual moment-block
projection. This is the coarse-conditioned congruence counting ingredient,
including a>0; do not continue listing that whole count as open. The
canonical representatives are 0,...,p^(k*b)-1 and a=b is also permitted.
These are classical ingredients, not a historical novelty claim.
`VinogradovAffineMoment` now proves exact affine invariance of complete
integer moments and the full complex homogeneous Gram coefficient.
`VinogradovResidueMoment` reconstructs the actual positive residue window,
retaining its exact quotient support before the explicit enlargement to
floor(X/q)+1. Every fixed tail target is bounded by the literal normalized
mean value J_(r,k)(floor(X/q)+1); `tail_completions_le_meanValue` applies
this to actual completions of each fixed pair of integer-weighted blocks.
`VinogradovSignedTailMoment` crosses the two variables at negative positions,
preserving the entire frequency target. `signed_weightedShift_eq_crossed`
retains every original complex pair weight through explicit conjugation.
Every fixed tail sign pattern has the same normalized completion bound.
The crossing acts on complete tuple products; additional joint constraints
within a tuple, including nonsingularity, require separate transport proofs.
Do not list all tail bounds as open. `VinogradovConditionedCompletion`
now combines the coarse count with every signed finite tail completion for
each fixed opposite block. It retains arbitrary integer coefficients on
both blocks and tails through translation, and an exact supported row sum
before its product bound. `conditioned_complete_count_le` counts canonical
block representatives in Fin(p^(k*b)), not arbitrary block integers <=X.
`VinogradovCongruenceEnergy` now retains the full complex fibre Gram form
and pays the pointwise Cauchy estimate with the actual signed fibre count.
`coarse_product_energy_le` applies it to products of actual positive
residue-window Fourier sums for every finite endpoint X. Each reversed
power-vector phase is exactly conjugated before its norm is simplified.
This is the pointwise ingredient in Wooley equation (6.5).
`VinogradovMomentPartition` now partitions the full original complex Gram
form and actual torus energy by all translated degree targets. Actual
positive tail windows discharge the complete collision condition, and
arbitrary integer coefficients and complex configuration weights survive.
`VinogradovPartitionEnergy` retains the exact coarse/fine polynomial
refinement and proves its full integral estimate with all integrability
and finite sum exchanges paid. `VinogradovResidueEnergy` then discharges
both arithmetic conditions for the original block entries: reduction modulo
p^(k*b) preserves their coarse class, normalized next digits and every signed
degree target. For 1<=k<p and a<b, `conditioned_whole_integral_le` pays the
whole original energy by the sum of its finer block-residue energies, with
cost p^((a+b)*k*(k-1)/2)*r+!*r-!. `window_whole_integral_le` applies it to all
admissible positive blocks and literal tail windows up to X, retaining
arbitrary complex weights and their correlations. Unlike the earlier
canonical block count, this whole-moment theorem includes original entries
up to X. Do not keep listing the exact target partition or this whole-moment
transfer as open. These are the ingredients underlying Wooley (6.4)--(6.6);
`VinogradovProductEnergy` now proves the actual product factorization.
Its finer-fibre bijection retains every original block entry, and
`window_fine_polynomial_eq_product` keeps arbitrary complex tail weights,
including correlations and joint restrictions between tail entries.
`conditioned_product_norm_energy_le` applies the whole-moment theorem to
those literal product factors, after the exact complex identities.
The actual finer-residue cardinality and weighted finite mean inequality
then give `conditioned_product_max_le`: the original energy is at most
r+!*r-!*p^((a+b)*k*(k-1)/2)*(p^(k*b-a))^k times the actual maximum over
canonical finer residues of integral(|f_(p^(kb))|^(2k)*|Tail|^2). No unproved
moment-budget premise remains. The full correlated tail polynomial survives,
and the exact fibre energies remain upstream of the maximum. Do not keep
listing this factorization or first finite Holder bound as open. The analytic
interpolation and higher homogeneous comparison are now proved as described
below; complete conditioning of arbitrary tuples and stronger high-moment iteration
remain open.
`VinogradovFourierEvaluation` now keeps complete complex frequency fibres
and proves point evaluation is at most attained-frequency count times the
actual energy. `ZetaRieszConditionedEnergy` applies signed congruencing
directly to the original Riesz carrier. Its full Fourier lift at zero and
exact residue partition retain the entire band, coefficient, logarithmic
phase, damping and filter. `actual_band_le_mixed_moments` bounds that literal
carrier by actual finer mixed moments with all sampling, congruence and
residue-summation costs explicit. The normalized theorem uses coarse class
zero; p^(a+1)<=2^(32*N) supplies an explicit nonsingular block and proves
the literal block count positive. The multiplied bound also covers empty
windows. Keep `amplified_moment_eq_gram` and the exact residue Gram identity
upstream of all majorants. `tendsto_actual_residue_source` retains the
original negative-multiplicity source and common length. Do not replace
the common length by log(n)/2, silently delete prime corrections, identify
the logarithmic phase with a polynomial, or treat torus energy as a free
pointwise estimate. The actual weighted mixed-moment saving after all costs
remains open. No new zero-free width follows from this bridge.
`VinogradovBlockMass` now injects every next-digit embedding and complete
higher quotient choice into the actual original block family. It gives
C>=p.descFactorial(k)*floor(X/p^(a+1))^k and the explicit real lower bound
p.descFactorial(k)*(X/(2*p^(a+1)))^k when a complete window fits.
`ZetaRieszBlockMass.actual_band_le_explicit_block_mass` uses this proved
positive mass in the original carrier bound. `VinogradovInterpolation`
proves the actual continuous Holder step (Wooley6.8), including u=1,
zero values and all Lp conditions. `ZetaRieszInterpolation` applies it to
the original weighted Riesz tail: M_eta<=H_eta^(1-1/r)*V_eta^(1/r), where
H_eta is the actual (2r+2)-moment and V_eta is the actual maximum of
integral |R_eta|^2*|f_fine|^(2kr). `actual_band_le_interpolated_moments`
retains all source weights/cutoffs and the explicit block denominator.
Do not keep listing this analytic interpolation or the block normalization
as open. The quantitative weighted-moment saving, the high-moment exponent improvement and full iteration remain open. The reverse mixed moment has a squared
Riesz factor; it is not assumed controlled. No new universal zero-free width
is claimed.

`VinogradovConditionedHigherMoment` now injects the original conditioned
blocks into full signed residue tuples, preserving every power coordinate.
The count comparison precedes sign crossing; no within-block nonsingularity
invariance under crossing is assumed. Every shifted count and bounded joint
complex weight receives J_(u*k,k)(floor(X/p^b)+1), and so does the actual
higher conditioned moment. `VinogradovCongruencingStep` retains all original
block restrictions in an exact image tail weight. Its
`conditioned_congruencing_step` transfers the actual energy K_(a,b) to
J_((u+1)*k,k)(floor(X/p^b)+1)^(1-1/u) times the actual reverse mixed maximum
I_(b,k*b)^(1/u), paying the explicit signed congruence and residue-count cost.
The statement keeps independent block colours, every finite endpoint and all
rounding. This is the finite inequality underlying Wooley (2012), Lemma 6.1;
it assumes no moment budget. Do not list the higher homogeneous comparison
or this finite transfer as open. The high-moment exponent improvement and
high-moment iteration remain open, as does the quantitative saving
for the original weighted Riesz moments after all sampling costs. No new
zero-free width follows from this finite step.

`VinogradovConditioningSupport` now uses the joint class support of both
sides of each original collision. It selects an actual nonsingular block,
retaining its induced signs and exact complement, or covers the singular
support by literal sets of k-1 classes. Their count is choose(p,k-1).
`VinogradovResidueDigits` gives exact finer-window equivalences and full
complex polynomial refinement at p^(b+1), with the original cutoff retained.
`VinogradovSingularConditioning` identifies the actual mixed moment with its
complete original collision count and splits it exactly into singular and
nonsingular contributions. The terminal `singular_count_le_next_mixed_max`
bounds the singular contribution by choose(p,k-1)*(k-1)^(2s) times the actual
next-level mixed maximum. All finite Holder and integral hypotheses are paid;
no supplied moment budget is assumed. This closes the singular contribution
underlying Wooley (2012), equation (5.2). Do not list that contribution or its
class refinement as open. The nonsingular estimate and one-step conditioning recurrence are now
proved by the following modules; their high-moment exponent improvement and
high-moment iteration remain open. Neither the
original weighted Riesz saving nor any larger zero-free width follows yet.

`VinogradovSignedComplement` retains every selected position, induced sign
and exact complementary frequency; its full complex factorization precedes
the norm bound. `VinogradovNonsingularSelection` injects each qualifying
original pair into both original blocks, the actual selected block and its
full complement, and covers T2 by the actual selected-position families.
`VinogradovConditioningHolder` proves continuous Holder with zeros included
and explicit AM-GM absorption. `VinogradovNonsingularConditioning` proves
T2<=D*K_*^(1/(2u))*I^(1-1/(2u)), s=k*u, D=(2s).descFactorial(k), retaining
the sum of induced-sign moments before the maximum. Its `conditioning_step`
proves I<=2u*A*I_+ + D^(2u)*K_*, A=choose(p,k-1)*(k-1)^(2s), for nonzero
p,1<=k<=p,u>=1,eta<p^b and the original finite X. All moments and maxima
are actual; no budget is assumed. These explicit constants are not optimized.
This closes the finite step underlying Wooley (2012), Lemma 5.1. Do not list
either collision bound, this Holder step or this one-step recurrence as
open. Improving the high-moment exponent through further iteration remains open.
The weighted Riesz moments are not identified with these unweighted moments;
their required saving and every new VK zero-free width remain unproved.

`VinogradovConditioningRemainder` now iterates the actual level maxima:
L_b<=S^H*L_(b+H)+E*sum_(h<H)S^h*Q_(b+h), preserving every finite cost.
Its remaining factor receives the two literal higher moments at
floor(X/p^a)+1 and floor(X/p^(b+H))+1. `VinogradovRemainderScaling`
retains the exact scale identity and proves the exponent inequality for
all lambda>=2k(u+1)-k(k+1)/2. `VinogradovConditioningPowerSaving` pays
the actual rounding with C=2^(k(2u+1))*k! and the iterated constant
D=2u*(k-1)^(2ku). For k>=2,u>=k,a<=b,H>=1,b-a<=2H,p^(b+H)<=X,
and (C*D)^2<=p, the actual remainder S^H*L_(b+H) is at most
(X/p^a)^k*(X/p^b)^(2ku)*p^(-H/2). The same threshold proves k<p.
`finite_conditioning_power_saving` inserts that bound into the actual
finite recurrence without any supplied moment-budget premise. Do not
list this elementary remainder saving, its constant absorption, or its
finite iteration as open. Keep the finite cutoff condition; this is not
a decay limit in H at fixed X. The general exponent transfer explicitly
requires its two homogeneous-moment bounds, which are discharged by the
final theorem only at the elementary exponent. Improving the high-moment
exponent and the full congruencing iteration remain open. No original
Riesz weighted saving, VK zeta growth or new zero-free width is claimed.

Stronger high-order moment bounds and
quantitative joint resonance control,
the required exponential-sum saving, zeta growth and the VK zero-free region
remain unproved here. Do not add a VK curve to the proved union or promote a
conditional transfer as that analytic proof. The independent cofinal signed
arithmetic floor and RH remain open. Numerical verification stays in its
optional target; do not edit its fingerprinted inputs during a live run.

Work in one coherent slice at a time. A slice should close a real lemma or
interface needed by the current RH frontier, not merely add parallel
abstractions.

1. Inspect `git status`, the imported theorem chain, the current dashboard
   data, and any newly supplied research dispatch before editing.
2. State the exact mathematical obstruction and the theorem that removes a
   concrete part of it. Check that its assumptions are available upstream.
3. Put new mathematics in a focused module with a module docstring and
   theorem-level documentation. Import it from `RiemannGaussian.lean` so the
   root environment and full build contain it.
4. Compile the changed module directly with warnings treated as errors.
5. Run the whole-package declaration linter, which includes every new public
   declaration. Use its verbose form during an audit when the individual
   results need to be recorded. Fix all findings; do not suppress them merely
   to pass.
6. Run `#print axioms` on the slice's terminal theorems. The result may contain
   only `propext`, `Classical.choice`, and `Quot.sound`.
7. Run the source placeholder scan, whole-project declaration lint, focused
   build, full build, generated-status check, and whitespace check described
   below.
8. Keep exactly two live research-status sections near the top of the README:
   `Current Direction` states the active strategy and immediate frontier, and
   `Latest Update` states only the newest verified slice and its next
   obstruction. Review both on every committed slice, replacing stale text
   rather than appending history. The README is never an audit log. Update the
   `Current Direction` body must be exactly one paragraph and no more than 500
   characters; replace it instead of extending it. Update the
   milestone list in `scripts/GenerateProjectStatus.lean` when and only when a
   new theorem genuinely advances the displayed frontier, then regenerate the
   artifacts.
   The generated panel is a theorem inventory, not a proximity meter: never
   draw a causal edge between milestones unless a checked theorem proves that
   implication, and label RH equivalences as reformulations rather than
   progress on their open direction.
   In the README, display only the latest proved zero-free region in its own
   `Proved Zero-Free Region` section immediately after the introduction. Display the
   bound prominently and link directly to the compiled Lean proof. Include
   a brief linked entry in `Accomplishments` too. State its exact bound and
   height-threshold scope, including whether the threshold is existential or
   numerically evaluated.
   When a stronger region is proved, replace the previous README presentation
   and remove references to superseded smaller regions, including historical
   comparison constants, duplicate table rows, and old accomplishment entries.
   Retain proof history and older bounds in the Lean sources and detailed
   documentation; the README is not a history of zero-free-region improvements.
   Keep `Accomplishments` to exactly ten major accomplishments. Select by
   mathematical significance, breadth and relevance to the project's goals,
   rather than recency or the number of new lemmas. A new entry may replace
   an existing one only if it is materially more significant; otherwise keep
   the result in `Notable Formalisations`, its detailed documentation and the
   generated inventory. Consolidate related theorem steps into one result
   rather than spending multiple slots on the same advance. Preserve source
   attribution, scope and any unevaluated thresholds when shortening text.
   Place `Repository Structure` immediately after `Accomplishments`. Keep it
   compact: link the complete generated theorem-family index and give a short
   directory map; do not copy module inventories into the README. Preserve
   existing Lean source paths and imports, as requested by the user.
9. Apply the current theorem-push commit gate. Commit and push the complete
   slice only after its actual mathematical target and all verification
   gates pass. Track GitHub Actions on that exact commit SHA. Per the user's
   2026-09-13 instruction, continue local theorem work while CI runs.

Lake builds independent modules in parallel. Direct elaboration of one Lean
module is normally one process; do not mistake that focused check for the
parallel full-library build.

## Commit and check-in invariant

The zero-free section's interactive theorem explorer is derived from the
compiled Lean dependency graph and the existing proof-status metadata.
Maintain logical families and optional theorem reading labels in
`docs/theorem-explorer/metadata.json`; theorem statements, docstrings, source
locations, dependency edges and transitive axiom audits come from Lean.
The same family metadata drives `docs/theorem-families/` and the Lean source
directory's landing page. Every project source module must have an
unambiguous family and be reachable from the ordinary root or the explicitly
optional `NumericalCertificate` root. Assign new modules
by an appropriate prefix or explicit override, then run
`scripts/build_theorem_explorer.py` to regenerate both indexes and explorer
assets. Its `--check` mode rejects missing, ambiguous or stale assignments and
stale generated pages. Keep one shared family taxonomy; do not hand-edit the
generated indexes or duplicate their full contents in the README.

Per the user's explicit numerical-certificate build instructions, exhaustive
certificate verification is opt-in. Keep generated `CertificateData` and every
module importing it out of `RiemannGaussian.lean` and `defaultTargets`; import
them from `NumericalCertificate.lean` instead. Normal CI and pre-commit builds
must not trigger those computations. The manual
`.github/workflows/numerical_certificate.yml` workflow checks prerequisite
data, eight disjoint cover shards, then the complete assembly and
`scripts/AuditNumericalCertificate.lean`. Caches accelerate unchanged inputs.
Hosted runners compile one prerequisite or two cover modules at a time and
have eight GiB of additional swap. The dedicated `NumericalCertificateData`
library owns only `RiemannGaussian.CertificateData` submodules. Its
performance-only `weakLeanArgs` disables asynchronous elaboration there,
preserving Lake's proof traces and independent module scheduling. Ordinary
proofs keep their established elaboration mode: changing it globally produced
a different generated-helper inventory between cached local and cold CI
builds. Do not weaken dashboard freshness or the complete axiom audit to
accommodate that difference. The hook and both CI workflows run
`test_numerical_certificate_build_config.py` after installing Lean; tiny
compiled probes check actual library ownership, elaboration modes and the
default import boundary without compiling certificate proofs. A strict
cold anchor check passed at about 7.5 GiB peak resident memory with that
setting; the asynchronous check exceeded its 12 GiB limit. Retain this
setting unless a replacement has a measured resource budget.
Progress reports include memory and disk
headroom. SIGTERM must stop the owned compiler process group and leave an
interrupted verdict, with no success marker; the regression includes an
actual spawned descendant. The first hosted run terminated while compiling
four anchor modules concurrently, so do not restore that concurrency without
a measured memory budget.
Artifacts from that same run transport checked prerequisites and all shards,
so cache eviction cannot remove a required inter-job dependency. The cold
option skips restored project certificate caches. Run the applicable
optional target and axiom audit locally when its proofs change; a default
build alone does not validate them. Preserve labels separating checked
components, the full cover, and an unconditional literal-count endpoint.
The final audit must type-check the actual unconditional dyadic and
cumulative statements and inspect their proof axioms before writing its
report. Run `scripts/test_numerical_certificate_audit.py` after the optional
target is built; it requires the genuine audit to pass before rejecting a
conditional replacement without a success report. Normal CI runs only the
fast build-boundary and scheduler regressions. Failed or changed-input runs
must remove stale success markers; partial jobs cannot claim a full result.
The current certificate work stays in this repository; an upstream PR is no
longer requested. See `docs/numerical-certificate.md` and its JSON metadata.

Use `python3 scripts/verify_numerical_certificate.py --jobs 4` for a cold
complete-cover build. It bounds concurrent heavy compiler processes and
retains each finished group's Lake artifacts. Small kernel reductions and
proved child-box equalities keep peak memory bounded; do not replace these
with one giant reduction of the entire tree. The driver records its live
process and progress and rejects an input digest change during the run.
Inspect that process before restarting; preserve completed artifacts. Keep
proof inputs stable while a verification run is active. Documentation outside
the input digest may be updated without interrupting it.

The README's `Proved Zero-Free Region` is the first section after the introduction.
Keep its mathematics in compact, readable display-math boxes using
`\boxed{\begin{gathered} ... \end{gathered}}` inside GitHub-supported math
blocks. Prefer fenced `math` blocks: they preserve TeX line breaks and
subscripts without Markdown escape processing. Write strict inequalities
with `\lt` instead of a bare `<`: GitHub's math renderer reparses formula
text as HTML, so `<L` or `<A` can swallow part of a formula and produce a
misleading "Missing close brace" error. Include assumptions and
endpoint conventions in the presentation;
do not leave formulas or coefficient ranges scattered in inline code.
Wrap each display box in a single-cell HTML table, with blank lines around
the fenced math block, so the frame remains visible when a browser's native
MathML renderer omits the `\boxed` border.
Show only the current proved union, with a direct Lean proof link. An
eventual component must state that its coefficient-dependent threshold is
unevaluated unless an actual numerical threshold has been proved.

Keep the colour comparison graph prominent at the start of `Proved Zero-Free
Region`. Its source annotations, colours and plotting ranges live in
`docs/zero-free-regions/metadata.json`. `scripts/ExportZeroFreePlot.lean`
checks the numerical expression trees against the actual imported width
definitions, the starting height and exact comparison endpoints. Run it after
the ordinary Lean build, then use the pinned environment in
`scripts/requirements-plots.txt` with `scripts/build_zero_free_plot.py`.
Commit the generated SVG, formula export and audit together. Do not edit
generated curves or copy their constants into a second plotting formula.
Update the checked formula interface when the proved region changes; its
endpoint must match the default proof-status theorem. Preserve `log(abs(t)+2)`
in the Gaussian curve, the exact crossover and ceiling, open/closed edges,
and the distinction between inspected and merely reported external results.
Never draw an eventual region from an invented finite starting height. The
overview must show heights where the external benchmark is stronger as well
as the magnified comparison interval; the graph does not establish a world
record or import an external analytic proof. Ordinary CI and pre-commit run
the exporter and `--check` to reject stale artifacts, without invoking the
optional numerical certificate. The GitHub README renderer check must also
verify the section title, graph placement, image load, enlargement link and
desktop/mobile fit. See `docs/zero-free-regions/README.md` for reproduction.

Keep benchmark details in `docs/zero-free-literature-frontier.md`, linked
from the compact zero-free section. Record source version, theorem/equation,
height range, open/closed edge, proof or retrieval status, and the relevant
compiled comparison theorem. Distinguish inequalities between explicit
width functions from importing external zero-free proofs. Preserve the
exact crossover and ceiling, including the enlarged height's `+2`; strict
improvement excludes the crossover where widths tie. No exhaustive record
claim follows from checking only headline constants or from an eventual
bound with an unevaluated threshold.

The interactive explorer belongs inside that same README section as a
linked preview and compact links, with the full interface on GitHub Pages.
Place a prominent, descriptive link immediately above or alongside the
clickable preview so readers know to open the interactive explorer.
It must support zooming, theorem selection and hover metadata, coloured
logical-family zones, and links to the exact Lean file and declaration line.
Expose the evergreen repository metadata and proof audits alongside it.
Do not hand-maintain theorem statements, source lines, dependency edges or
audit verdicts in the README or generated site. For a new comparison or
terminal endpoint, update its status references and reading labels in the
metadata; retain the actual zero-free conclusion as the default endpoint.
After changing an endpoint or its dependencies, run
`scripts/ExportTheoremGraph.lean` and `scripts/build_theorem_explorer.py`, then
check the generated assets and run `scripts/check_theorem_graph.cjs` and the
browser interaction checks. Every compressed edge must have an exported
dependency-path witness. Keep the README presentation to the linked preview
and its compact explorer/metadata/audit links. Publish only a verified source
snapshot, with GitHub links pinned to its commit; respect the user's current
commit and push instructions.
Check the rendered README math and the explorer at desktop and narrow
viewport widths after presentation changes. Confirm navigation, source-line
links and audit links in the published artifact after exact-commit CI passes.
For every README presentation change, run `scripts/test_github_readme.py`
with the pinned Playwright browser before committing. It sends the working
README through GitHub's Markdown API and its live `math-renderer` component;
a standalone MathJax render is not a substitute. Require every math block to
render without an error, retain its box and fit its available width at
desktop and mobile sizes. Wait for a loaded graph and positive visible
layout together before measuring it; GitHub hydration can temporarily
replace an article. Keep all fit, placement and math assertions enforced.
This check is also a mandatory CI step before
Pages publication. After pushing, run it again with `--published` to check
the actual README page at the exact current commit. A network or renderer
failure is a failed check, not a reason to claim rendering success. The
script writes screenshots and a JSON report under `.lake/github-readme/`.

The repository history is the durable record of verified progress. Enforce
this regime yourself; do not rely on the user to request individual commits,
pushes, or CI checks.

- The user authorized parallel theorem development and CI on 2026-09-13,
  until further notice. Continue local work while CI checks a committed
  snapshot; keep verification and publication claims attached to that exact
  SHA. This supersedes earlier instructions to wait before starting a slice.
- The user also authorized committing and pushing all accumulated work once
  the complete numerical certificate and its optional cached CI workflow are
  ready. Preserve the running verifier's frozen inputs until it finishes;
  partial cover verification is not readiness of the literal-count endpoint.
- Keep one coherent mathematical slice per commit. Include infrastructure or
  documentation changes needed by that theorem advance. Do not mix unrelated
  cleanup into the slice.
- Before committing, stage the complete intended slice and verify the staged
  content with all applicable local gates, `git diff --cached --check`, and
  the tracked pre-commit hook. Documentation-only and CI-only commits are not
  exempt from the gate.
- Do not bypass the pre-commit hook. If an exceptional environment prevents
  the hook from running, execute every command it enforces manually and record
  that fact in the handoff.
- Push each passing commit promptly, record its full SHA, locate the workflow
  run whose `headSha` is exactly that SHA, and require a `success` conclusion.
- While exact-SHA CI is pending, continue local proof work. If CI fails,
  prioritize its repair, preserve later local work, rerun affected gates and
  verify the repair commit. Do not report a pending or failed SHA as green.
- Progress reports and handoffs must distinguish local success from remote
  verification and should cite both the exact commit SHA and CI run number.

## Mandatory local gates

Use the repository's pinned Lean toolchain. In environments where `lake` is
not already on `PATH`, invoke the pinned binary through the configured
`ELAN_HOME` rather than changing the project version.

Enable the tracked pre-commit gate once in every fresh clone:

```bash
git config core.hooksPath .githooks
```

The hook repeats the staged placeholder scan, warning-as-error build,
whole-project declaration lint, compiled-environment/dashboard audit, and
staged whitespace check. CI remains authoritative because local hooks can be
bypassed and a partially staged commit may differ from the working tree.

For a changed module `RiemannGaussian/NewSlice.lean`, the minimum gate is:

```bash
lake env lean -DwarningAsError=true RiemannGaussian/NewSlice.lean
lake env lean -DwarningAsError=true /tmp/RiemannGaussianAudit.lean
if git grep -nE '\<(sorry|admit|sorryAx)\>' -- '*.lean'; then exit 1; fi
lake env lean -DwarningAsError=true scripts/LintProject.lean
lake build RiemannGaussian.NewSlice --wfail
lake build --wfail
lake env lean -DwarningAsError=true scripts/GenerateProjectStatus.lean
git diff --exit-code -- docs/proof-status.json docs/proof-status.svg
git diff --check
```

The temporary audit file must import the root library. Its verbose lint command
and explicit axiom commands for terminal theorems have this form:

```lean
import RiemannGaussian
import Mathlib.Tactic.Linter
#lint+ in RiemannGaussian
#print axioms RiemannGaussian.newFrontierTheorem
```

The generator is also a soundness gate. It scans every declaration in
compiled project modules for indirect placeholder dependencies, rejects all
project-defined axioms and disallowed transitive axioms, and verifies that
every green dashboard milestone is an actual project theorem using only the
three permitted standard axioms.

Public status language is an additional gate: never describe an abstract or
conditional `13/18` statement as a result. Until a theorem over literal zeta
counts discharges the required eta-arithmetic inequality, README, dashboard,
commit messages, and handoffs must say that no `13/18` certificate exists.

## GitHub gate

Do not infer remote success from a local build or from a workflow attached to
another commit. After pushing:

1. Record `git rev-parse HEAD`.
2. Locate the GitHub Actions run whose `headSha` is exactly that value.
3. Wait for it to finish and require conclusion `success`.
4. Record that the checked snapshot is green. Later local changes still
   require their own gates before being committed.

If CI fails, repair the same slice, rerun every affected local gate, push the
repair, and verify the new exact commit. The user permits continued local
mathematical work during CI; preserve exact-SHA status throughout.

## Research discipline

- Prefer exact identities, coercion lemmas, summable dominators, and explicit
  quantitative estimates that can be reused downstream.
- Distinguish finite-window, infinite-sum, boundary-limit, and large-height
  statements in names and hypotheses.
- Treat division, logarithmic derivatives, contour deformation, exchanged
  limits, derivatives under integrals, and sum-integral swaps as proof
  obligations requiring their own hypotheses and Lean theorems.
- New mathematics is welcome. Grow it from the checked chain, isolate its
  genuinely novel lemma, test finite or numerical shadows when useful, and
  then prove the general statement in Lean.
- Never claim RH is proved until the completion audit reaches an unconditional
  term of `RiemannHypothesis` and all local and exact-commit remote gates pass.
