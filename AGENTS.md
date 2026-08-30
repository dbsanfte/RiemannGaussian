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
work law. These are finite identities; no infinite operator, heat-time
integral, or cancellation estimate has been inferred. The next live bridge is
to derive a controlled heat transform of the leading current that produces
the signed `1/(log n-log m)` kernel required to apply the checked
Montgomery--Vaughan estimate. That transform and its eta-arithmetic estimate
must be proved, not assumed.

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
- External research notes are leads, not trusted inputs. Re-derive every fact
  in Lean from already checked definitions and theorems.
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

## Proof-slice workflow

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
8. Update the README only for stable explanatory changes. Update the milestone
   list in `scripts/GenerateProjectStatus.lean` when and only when a new
   theorem genuinely advances the displayed frontier, then regenerate the
   artifacts.
   The generated panel is a theorem inventory, not a proximity meter: never
   draw a causal edge between milestones unless a checked theorem proves that
   implication, and label RH equivalences as reformulations rather than
   progress on their open direction.
9. Commit and push the complete slice. Wait for GitHub Actions on that exact
   commit SHA to finish successfully before beginning another slice.

Lake builds independent modules in parallel. Direct elaboration of one Lean
module is normally one process; do not mistake that focused check for the
parallel full-library build.

## Commit and check-in invariant

The repository history is the durable record of verified progress. Enforce
this regime yourself; do not rely on the user to request individual commits,
pushes, or CI checks.

- Begin a new slice only from a clean worktree whose current `HEAD` has a
  successful GitHub Actions run with exactly the same full commit SHA.
- Keep one coherent mathematical or infrastructure slice per commit. Do not
  mix unrelated cleanup into it, and do not leave concrete verified progress
  only in the working tree.
- Before committing, stage the complete intended slice and verify the staged
  content with all applicable local gates, `git diff --cached --check`, and
  the tracked pre-commit hook. Documentation-only and CI-only commits are not
  exempt from the gate.
- Do not bypass the pre-commit hook. If an exceptional environment prevents
  the hook from running, execute every command it enforces manually and record
  that fact in the handoff.
- Push each passing commit promptly, record its full SHA, locate the workflow
  run whose `headSha` is exactly that SHA, and require a `success` conclusion.
- While exact-SHA CI is pending, do not start or commit the next slice. If CI
  fails, work only on repairing that same slice, rerun every affected local
  gate, push the repair as a new commit, and verify the replacement SHA.
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

## GitHub gate

Do not infer remote success from a local build or from a workflow attached to
another commit. After pushing:

1. Record `git rev-parse HEAD`.
2. Locate the GitHub Actions run whose `headSha` is exactly that value.
3. Wait for it to finish and require conclusion `success`.
4. Confirm the worktree is clean before starting the next proof slice.

If CI fails, repair the same slice, rerun every affected local gate, push the
repair, and verify the new exact commit. Never stack a new mathematical slice
on an unverified commit.

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
