# Finite divisor mass and the whole signed floor

This local slice removes the fixed auxiliary divisor-growth exponent from
the sparse phase-pair payment. It proves an additional independent payment
for the original carrier. The remaining signed energy, the floor and the
restricted zero exclusion are **open**.

`NatDivisorSquareHarmonic` expands both divisor incidences, sums the common
multiples with their exact lcm reciprocal, and applies the existing common-gcd
harmonic bound. For every finite masked population `S` in `[1,X]`, Lean proves

$$
\sum_{n\in S}\frac{\tau(n)^2}{n}
\le H_X^4\le(1+\log X)^4.
$$

The previous estimate used
`exp(log(X)/262144) * divisorSquareDirichletMass(1+1/262144)`.
The new bound has no exponential loss and no unevaluated infinite divisor mass.

`ZetaRieszFinitePhasePayment.logNear_pair_mass_bound` applies this to every
finite symmetric family of literal total-log phase neighborhoods. Its capacity
is at most `card(P) * (4*epsilon + exp(-l)) * (1+log(X))^4`, including the integer
endpoint error. No prime-density replacement or count orthogonality is used.

The new literal width is

$$
\delta_N(y)=\frac{e^{-N/4900}}{1+|y|},
$$

wider than `exp(-N/4500)/(1+abs(y))`. At the unchanged radius ceiling
`U=10001/20000`, the exact rational rate audit gives

$$
2\log(2U)-\frac1{4900}
\le-\frac1{245000}< -\frac1{250000}.
$$

For the actual source-normalized weights and an arbitrary additional pair
mask, `weighted_maskedEnergy_bound` proves

$$
|E_{\rm paid,N}|
\le C(B,y)(N+1)^8e^{-N/250000},\qquad
C(B,y)=20480U^2B^2\operatorname{phaseCount}(y).
$$

Its profile cost is at most
`sqrt(4*C(B,y)) * (N+1)^5 * exp(-N/500000)` and tends to zero for every fixed
height. The larger polynomial degree is explicit. This is an eventual theorem;
no numerical starting order or native mass fraction is certified.

The current signed energy is partitioned exactly, at the **same** actual
whole-population adverse cutoffs. Only pairs outside all previous payments
enter the new difference. The source-normalized original `joinedPhysical`
satisfies the checked whole-floor comparison

$$
\Re P_j\ge
-\sqrt{\max(E_{\rm remaining,j},0)\,129N_j/200}-e_j,
\qquad e_j\longrightarrow0.
$$

All original phase, allocation, squarefree, physical, count, owner and radial
masks remain. The remaining energy contains signed cross-count correlations;
it is not a sum of independent positive allowances. Removing a negative paid
term may increase that energy. No monotonicity claim is made.

The sufficient relaxed numerical target remains
`E_remaining <= 987/(100000*(N+1))` cofinally, giving floor `-399/5000-o(1)`
with the already checked strict source gap. **That estimate is not proved.**
The separate whole-carrier directional cost and its exact phase credit remain
available; no unproved credit size is added to this energy comparison.

The optional `probe_riesz_finite_phase_payment.py` checks rational rate margins
and the finite harmonic bound, then tests the new pair difference on complete
subsets of constructed prime universes. It retains the same adverse selection
and integer divisor steps. Probable primes, common amplitude rescaling and
log interpolation make its carrier results exploratory, not a full-core,
source-budget or cofinal certificate. It runs outside ordinary builds and CI.

The [scoped proof audit](riesz-finite-phase-payment-audit.json) records all
new public axioms, namespace lint, current-root checks, numerical scope and
the still-open joint arithmetic target. The
[joint credit floor](zeta-riesz-joint-credit-floor.md) retains the global
phase saving in this current signed-energy comparison.
