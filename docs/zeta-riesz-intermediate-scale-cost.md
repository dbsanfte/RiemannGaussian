# Intermediate prime scales in the signed population cost

The independent whole `-79/1000` floor, `3/2` ceiling, restricted
contradiction and new zero exclusion remain open. This slice extends the
previous total-log population bound to retain intermediate-scale primes.
It bounds the assembled signed periods and their literal ownership clips
for a growing population; it does not bound every absolute matching cost
or the unrestricted remainder.

## What is now covered

For a finite cofactor-prime universe `U`, let

```
E = {p in U : B < log p < J/W}.
```

These are exactly the primes excluded by the earlier head/shell spectrum.
`exact_gap_complement` proves the remaining spectrum condition for `U\E`.
The primes in `E` stay in the actual squarefree cofactor. Their phase,
both hinges, original factorial kernel and unique-owner allocation stay
unchanged. A positive marker is used only to price the population AFTER
the complete signed owner-prime period has been summed.

`intermediate_population_mass_le` proves, for every selected squarefree
population `D` with prime support in `U` and at most `m` factors in `E`,

```
sum_{a in D} 4^omega(a)/a
  <= t^m * exp(4 M_(U\E) + 4 M_E/t),       t >= 1,
M_E = sum_{p in E} 1/p.
```

The proof keeps exact squarefree symmetry; there is no fixed total count
ceiling. The intermediate-count condition is inherited by divisors,
which is needed when the literal ownership boundary deletes its two
near-tied largest primes. No coefficient class or small cofactor prime
is discarded.

The complete signed owner period costs `123136` times this population
mass divided by its radial center `v`. The original ownership clips cost
`98304` in the same units. Both missed sign selections spend ONE original
boundary atom. `sparse_intermediate_period_floor` joins them with the
single constant `221440`, retaining the original varying allocation.
Despite its name, this theorem accepts the general marked budget without
an extra small reciprocal-mass assumption.

## One cost across counts, owner scales and radial periods

Set

```
B = W = 32 log(N+1),
t = 16,
m <= floor(log(N+1)/4),
N+2 <= v <= 4(N+1).
```

The leading-one reciprocal-prime estimate is applied to the actual finite
prime universe. `quarter_count_marker_bound` gives

```
16^m exp(M_E/4)/(N+1)
  <= intermediateHeadFactor * exp(-log(N+1)/20).
```

The arithmetic head is a fixed positive, finite, UNEVALUATED constant.
`intermediateCountCeiling_tendsto` proves that the permitted number of
intermediate factors tends to infinity.

`global_quarter_count_floor` is the literal signed inequality over every
selected cofactor count, dyadic owner scale and radial period, including
both missed ownership selections. Its single total cost is

```
quarterCountSupplyPrice(N) * sum_v amplitude(N,v)/v,

quarterCountSupplyPrice(N)
 = 221440 * gappedHeadCost * intermediateHeadFactor
   * (32 log(N+1))^8 * (1 + log(4(N+1))/log 2)
   * exp(-log(N+1)/20).
```

Lean proves `tendsto_quarterCountSupplyPrice` and its eventual comparison
with any positive constant. The relative rate is
`O(log^9(N)/N^(1/20))`. The ACTUAL supply unit is

```
amplitude(N,v)/v = exp(-v/2) * v^N/N!.
```

No radial power is omitted. These are population costs after signed
prime-period cancellation, not generic Abel/PNT or absolute Fourier
allowances. In particular, a vanishing relative supply price is NOT an
absolute source-scale `o(1)` estimate. `quarter_cost_paid_by_reserve`
requires a genuinely disjoint existing reserve in these same units; it
does not create a fresh credit or make an old credit available twice.

## The remaining dense population

This covers the earlier one-intermediate-prime clustered example and a
growing family of such examples. It does not cover cofactors with more
than `floor(log(N+1)/4)` intermediate factors, or incomplete original
physical prime fibres. The whole original fibre/mask cover and compatibility
with prior supply credits remain explicit obligations.

The positive budget cannot simply be extended indefinitely:

* `dense_marker_price_lower` shows that at `m >= log(N+1)` the fixed
  marker-16 price already grows linearly, before owner-scale multiplicity.
* `dense_every_marker_budget_lower` rules out rescuing that dense budget
  just by retuning its marker. If `m >= log x` and the ACTUAL
  intermediate reciprocal mass satisfies `M_E >= log x/2`, then for every
  `t >= 1`,
  `t^m exp(4 M_E/t) >= exp(3 log x/2)`.
  `dense_every_marker_price_lower` consequently gives a price at least
  proportional to `sqrt(N+1)` in the actual radial-supply units.

The mass lower bound in the second audit is explicit; it is not assumed
for every masked universe. These are obstructions to the positive
allowance, not lower bounds for the signed carrier or impossibility
theorems for further cancellation. The remaining dense layers need
additional signed cancellation or a sharper population bound. The
subsequent [dense-shell cost](zeta-riesz-dense-shell-cost.md) now covers
ANY number of intermediate factors occupying at most
`floor(log(N+1)/16)` dyadic log bins, with all possible locations paid.
The [separated-parity floor](zeta-riesz-separated-parity-floor.md) gives
a different count-free signed estimate for widely spread, nonoverlapping
divisor windows. Diffuse overlapping windows remain open.

The current `polynomialCentralRemaining` and its source ledger are
unchanged. There is still no numerical whole-floor theorem.

## Optional diagnostics and checks

`scripts/probe_riesz_intermediate_scale_cost.py` checks the marked Euler
bound by enumerating actual small-prime squarefree populations, explores
the marker/count tradeoff, and checks the correct radial-price units.
The allowance model has a critical count coefficient near `0.27081`;
Lean uses the simpler `1/4` and proves its explicit `1/20` exponent.
Those model values are not signed-carrier asymptotics or a certificate.

The clustered large-log examples use equal-share continuous models with
exact binomial multiplicities. Prime existence, distinctness and physical
masks are not certified. They include dense examples outside the new
range whose active based blocks still have only one parity. No effective
starting order or evaluated arithmetic head is claimed. The probe is
optional and outside ordinary builds and CI.

Focused warning-as-error direct/build, ordinary-root-plus-explicit-module
namespace lint and all public transitive axiom checks are recorded in
[riesz-intermediate-scale-cost-audit.json](riesz-intermediate-scale-cost-audit.json).
No historical novelty claim is made for finite Euler markers or factorial
population tilting.
