# Actual macro-Fermat arithmetic bridge

New owned module: `RiemannGaussian/SemiprimeMacroFermatNetwork.lean`.

Theorems directly establish the arithmetic used by the frozen `factor_network.py` compiler:

- `root_four_half_period`, `root_four_cancellation`, `root_four_delta`, `macro_length_unit`: length `n=2^(d+1)`, ring `ZMod(2^n+1)`, principal root **4**, reflected zero frequency, and invertible normalization. No primality hypothesis.
- `macro_phase`, `macroFourier_eq_fourier`: exact two-stage Cooley–Tukey reindexing `j=j1+r*j2`, `k=k2+t*k1`, first-stage root `w^r`, twiddle `w^(j1*k2)`, second-stage root `w^t`, using only the proved full-period identity.
- `convolution_evaluation`, `fourier_convolution`: finite ordinary convolution and point-product identity, derived from sums, not assumed as a graph-validity premise.
- `fourier_reflection`, `inverse_convolution_unique`: actual normalized inverse recovers convolution uniquely over the composite ring.
- `convolution_bound`, `compiler_no_wrap`, `canonical_inverse_convolution`: each convolution coefficient is at most `digits*radix^2`; the compiler’s sufficient quarter-radix assumptions `digits<=bits`, `3*bits<=n`, `radix=2^bits` imply coefficient `<2^n+1`; canonical representatives therefore recover integers, not just congruences.
- `compiler_quarter_strict_bound`, `compiler_carry_capacity`: for the actual `n=4*bits`, positive bits and `digits<=bits`, coefficients and carries are strictly below `2^n`, meeting the physical carry-word capacity rather than merely the Fermat-modulus bound.
- `carry_telescope`, `integer_carries_exist`, `integer_carries_unique`, `integer_carry_bound`: actual integer carry equations are sound, exist from equal digit evaluations, unique from the initial carry, and bounded by the coefficient bound for radix at least two.
- `arithmetic_network_iff`: canonical inverse + integer carry vertices exist **iff** the actual digit sums multiply to the target digit sum. The no-wrap and digit-range premises are explicit and checkable, not a convolution-correctness premise.
- `arithmetic_network_unique`: all inverse output coefficients and internal carries are uniquely determined on the finite network range. Forward and point-product stages are explicit deterministic expressions.

## Scope retained

This is a complete arithmetic-stage bridge, not yet a Lean compiler theorem for the Python Boolean bit-edge graph. A future compiler bridge must connect canonical bit words/local port predicates and subdivision wiring to `ArithmeticNetworkValid`, discharge the public parameter-selection arithmetic (`n^2>=16L`, `bits=n/4`, `digits=ceil(L/bits)`), enforce nontrivial input factors, and link the target digit sum to the input integer. It must also carry the physical graph/wire cost proof. None of those interfaces is silently assumed proved here. No tensor-contraction theorem, D.1, or complexity consequence is asserted by this module.

## Verification

Standalone strict compilation and an audit importing both `RiemannGaussian` and the new leaf module are run with `-DwarningAsError=true`. `CheckMacro.lean` applies all 15 scoped linters and checks every generated declaration for custom/transitive axioms; only `propext`, `Classical.choice`, `Quot.sound` are allowed. Output: `macro-audit.txt`. No existing repository module, packet, journal, or AGENTS file was changed. The external full build was not restarted.
