# Closing the logarithmic allowance in the Suzuki chain

`SuzukiLogarithmicWork.lean` proves that an eventual logarithmic lower
bound on ordinary-prime signed work suffices for Mathlib's RH. The
[independent proper-prime-power bound](suzuki-proper-prime-power-work.md)
is now included in the complete implication. **The ordinary-prime
arithmetic inequality remains open; this is a conditional RH theorem.**

The earlier constant-floor criterion could not directly absorb the
`90+45*log(N)` allowance left by separating proper prime powers. The new
proof supplies the missing analytic connection:

1. A logarithmic floor for cumulative full work gives such a floor for
   its canonical gaps, since the complete nonlinear transport cost is
   already summable.
2. At each positive tail time `t`, select the actual active event prefix.
   Its endpoint satisfies `log(N)<=t`. The canonical gap is a lower bound
   for that frozen cell, and the frozen model equals the literal Suzuki
   function there. Thus a floor `-(C+D*log(N))` gives an affine time floor
   `-(C+D*t)`. The reset cell and the prime-free initial interval are
   handled separately. No bound for inactive future prefixes is used.
3. Add `C+D*t` to the literal logarithmic-average signal. This positive
   compensator has a genuinely convergent Laplace transform for every
   positive damping; exponential moment integrability is proved directly.
   The compensated positive measure agrees with the original transform
   plus that compensator on the safe half-plane.
4. The existing eta exclusion of real zeros supplies analyticity along
   the positive real axis. Positive-Laplace Landau continuation therefore
   gives true convergence for the compensated signal at every positive
   damping. Subtract the compensator's actual holomorphic transform and
   invoke the original xi-denominator and positive-multiplicity
   contradiction.

The proof uses the compensator's actual complex moment-generating integral.
It does not treat formal continuation as convergence of the original
integral. It also does not introduce a zero-free-strip or integrability
hypothesis beyond the explicit arithmetic floor.

Writing `W_prime(N)` for the unchanged work selected at ordinary-prime
new atoms, the resulting sufficient target is

```text
there exist finite B and D>=0 such that, eventually,
W_prime(N) >= -(B+D*log(N)).
```

Indeed, the checked proper-prime-power bound transfers this to
`W(N)>=-((B+90)+(D+45)*log(N))`. The new analytic argument absorbs that
entire allowance. A finite initial prefix changes only the constant.
A fixed constant floor is a special case, and the finite mass-log work
may replace the canonical-center work using its proved positive Lerch
correction. Every preceding prime power remains inside each old prefix
mass and canonical center; no primes-only recentering is performed.

Conversely, every hypothetical right-half zero forces `W_prime(N)` below
every prescribed logarithmic floor at arbitrarily late cutoffs. This is a
checked consequence of the conditional theorem, not an exclusion of such
a zero or a proof of the required arithmetic bound.

Key compiled declarations:

- `riemannHypothesis_of_suzuki_signal_affine_lower_bound`
- `suzukiPsi_lower_bound_of_canonical_gap_log_lower_bound`
- `riemannHypothesis_of_suzuki_signed_work_eventually_log_lower_bound`
- `riemannHypothesis_of_suzuki_ordinaryPrime_work_eventually_log_lower_bound`
- `riemannHypothesis_of_suzuki_ordinaryPrime_massLog_eventually_log_lower_bound`
- `suzuki_ordinaryPrime_work_frequently_below_log_of_right_half_zero`

Both new modules are imported by the root library and are validated locally
with warnings as errors, declaration lint and transitive axiom checks.
The changes remain uncommitted under the user's instruction.
