# Arithmetic cancellation through the complete Suzuki chain

The repository's proved Gaussian Möbius cancellation now feeds into the
actual Chebyshev function, the original weighted prime-power mass, and the
complete Suzuki work. Lean proves

```text
psi(x)/x -> 1,
M(x)/sqrt(x) -> 2,
sum_{j<count} |I_j| / sqrt(count+2) -> 0,
G_count / sqrt(count+2) -> 0.
```

Here `I_j` and `G_count` are the unchanged canonical-center work and gap.
All prime powers and both finite-prefix endpoints are retained. These are
unconditional arithmetic estimates. **The independent logarithmic signed
lower bound remains open. No new zero exclusion or RH proof follows.**

## The finite Möbius transfer

`ChebyshevMoebiusCancellation.lean` retains the exact convolution

```text
F(q) = sum_{1<=m<=q} log(m),
psi(N) = sum_{1<=d<=N} mu(d)*F(floor(N/d)).
```

For `y=N/d`, the normalized remainder is
`R(N,d)=F(floor(y))/y-log(y)+1`. Integral comparison proves
`|R(N,d)|<=2/sqrt(y)`, including the floor error. The entire correction
`C_N=sum mu(d)*R(N,d)/d` is then split at `D=floor(N/Q)`.

The complete low-divisor part costs at most `4/sqrt(Q)`. On the remaining
interval, signed summation by parts preserves every quotient jump. If the
actual ordinary prefixes have magnitude at most `e*N` and the harmonic
prefixes have magnitude at most `e`, the whole complementary part costs
at most `2*e*(F(Q)+log(Q)+1)`.

For each fixed `Q`, both prefix hypotheses follow from the existing
ordinary and harmonic Möbius cancellation theorems. Taking `Q` large and
then `N` large proves `C_N->0`. The exact normalization identity is

```text
psi(N)/N = pairedEtaMoebiusLogHarmonic(N)*log(N)
           - moebiusHarmonicPrefix(N) + C_N.
```

The first term already tends to one, so the integer Chebyshev limit follows.
The real-cutoff theorem also proves and uses `floor(x)/x->1`. This supplies
the classical prime-number-theorem conclusion from the repo's existing
proofs; no claim of mathematical novelty is made for that conclusion.

## Transport into the original arithmetic work

`SuzukiArithmeticCancellation.lean` first turns the real Chebyshev limit
into a complete envelope: for every `e>0`, some finite `C>=0` satisfies
`|psi(x)-x|<=e*x+C` for every `x>=1`. The original Abel mass formula gives

```text
|M(x)-(2*sqrt(x)-1)| <= 2*e*sqrt(x)+C.
```

All integrals in this transfer are proved integrable. The finite constant
and the lower endpoint are included. Consequently the mass error divided
by `sqrt(x)` tends to zero.

The old mass at cell `j` ends at `j+2`, whereas the new event is at `j+3`.
The exact mass update and the bound on that intervening atom handle this
index difference. The actual corrected mass ratio

```text
q_j = (M_j-c)/(2*sqrt(j+3))
```

tends to one. The original mass-log work is exactly
`L_j=-2*a_j*log(q_j)`. For every `e>0`, Lean obtains one finite `C` with
`sum_{j<count}|L_j|<=e*M_count+C`. The mass upper bound then proves its
complete absolute sum is `o(sqrt(count+2))`.

Finally, the already proved summable Lerch correction transfers that
estimate to `sum |I_j|`. The exact gap recurrence includes the summable
transport costs and the initial gap, giving the stated gap limit as well.
No convergence of the unnormalized work or gap is asserted.

## Remaining strength gap

The earlier uniform estimates were `O(sqrt(N))`; the complete arithmetic
work now satisfies `o(sqrt(N))`. This is smaller than every fixed positive
multiple of `sqrt(N)` eventually. It does **not** imply a fixed power saving,
a logarithmic bound, nonnegativity, or a bounded total work.

The sufficient target remains an eventual signed lower bound
`W_prime(N)>=-(B+D*log(N))`, with finite constants and `D>=0`. Controlling
the signed accumulation more sharply is still required. No unresolved
estimate is introduced as an axiom or hidden in the new limit theorems.

Key declarations:

- `moebiusFactorialCorrection_tendsto_zero`
- `chebyshevPsi_div_tendsto_one`
- `suzukiWeightedMassError_div_sqrt_tendsto_zero`
- `suzukiFirstTailCorrectedMassRatio_tendsto_one`
- `suzukiSignedWork_absolute_sum_div_sqrt_tendsto_zero`
- `suzukiSignedWork_sum_div_sqrt_tendsto_zero`
- `suzukiCanonicalGap_div_sqrt_tendsto_zero`

Both modules are imported by the root library. Validation is local under
the standing instruction to hold commits.
