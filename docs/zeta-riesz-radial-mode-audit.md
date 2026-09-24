# Radial audit of the masked-mode obstruction

Continuation from `6214417f635f8c4aa48af2d4f2ad37d314331408`.
The arithmetic packet, every finite mask, its rest ledger, the supported
insertion-tail estimates, and `LocalizedTypeIIBound` are unchanged.

**The radial window does not suppress the existing two-mode analytic
counterexample.** The all-count continuum probe also retains growing
resonance in its ordered modal sector. This is a negative test of the
proposed generic phase-transfer mechanism, not a theorem that the literal
`fullParityPacket` is unbounded. In particular, growth of one sector is
not asserted to prove growth after summing every assignment of both modes
to the same prime measure. No packet bound, revised rest limit, arithmetic
floor, or zero exclusion follows from this pass.

## Normalization: do not integrate the Gamma weight twice

Write

\[
u=\frac{10001}{20000},\quad a=\frac{20001}{40000},\quad
q_0=\frac{43}{80},\quad q_1=\frac9{16},\quad \gamma=\frac8{37}.
\]

The modes are exactly the existing `leftMode` and `rightMode`:

\[
z_1=a+i/10,\qquad z_2=a-43i/370,\qquad
z(q)=qz_1+(1-q)z_2=a+i\gamma(q-q_0).
\]

Both individual mode norms exceed `u`, but `z(q_0)=a<u`.
The old `band` integrates powers of `u/z(q)`. Those powers are already
complete factorial Laplace moments; `band` is not a fixed-total-log slice.
Putting the same powers inside another factorial radial integral would
apply the radial integration twice.

With the requested physical kernel, the appropriate mode density is

\[
e^{-T/2}\,e^{(1/2-z(q))T}=e^{-z(q)T}.
\]

Consequently the bare radial model tested here is

\[
B_N^{\rm win}=
\frac{u^{N+1}}{N!}\int_{1.95N}^{2.03N}
 T^N e^{-aT}\frac{1-e^{-iT/185}}{i\gamma T}\,dT.
\]

The elementary complete Laplace calculation gives, for `N>=1`,

\[
B_N^{\rm full}=\frac{u}{i\gamma N}
 \left[\left(\frac ua\right)^N-
       \left(\frac{u}{a+i/185}\right)^N\right].
\]

This is the existing `band (N-1)` with its order shifted by one.
Its leading exponential rate and radial saddle are

\[
g=\log\frac{20002}{20001}
  \simeq 4.9996250292\times10^{-5}>0,\qquad
\frac{T_*}{N}=\frac1a\simeq1.999900005.
\]

The saddle lies inside the prescribed window. The Gamma window-tail
rates `I_a(t)=at-1-log(at)` are approximately

| Boundary `t` | `I_a(t)` | Compared with `g` |
| --- | ---: | --- |
| `39/20` | `0.00031655923425` | larger |
| `203/100` | `0.00011213875621` | larger |

For example, positive exponential tilting bounds a radial tail by a
constant times
`[(u/b)*exp((b-a)*t)]^N`, taking `b=1/t`. Its log rate is exactly
`g-I_a(t)<0`. The complete-to-window error therefore decays in this bare
analytic calculation; removing the tails cannot remove its growing
endpoint. The imaginary part of the displayed window integrand has one
sign, since `1-cos(T/185)>=0`.

The new compiled results in
[`ZetaRieszParityMaskedPhaseAudit.lean`](../RiemannGaussian/ZetaRieszParityMaskedPhaseAudit.lean)
are deliberately narrower than a complete radial integral theorem:

- `radial_saddle_in_core` checks the exact saddle location;
- `radial_saddle_exponent` evaluates its exponent;
- `radial_growth_bounds` proves `1/21000 < g < 1/20000`;
- `radial_window_rate_margin` proves both displayed tail-rate comparisons;
- `no_uniform_negative_radial_exponent` rules out the proposed uniformly
  negative real exponent on the original radial/share box.

The complex Gamma integral identification and the window-tail integral
argument in this paragraph are analytic calculations, not new compiled
theorems. The existing `not_eventually_band_bounded` remains the checked
complete-response no-go theorem. A positive pointwise real exponent alone
would not prove growth of a general oscillatory integral.

## Moving-length, all-count numerical test

The optional
[`probe_riesz_radial_modes.py`](../scripts/probe_riesz_radial_modes.py)
computes the exact integer cutoff before taking a 192-bit logarithm:

\[
K_N=\left\lfloor\frac{20000^N}{10001^N(N+1)}\right\rfloor,
\qquad L_N=2\log(K_N+2),\qquad \lambda_N(T)=L_N/T.
\]

It integrates over the entire original radial window, without freezing
`T=2N`. In the ordered sector the largest prime carries `z1` and every
cofactor prime carries `z2`. Thus all the cofactor prime counts still
couple through the Riesz kernel, while their mode factor is
`exp(-z(q)*T)`. The model amplitude is

\[
A_N(T,q)=\frac{G_{r_-(T)}(1-q,\lambda_N(T)-q)
                    -G_{7/250}(1-q,\lambda_N(T)-q)}
                   {\lambda_N(T)q},\qquad
r_-(T)=\max\{3/250,2\log N/T\}.
\]

Here `G` is the candidate Dickman/Buchstab inverse already independently
tested in `probe_riesz_zero_parity.py`. Its full one-sided inverse
identification is not yet proved in Lean. The difference of cutoffs
selects the requested least-share interval; the count-one cofactor term
cancels. All admissible counts are included, rather than truncated at
10 or 11. At most 38 cofactor primes fit in the box, consistent with the
arithmetic count ceiling 39. The eventual literal count cutoff exceeds
this ceiling. The lower physical cutoff is included. The upper physical
cutoff and largest-prime ordering hold throughout these model evaluations.

The coefficient orientation is the plus sign in
`coefficient_saturated_prime`, combined with `(-1)^(k+1)` for the largest
prime and `k` cofactor primes. The simplex radial Jacobian cancels the
extra `T` in the homogeneous Riesz coefficient, leaving `1/(lambda*q)`
and the radial power `T^N` used above.

The script does **not** simulate actual primes, the original finite
`rectangleMass`, or the old allocation factor. Their independently proved
arithmetic error bounds remain intact; they are not silently treated as
theorems about this synthetic modal measure. This is an audit of the
remaining coefficient-box mechanism, not an evaluation of the literal
finite packet. The arbitrary requested probe orders also need not be
members of the repository's cofinal dyadic sequence.

The main output is
[`riesz-radial-modes-probe.json`](riesz-radial-modes-probe.json).
The decisive high orders were recomputed with twice the delay-equation
resolution and higher radial/share quadrature degrees in
[`riesz-radial-modes-refinement.json`](riesz-radial-modes-refinement.json).

| `N` | Source-normalized ordered all-count norm |
| ---: | ---: |
| 256 | `1.8646e-16` |
| 640 | `1.5064e-16` |
| 1536 | `6.5720e-16` |
| 4096 | `6.8666e-17` |
| 8192 | `6.3897e-17` |
| 131072 | `3.8442e-15` |
| 524288 | `3.26117e-7` |
| 700000 | `1.59412e-3` |
| 786432 | `1.06777e-1` |
| 1048576 | `3.93662e4` |

The refined last value is approximately `39366.16389`, versus
`39366.19079` on the preceding grid. The relative change is about
`6.8e-7`. Its **raw**, unnormalized log-base-10 norm is approximately
`315612.1880`. Raw values are recorded logarithmically to avoid overflow.
The full complex values and phases are retained in the JSON. The growth
is predominantly imaginary; these norms do not themselves disprove a
one-sided real floor.

At the resonant saddle the limiting model amplitude is approximately
`-3.0388446e-13`. The lower-cutoff contribution there is about `3.1950e-41`,
whereas the upper-cutoff contribution is about `3.0388e-13`. The all-count
cancellation is extremely strong but numerically does not make this
endpoint coefficient zero. Its small size delays visible growth to orders
far beyond the initial `256..8192` samples. The endpoint approximation has
the form

\[
\frac{u A_*}{i\gamma N}e^{gN},
\]

which explains the observed delayed growth. The endpoint amplitude and
this all-count asymptotic remain model diagnostics, not Lean-certified
constants or an asymptotic theorem for actual primes.

The numerical checks compare the Gamma quadrature mass with the exact
incomplete-Gamma window probability, refine the delay grid, and refine
both quadratures. Inner QAWO error reports exclude interpolation, delay
discretization, and floating-point errors; they are not rigorous total
error bars. This data is exploratory, not a certificate.

## Other assignments of the two modes

There is an exact useful separation of modal shares. If the largest prime
carries the left mode and any cofactor does too, the total left-mode
share is at least `q0+3/250`. If the largest prime carries the right mode,
all left-mode shares together are at most `1-q0=37/80<q0`.
`left_owner_extra_mode_separated` and `right_owner_mode_separated` now
check these inequalities and the resulting imaginary-pole separations.

Thus only the ordered sector above reaches the resonant endpoint
`q0`. This is spectral support information; by itself it does **not**
rule out cancellation of the final integrals. The moving Riesz weights
must still be controlled in any proof making that inference.

For orientation, the first mixed boundary is shifted by the cofactor
cutoff. Its complete radial rate is approximately `3.6534e-5` at
`r=3/250`, with model boundary amplitude `3.3051e-37`; at `r=7/250` the
rate is already negative, approximately `-2.3294e-5`. These are endpoint
diagnostics, not bounds for the whole complementary modal sector.

The optional `--mixture` mode also expands all assignments to the same
two-mode measure by FFT convolution. Low-order exploratory runs produced
very small residuals, but their inverse-convolution diagnostics were
much larger than those residuals. High-order same-mode oscillations also
require refinement of radial quadrature, not just the FFT grid. Those
runs are **excluded from the verdict**: no full-mixture growth or decay
claim is supported by them.

## Decision and unchanged obligations

Stop trying to justify the packet limit by separate complete-leg phases,
a tiny fixed continuum defect, and radial localization alone. The bare
analytic counterexample survives the actual radial window, and the
ordered all-count test supplies additional adverse evidence. Proving
decay for the actual prime measure would require new joint information
that excludes or cancels these correlated endpoint modes. The numerical
sector computation does not prove that such information is impossible.

The short optional positive-cutoff inverse task has not been closed:
one-sided support, the empty-cofactor term, and the auxiliary-cutoff limit
remain separate from the proved supported 12+ tail. No `O(1)` boundary
source has been established in this pass. None of those open obligations
is assumed away to obtain a packet estimate.

Keep the exact `coreResponse = fullParityPacket + fullParityRest` ledger.
Do not recompute the rest source using an unproved small-packet premise,
and do not reuse the already divergent `restAllowance` as a proposed
floor. No public RH or zero-free frontier changes here.

Local validation passed: warning-as-error module and full-project builds,
the declaration lint, the namespace lint, explicit axiom audits of all
seven new public theorems, and the compiled project soundness audit. The
new theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
The regenerated dashboard changes only inventory counts; no milestone or
frontier is advanced. Both numerical reports match the recorded source
hashes, and the high-order refinements agree to better than one part per
million. These numerical checks remain distinct from the Lean proofs.

Reproduction, outside ordinary builds and CI:

```bash
python -m venv .lake/riesz-probe-venv
.lake/riesz-probe-venv/bin/pip install -r scripts/requirements-riesz-probes.txt
.lake/riesz-probe-venv/bin/python scripts/probe_riesz_radial_modes.py \
  --steps 3200 --radial-degree 24 --share-degree 32 \
  --orders 256 640 1536 4096 8192 32768 131072 524288 700000 786432 1048576 \
  --output docs/riesz-radial-modes-probe.json
.lake/riesz-probe-venv/bin/python scripts/probe_riesz_radial_modes.py \
  --steps 6400 --radial-degree 32 --share-degree 48 \
  --orders 524288 700000 1048576 \
  --output docs/riesz-radial-modes-refinement.json
```
