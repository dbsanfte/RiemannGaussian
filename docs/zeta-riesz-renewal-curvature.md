# The joined count coefficient at a minimum boundary

The literal target remains open:

\[
u^{N+1}\left(\mathrm{lowerThresholdPacket}_{3..55}
             -\mathrm{shortOverflowPacket}_{3..13}\right).
\]

This pass resolves a smaller question: **does the unit selected-mode background
annihilate the two-marked-leg cutoff difference when all its prime counts
are summed?** The finite lattice model has a strictly positive coefficient in an
interior chamber.
This is neither a net prime-sum bound nor a proof that the entire modal
response grows. The actual favorable five-prime supply proved earlier
and every earlier negative audit remain unchanged.

## The checked finite recurrence

[`ZetaRieszRenewalCurvature`](../RiemannGaussian/ZetaRieszRenewalCurvature.lean)
defines a positive cumulative sequence `D`, signed coefficients `a`, and
positive rough coefficients `b`, with all three empty coefficients equal
to one. For an integer cutoff `ell>=1`,

\[
nD_n=\sum_{\max(0,n+1-\ell)\le j<n}D_j,
\qquad a_n=D_n-D_{n-1}\quad(n>0).
\]

Lean proves the exact reduction

\[
na_n=-\mathbf1_{n\ge\ell}D_{n-\ell}.
\]

Consequently `a_n<=0` for every positive degree and `a_n<0` for
`n>=ell>=2`. The file also proves the Euler recurrence for `a`, its
uniqueness, positivity of `b`, and `b_n>=1/n` for `n>=ell`. These are the
recurrences for

\[
A(X)=\exp\!\left(-\sum_{j\ge\ell}\frac{X^j}{j}\right),\qquad
B(X)=A(X)^{-1},\qquad D(X)=\frac{A(X)}{1-X}.
\]

The Lean statements concern the recurrences directly. The optional probe
independently verifies their equality to the count-by-count exponential
convolution using exact rational arithmetic on the reported finite grid;
it is not a formal power-series identification theorem in Lean.

Define the finite inverse ramp convolution, including both empty atoms,

\[
F_\ell(S,d)=-\sum_{j=0}^{S}a_{S-j}b_j(d-j)_+.
\]

Its second cutoff difference is exactly

\[
F_\ell(S,d)-2F_\ell(S,d-r)+F_\ell(S,d-2r)
=-\sum_{j=0}^{S}a_{S-j}b_j\mathcal T_r(d-j),
\]

where `T_r(t)=t_+-2(t-r)_++(t-2r)_+` is the existing two-prime tent.
When `d<S`, the `j=S` atom vanishes by support. Every other term is
nonnegative. If some `ell<=j<=S-ell` satisfies `0<d-j<2r`, the sum is
strictly positive. Both statements are proved without an absolute-value
estimate of the original count sum.

`upper_face_lattice_strict` instantiates `ell=20`, `S=185`, `d=143/2`,
`r=20`, `j=60`. The exact rational probe gives about `5.7133451e-6`.
There are at most nine background atoms of size at least 20; with the
owner and two marked legs this fits inside total count 13. At the matching
lower face (`ell=5`, `S=215`, same `d`) its value is about `6.30436e-56`;
the rational comparison is negative after subtracting the upper face.
That comparison is a probe result, not the integrated factorial ledger.

## Why Dickman and Buchstab appear

For unit continuum cutoff let

\[
A(w)=e^{-E_1(w)},\qquad B(w)=e^{E_1(w)}.
\]

The ordinary densities, apart from their unit atoms, are
`a(v)=-rho(v-1)/v` and `b(v)=omega(v)`. Here `rho` is the Dickman
function and `omega` the Buchstab function. Their classical renewal and
Laplace identities are described in
[Lagarias, Sections 3.5–3.6](https://arxiv.org/abs/1303.1856).
This identification is used to analyze the model, not as a theorem
transporting an arithmetic prime measure to a density.

On `0<d<s`, the complete selected-background ramp is

\[
F(s,d)=\frac{d\rho(s-1)}s+
\int_{\max(1,s-d)}^{s-1}
 (v-(s-d))\frac{\rho(v-1)}v\omega(s-v)\,dv.
\]

The first term retains the empty `B` atom. The empty `A` atom is zero
because `d<s`. Taking the second unit difference gives the positive formula

\[
\frac{\rho(s-1)}s\mathcal T_1(d)+
\int_0^2\mathcal T_1(t)
 \frac{\rho(s-d+t-1)}{s-d+t}\omega(d-t)\,dt.
\]

For owner share `p`, two marked least-share legs `r`, and
`lambda=L/T`, substitute `s=(1-p)/r-2`, `d=(lambda-p)/r`.
The sign follows the repository's **positive** saturated coefficient
normalization and the owner's negative selected-mode phase. The probe
checks the triangle integral against three separately evaluated ramps.

## Quantitative diagnostic and its limits

The optional [probe](../scripts/probe_riesz_renewal_curvature.py) and
[report](riesz-renewal-curvature-probe.json) include:

- exact rational count convolution and both coefficient atoms;
- 140/180-digit construction of the renewal functions, with Taylor
  degrees 300/400 and 32/64-point quadrature refinement;
- lattice refinement through cutoff-grid size 1280;
- an explicit count-cap check at every sampled geometry.

At `u=10001/20000`, the **asymptotic fixed ratio**
`lambda=-2u log u`, and owner shares `0.525,0.55,0.575`, the second
difference is about `2.598e-48` at `r=0.01` and `8.78e-6..8.88e-6`
at `r=0.04`. These are not finite-`N` evaluations of `L_N/T`; no radial
integration is claimed in this probe. The lower and upper faces enter
with opposite signs. Quadrature refinements are not certified enclosures.

For a pair of conjugate synthetic modes with horizontal gain
`delta=1/40000`, the candidate minimum-corner radial rate is
`log(u/(u-2*delta*r))`: about `1.00e-6` and `4.00e-6`, respectively.
Higher marked-leg contributions already show why this distinction matters.
At `p=0.55`, `r=0.04`, `lambda=0.693`, the corresponding even differences
for 2, 4, 6, 8 and 10 marked legs are approximately
`8.807e-6`, `0.0017915`, `0.0459531`, `-1.49240` and `-19.2`.
`tenth_difference_one_background` proves the last value exactly `-96/5`
in Lean, using the existing finite Riesz kernel. The higher differences can therefore **oppose** the paired
term after the upper-face subtraction. The empty-background coalescence
is another separate contribution; it is not removed as an error.

A nonzero positive pair coefficient rules out annihilation of that
coefficient alone, but **does not prove a surviving asymptotic residue**.
Other assignments, corners, both finite beta faces, the moving length,
and the radial window must still be summed together.

The marked-pair calculation can be viewed as a coefficient in auxiliary
mode multiplicities. Do not apply the finite negative-mode support theorem
to noninteger multiplicities introduced by differentiating those parameters;
that theorem uses integer multiplicities. Nor does this diagnostic describe
actual zeta zeros or actual prime populations.

The next required test is the full joint coefficient with all modal
assignments and both factorial faces. Only after that can one claim a
modal obstruction or an estimate useful for the literal prime sum. There
is still no independent floor for the full retained sum or its complementary
carrier, and no zero exclusion follows from this slice.
