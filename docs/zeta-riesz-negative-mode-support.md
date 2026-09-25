# Finite negative-mode support and the infinite-divisor domination obstruction

This local continuation starts from `cb88975fd7a80dbe58eaf08c7d2f1718c6d21a8b`.
It preserves the shifted-center leg theorems, every existing packet/rest
ledger, the moving supported-insertion bound, and all previous negative audits.
No factorial allocation is deleted, including orders zero and one.

The subsequent [finite-local-divisor audit](zeta-riesz-local-analytic-audit.md)
avoids the infinite inverse, proves the local xi decomposition, and tests
the remaining analytic factor. It preserves both results proved here.

**The finite support test passes. The proposed fixed-primitive, dominated
passage to the complete xi count response fails.** This is an obstruction
to that inverse-transform argument, not a counterexample to an arithmetic
packet bound, a zero exclusion, or RH. The literal moving-cutoff identification
is not proved in this slice.

## Finite inverse, with every diagonal derivative

[ZetaRieszNegativeModeSupport](../RiemannGaussian/ZetaRieszNegativeModeSupport.lean)
constructs an explicit weak inverse using iterated Bochner integrals on
positive rays and signed real derivatives of test functions. It does not
assume an inverse-Laplace identification or introduce a distribution axiom.

For a finite mode family A, the transform is exactly

$$
R_A(w,z)=\frac{1-\prod_{i\in A}(w-\xi_i)/(w+z-\xi_i)}{z^2}.
$$

Write J for integration on the positive d-ray and T_i for convolution on
the positive diagonal with weight exp(xi_i t). Expanding each factor as
1-z/(w+z-xi_i) gives the tested inverse of the r-fold primitive:

$$
J^{r+2}
-\sum_{B\subseteq A}(-1)^{|B|}
  \left(\prod_{i\in B}T_i\right)J^{r+2}\partial_d^{|B|}.
$$

The empty subset is retained. A distributional derivative acts on the
test with its exact sign. Thus terms that give diagonal deltas or their
derivatives are present; they have not been called negligible.

`inversePrimitive_laplace` evaluates this functional on
exp(-ws-zd) and obtains exactly R_A(w,z)/z^r, under the explicit convergence
conditions Re z>0 and Re(w+z-xi_i)>0. `inversePrimitive_support` proves
that the functional is zero for every test whose closed support lies in
d<s, for every r, including r=0. This is a weak support theorem for the
explicit inverse functional, not a new general distribution library.

`inversePrimitive_core_patch` applies the existing literal core gap
s-d>7/25. Tests supported within 7/100 in each coordinate of a core point
still miss the support cone. No phase replacement, norm comparison, or
individual lower-order condition enters this argument.

[ZetaRieszInfiniteModeAudit](../RiemannGaussian/ZetaRieszInfiniteModeAudit.lean)
then uses repeated actual-zero indices to retain every analytic
multiplicity. `finite_zero_core_support` applies to every finite genuine
zero window without simplicity, exposure, or a rightmost assumption.
`canonical_windows_core_limit` is identically zero on these restricted
tests. **This restricted limit does not identify a global inverse.**

## What fails in the infinite passage

The exact normalized count factor of the full xi logarithmic derivative is

$$
Q(s,z)=\frac{\xi(s)}{\xi(s+z)},\qquad
\partial_z Q(s,z)=-\frac{\xi'}{\xi}(s+z)Q(s,z),\qquad Q(s,0)=1.
$$

`hasDerivAt_xiFactor_global` identifies this ODE with the existing
multiplicity-weighted, absolutely summable Cauchy-difference expansion.
It explicitly keeps the constant log-derivative boundary channel. We do
not assert convergence of an unregularized infinite product.

For any fixed real v>1, set z_n=v+2n+1 and s_n=v-z_n=-2n-1. The functional
equation gives xi(s_n)=xi(2n+2). In the repository's normalization,
xi(s)=s(1-s) Gamma_R(s) zeta(s), and `xi_even_lower` proves

$$
\left|\xi(2n+2)\right|\ge\frac{n!}{\pi^{n+1}}.
$$

Consequently `xi_response_normal_growth` proves, for **every fixed** r,

$$
\left|\frac{1-\xi(v-z_n)/\xi(v)}{z_n^{r+2}}\right|
\longrightarrow+\infty.
$$

This is growth of the actual xi function, not a synthetic zero model.
No hypothesis about a zero to the right of the critical line is used.
It does not contradict inverse-square summability of each fixed leg
coefficient: exponentiating all counts and inverting is a stronger operation.

To see the precise domination obstruction, use cone coordinates s>=0,
d-s>=0. Any ordinary inverse primitive F with

$$
\int_{0\le s\le d}e^{-v s-b(d-s)}|F(s,d)|\,ds\,dd<\infty
$$

has a Laplace transform uniformly bounded along w=v-z, z>=b. Increasing
z only strengthens the damping of d-s. The normal base b is arbitrary:
this test permits the positive normal damping needed even by polynomially
growing ordinary primitives. `coneLaplace_norm_le` proves the bound.
`no_dominated_cone_primitive` combines it with the actual xi growth to
rule out matching the response on that normal ray for any fixed r and b.
`no_dominated_shifted_cone_primitive` retains the literal center
s0=3/2+i*y; it changes the tangential weight to v-3/2 and gives the same
obstruction.

The exact formal no-go is for an ordinary cone-supported primitive with
this weighted integrability and agreement with the xi transform on the
eventual normal ray. We have not proved a uniqueness/continuation theorem
for every possible generalized inverse, nor ruled out every distribution
or joint regularization. In particular, this is not a proof that a specific
actual-zero term survives below the diagonal. It shows that the suggested
fixed-order dominated inverse passage cannot be supplied by these data.

## Quantitative reproduction

The optional probe evaluates the actual xi response at v=2 using Gamma
and zeta at positive even arguments and the exact functional equation:

```sh
.lake/plot-venv/bin/python scripts/probe_riesz_xi_support.py \
  --output docs/riesz-xi-support-probe.json
```

For example, after 100 integrations, the base-10 logarithm of its norm is
approximately -154.97 at n=64, -89.90 at n=128, and +107.96 at n=256.
Small initial values therefore cannot establish convergence. The Lean
theorem proves eventual divergence for every fixed number of integrations;
the numerical report is illustrative and is not used by the proof or CI.
Here n indexes transform samples; it is not the Riesz packet order N.

## Stop point and remaining obligations

The pass stops at the requested infinite-divisor gate. The finite theorem
does cover all low-order diagonal channels, but a global inverse with the
required domination has not been obtained. The existing exp(-N/100)
bound remains a bound for the supported insertion process, not a bound
for the physical-cutoff packet.

No analytic-remainder/count exchange, multiplier-subset packet estimate,
broad packet, new packet/rest source ledger, or independent floor is
claimed. Any continuation through the complete zero divisor must first
address this count-transform growth, possibly by retaining the regular
completion term jointly; analyticity of its individual leg coefficients
alone is not such a joint bound. The old divergent restAllowance is not
reopened. The public RH, zero-free, and certificate frontiers are unchanged.

## Validation

Both new modules are imported by the ordinary root and assigned to the
shared arithmetic family. The warning-as-error root build, whole-project
declaration lint, and compiled-environment soundness audit pass. Explicit
axiom checks for the support, core, global-divisor ODE, growth, and
domination theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
The numerical probe is separate from the Lean proof and routine builds.
