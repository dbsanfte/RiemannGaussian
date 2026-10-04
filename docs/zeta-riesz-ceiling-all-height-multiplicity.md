# All-height multiplicity payment for the current ceiling

The ceiling now has an independent arithmetic payment in an explicit layer
at **every height**. The full fixed-strip ceiling remains open.

Let `L = log(abs(Im rho)+2)`. The new kernel-checked theorem
`ZetaRieszCeilingAllHeightMultiplicity.simple_of_boundary_layer` proves that
every actual nontrivial zeta zero satisfying

$$
1-\Re\rho\le
w(L):=\min\left(\frac1{20000},\frac9{2(L+40000)}\right)
$$

has analytic multiplicity exactly one. The multiplicity theorem assumes
neither exposure nor simplicity. It excludes multiple zeros in this layer;
it **does not exclude simple zeros** and is not an all-zero-free strip.

The curve joins the preceding plateau exactly at `L=50000`. That earlier
proof, including its signed-pole low-height payment, handles all smaller
heights. The new adaptive estimate handles every greater height, with no
unknown starting threshold or upper-height restriction.

The proof uses the same complete Gaussian arithmetic inequality. For
`L>=50000`, set

$$
q=\frac{L+40000}{10^6},\qquad
\frac9{2(L+40000)}=\frac{81}{40}\operatorname{width}(q).
$$

Then `q>=9/100`, and the worst damping is exactly `1013/500`, already covered
by the checked nonzero-point exponential tangent. Gaussian homogeneity gives

$$
G_{\operatorname{gaussianScale}(q)}
 \bigl(\operatorname{width}(q)\,1013/500\bigr)
\ge\frac{2769402}{25}\,q.
$$

Keeping multiplicity at least two and the existing exact contact family,
paying the cotangent correction, and retaining the nonnegative Poisson
reserve gives selected source at least `70000*q-4`. The **complete** budget
is still at most

$$
36922q+\frac L{35}+57\log L+840.
$$

The global logarithmic tangent
`log L <= L/20000+9` is proved using `exp(10)>20000`; no logarithm is sampled
as part of the proof. Substitution leaves the rational surplus

$$
\frac{2899}{1750000}L-\frac{847}{25}
\ge\frac{8566}{175}>0.
$$

`complete_cost_margin` checks this for every `L>=50000`. The margin is in
Gaussian detector units; it is not a credit, missing error or percentage
of completion for the Riesz ceiling.

`old_simplicity_width_lt` proves, at every ordinate, that `w(L)` is strictly
more than `5/2` times the earlier Gaussian multiple-zero layer

$$
\frac{13}{6}\min\left(\frac1{450000},\frac{32}{45L}\right).
$$

The new width is asymptotic to `9/(2L)`, whereas that earlier layer is
asymptotic to `208/(135L)`. Their limiting width ratio is `1215/416`.
This compares two repository theorems; it asserts no literature record or
historical novelty. At very large heights another proved all-zero-free
region may contain portions of either layer.

`eventually_joinedPhysical_ceiling_in_boundary_layer` transfers the
independent simplicity theorem through the existing exposed-zero source:

$$
\Re\left(u^{N_j+1}\operatorname{joinedPhysical}
 (u,\Im\rho,N_j,K_j)\right)<\frac{42}{25}
$$

eventually whenever the original exposure/radius hypotheses and the new
layer condition hold. The carrier, phase, moving length, literal masks,
prime counts, allocations, every factorial order, swapped incidences and
single square diagonal are unchanged. This is a proved ceiling on that
exposed-source endgame, not an unconditional bound at arbitrary ordinates.

`unpaid_multiple_location` states the remaining gap explicitly. Any actual
multiple zero still in the original fixed candidate strip must satisfy

$$
L>50000,\qquad
\frac9{2(L+40000)}<1-\Re\rho\le\frac1{20000}.
$$

No estimate on that remaining region is supplied by this theorem. Closing
the fixed-strip ceiling still requires new arithmetic information there;
the independent simple-zero floor also remains open. This slice does not
prove the restricted RH contradiction or RH.

The optional focused check is
`scripts/CheckRieszCeilingAllHeightMultiplicity.lean`. The scalar replay is
`scripts/probe_riesz_ceiling_all_height_multiplicity.py`; it checks exact
fractions and independently quadratures the Gaussian, and samples no
primes, zeta zeros or carrier arrays. It certifies no native entry order.
The scoped proof and artifact pins are in
`riesz-ceiling-all-height-multiplicity-audit.json`. Everything remains local,
without root registration, commits, pushes, subagents or wider gates.
