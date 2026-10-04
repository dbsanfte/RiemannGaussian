# Gaussian multiplicity payment for the current ceiling

The current ceiling is now proved for exposed candidate zeros through
`log(abs(Im rho)+2) <= 50000`. The **all-height 1.68 ceiling remains open**.
This is a genuine payment of a height range using actual arithmetic, rather
than another positivity test of a continuous prime model.

`ZetaRieszCeilingGaussianMultiplicity.multiple_zero_re_lt` proves, with no
exposure or simplicity assumption, that every actual nontrivial zeta zero
of analytic multiplicity at least two in that height range satisfies

$$
\Re\rho < \frac{19999}{20000}.
$$

Simple zeros are not excluded. This is a multiplicity-dependent restriction,
not an all-zero-free strip, an RH result or a claim of historical priority.
The existing signed-pole proof covers the heights below the Gaussian
starting height `10^6`; the new complete Gaussian estimate covers the rest.

The full Gaussian budget already retains the selected analytic multiplicity.
At dilation `q=9/100`, the candidate strip has worst normalized damping
`1013/500`. Integrating the exponential tangent at `t=1/5`, instead of at
zero, gives the kernel-checked enclosure

$$
G_4(1013/500) \ge \frac{461567}{1875000}.
$$

Exact Gaussian homogeneity gives a physical source of at least
`12462309/1250 = 9969.8472`. With multiplicity at least two, the exact
contact-family coefficient `a_1 >= 79/250`, the cotangent cost at most five,
and the nonnegative Poisson reserve retained, the selected source is at least

$$
\frac{984028661}{156250}=6297.7834304.
$$

The already-proved **complete** budget is bounded by

$$
36922\frac9{100}+\frac L{35}+57\log L+840.
$$

For `1 <= L <= 50000`, Lean proves `log L <= 11`, so this is at most
`2176493/350`. The remaining strict rational margin is
`43330001/546875`, approximately `79.2320`, **in Gaussian detector units**.
It is not a fraction of progress on the Riesz source gap.

`eventually_joinedPhysical_ceiling_in_height_range` transfers this independent
multiplicity restriction to the unchanged source-equivalent carrier:

$$
\Re\bigl(u^{N_j+1}\operatorname{joinedPhysical}(u,\Im\rho,N_j,K_j)\bigr)
<\frac{42}{25}
$$

eventually, under the original exposure and radius hypotheses and the stated
height restriction. Exposure is used only in the existing exact source
transfer. No literal mask, moving length, factorial order, prime count,
diagonal, allocation or phase has been changed. The theorem does not give an
unconditional carrier bound at arbitrary ordinates; it supplies the required
ceiling on the exposed-zero endgame in the independently paid range.

The earlier common-phase radius payment covered logarithmic heights through
1800, already excluded by the previous zero-free region. This slice increases
the checked ceiling's height coverage to 50000 by retaining multiplicity in
another existing arithmetic inequality. It does **not** close the ceiling
above 50000 or the independent simple-zero floor. The current source,
threshold, positive results and all no-go audits stay unchanged.

The focused leaf, namespace and transitive-axiom check is
`scripts/CheckRieszCeilingGaussianMultiplicity.lean`. The optional scalar
probe independently replays the exact fractions and Gaussian integral; it
samples no primes or zeta zeros and certifies no carrier entry order.
Everything remains local and outside the ordinary build/CI root.
