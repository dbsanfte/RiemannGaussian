# Prime separation in the full complex zeta kernel

`ZetaPrimeGram.lean` connects the repo's exact eta prime-base separation
theorem to the actual zeta logarithmic derivative. It proves a structural
property for arbitrary distinct complex probes, including a strict finite
arithmetic witness beyond every cutoff. The independent signed bound for
RH remains open.

## The arithmetic kernel and its full information

For a finite index set, choose distinct complex numbers `s_i` with
`Re(s_i)>1/2`, and arbitrary complex coefficients `c_i`. Define

\[
 K_{ij}=-\frac{\zeta'}\zeta(\overline{s_i}+s_j),
 \qquad f_i(n)=n^{-s_i}.
\]

The feature at `n=0` is defined by an exponential; it makes no contribution
because `Lambda(0)=0`. All positive-integer features are the literal complex
powers. `hasSum_zetaPrimeGram_entry` and
`hasSum_zetaPrimeGram_energy_complex` prove genuine convergence and

\[
 \boxed{c^*Kc=\sum_{n\ge1}\Lambda(n)
                 \left|\sum_i c_i n^{-s_i}\right|^2.}
\]

The entire complex identity is retained before taking its real part.
Different real parts, both phase channels, and every cross term remain.
There is no restriction to nonnegative coefficients, an integer frequency
lattice, a selected support, or a specific optimizer.

The domain is essential: each mixed argument has real part greater than
one. The threshold `Re(s_i)>1/2` here comes from adding two exponents in an
absolutely convergent Euler series. It is not a new zero-free region.

## A finite prime witness at every depth

The existing `exists_prime_etaGeometricDecayMode_injOn` theorem proves that
one prime separates any finite injective family of complex exponents.
`zetaPrimeFeature_eq_etaGeometricDecayMode` makes the connection exact.
The selected prime `p` depends only on the probes, not on their coefficients
or on the cutoff.

Put `d=cardinality({i})` and `z_i=p^{-s_i}`. The `z_i` are distinct and
nonzero. A Vandermonde argument proves that, for every nonzero `c` and
every natural `J`,

\[
 \left(\sum_i c_i z_i^{J+k}\right)_{0\le k<d}\ne0.
\]

This is `zetaPrimeFeature_block_nonzero`. It is exact at every finite
depth, rather than an eventual asymptotic assertion. Factoring out `z_i^J`
does not lose information because each factor is nonzero.

For any integer cutoff `N`, `J>=1`, and `p^J>N`, the terminal theorem
`exists_prime_zetaPrimeGram_strict_block_floor` gives

\[
 \boxed{0< (\log p)\sum_{k=0}^{d-1}
       \left|\sum_i c_i p^{-(J+k)s_i}\right|^2
 \le c^*Kc-
       \sum_{n\le N}\Lambda(n)\left|\sum_i c_i n^{-s_i}\right|^2.}
\]

The prefix and the prime-power block are proved disjoint. Every term's
weight is the actual von Mangoldt weight. No conjectural arithmetic
estimate or positive-definiteness assumption is used.

The displayed floor depends on the probes, coefficients, and depth.
Strict positivity is not a uniform lower bound of the magnitude needed
to beat a hypothetical zero's source term.

## What this tells us about phase counts

`zetaPrimeGram_posDef` proves that `K` is positive definite. More strongly,
`zetaPrimeGram_sub_prefix_posDef` proves that subtracting the complete
matrix of any finite prime prefix still leaves a positive definite matrix.
`zetaPrimeGram_sub_prefix_rank` proves its rank is exactly `d`.

Consequently this arithmetic kernel has no fixed finite rank: arbitrary
finite sets of distinct admissible probes give full-rank matrices, even
after any finite prime prefix has been removed. A phase polynomial's
contact zeros are therefore not exact null directions of this arithmetic
kernel. In particular, the previous optimizer's eight nonconstant
frequencies do not identify an intrinsic eight-dimensional zeta spectrum.
The earlier optimum remains a statement about its specified objective and
budget. This rank theorem does not assert that every objective improves
strictly whenever another frequency is added.

There is also a literal zeta inequality. For distinct `s,t` in the same
domain, `zetaPrimeGram_strict_cauchySchwarz` proves

\[
 \left|-\frac{\zeta'}\zeta(\bar s+t)\right|^2
 < \Re\!\left(-\frac{\zeta'}\zeta(2\Re s)\right)
   \Re\!\left(-\frac{\zeta'}\zeta(2\Re t)\right).
\]

Its vertical-line specialization,
`norm_neg_logDeriv_riemannZeta_lt_real_axis`, gives, for `sigma>1` and
`y!=0`,

\[
 \boxed{\left|\frac{\zeta'}\zeta(\sigma+iy)\right|
       <\Re\!\left(-\frac{\zeta'}\zeta(\sigma)\right).}
\]

Both the real and imaginary parts contribute to the modulus. No positive
gap uniform in all nonzero heights is asserted.

## Connection to the open RH estimate

This supplies a rigorous matrix for choosing coupled complex probes and a
finite test that rules out exact arithmetic cancellation across a complete
prime-power block. Future inverse-matrix or amplification arguments can
use proved strict positivity of the actual matrix, rather than a generic
matrix assumption.

The [signed Suzuki bridge](suzuki-phase-curvature-and-actual-cutoff.md)
still fixes the direction: positivity of prime work yields an upper
curvature bound. It does not establish the lower Suzuki signal estimate.
Nor does full rank provide an independent contraction or a useful uniform
conditioning bound as probes and cutoffs move.

The direct sufficient arithmetic target is still the unproved eventual
upper bound

\[
 \sum_{n\le N}\frac{\Lambda(n)}{\sqrt n}\log(N/n)
       \le 4\sqrt N+C+D\log N,
 \qquad D\ge0.
\]

The next useful estimate must control the signed difference between the
whole prime average and its continuous main term. It must use more than
positive rank or a strictly positive but unquantified finite-block floor.
Larger sub-source allowances remain worth investigating with a checked
transfer; the logarithmic allowance is one sufficient route.

## Mathematical provenance and validation

Dirichlet-series kernels with nonnegative coefficients belong to an
established framework; see
[McCarthy and Shalit, *Spaces of Dirichlet series with the complete Pick property*](https://arxiv.org/abs/1507.04162).
The additions here are the Lean connection to the repo's exact eta
separation machinery, the complete finite-cutoff witness, and the checked
zeta consequences. No claim of mathematical priority is made for these
formulations.

The module contains 21 public theorems. Direct elaboration with warnings
treated as errors, the focused build (4254 jobs), and the full root/default
build (9783 jobs) passed. Whole-project declaration lint and the verbose
module lint passed. All 21 public theorem axiom reports were checked and
contain only `propext`, `Classical.choice`, and `Quot.sound` transitively.
Source-integrity and whitespace checks passed.

No files were staged, committed, or pushed; no remote CI, README, or
generated-status update was performed. The global goal remains open.
