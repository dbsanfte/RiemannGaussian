# Prime replacements in the retained signed sum

Lean now gives the complete original finite Riesz carrier an explicit
absolute-mass bound **minus a nonnegative pair-saving budget**. Each
selected pair keeps the better of two proved estimates: a small integer
gap and the exact relative sine phase. The selected classes are disjoint
subsets of the original band. The full signed decomposition, including
the unmatched remainder, remains available.

This does not prove that the saving is positive at every order, large
enough at source scale, or sufficient for a zero-free region.

## What the window interactions retain

Write `d=g r`, `e=g s`, with `g=gcd(d,e)`. For squarefree divisor labels,
the complete Gram entry has Mobius sign `mu(r)mu(s)`, while its window
cutoff shifts from `L` to `L-log(g)`. Its original complex amplitude stays
at **L**. The reduced pair is coprime; common primes cannot be discarded
from the physical cutoff.

Within a fixed prime-pair family, proper divisor chains have exactly zero
overlap. A negative Mobius pair with nonzero overlap therefore requires
two coprime nonunits with at least three nonshared prime factors and a
logarithmic ratio smaller than the window width. Negative Mobius sign
alone does not imply a negative complex Gram contribution.

Across families sharing their first prime, a comparable interaction must
introduce a new prime between the two second-prime thresholds. The
[`actual_chain_overlap_requires_new_small_prime`](../RiemannGaussian/ZetaRieszCrossFamilyWindow.lean)
theorem discharges roughness and positivity from the original smallest-prime
factorizations. These restrictions do not cover all varying-first-prime
interactions and do not yet bound the remaining correlations.

## A quantitative cancellation across actual integers

Let `a,b,q` be primes, `a!=b`, none dividing the squarefree nonunit `n`.
For the original Riesz profile `R_L`, Lean proves the exact identity

```math
R_L(qn)+R_L(abn)-R_L(an)-R_L(bn)
 =R_{L-\log a-\log b}(n)-R_{L-\log q}(n).
```

Its absolute value is at most

```math
\left|\log q-\log(ab)\right|\sum_{d\mid n}|\mu(d)|,\qquad
\left|\log q-\log(ab)\right|\le\frac{|q-ab|}{\min(q,ab)}.
```

The two smaller profiles vanish when `log(an)<=L` and `log(bn)<=L`:
their complete Mobius mass and first moment cancel. These cutoff
conditions are checked in the definition of the selected cofactor class.

The actual band weights include `A_n=-log(n)/L` times the full complex
factorial filter. Their mismatch is not assumed small. The proof
differentiates the complete amplitude in logarithmic coordinates, keeps
both adjacent orders, and proves an explicit uniform allowance. The
[`norm_bandWeight_replacement_pair_le_integer_gap`](../RiemannGaussian/ZetaRieszPrimeReplacement.lean)
theorem bounds `|B(qn)+B(abn)|` by that complete allowance times
`|q-ab|/min(q,ab)`. Both integers must belong to the original band.

## Preserve the relative phase

At height `t`, the common cofactor cancels from the relative angle. The
[`norm_bandWeight_replacement_pair_le_phase`](../RiemannGaussian/ZetaRieszReplacementPhase.lean)
bound retains the exact chord

```math
2\left|\sin\!\left(\frac{t}{2}(\log(ab)-\log q)\right)\right|.
```

The smooth derivative allowance is evaluated on the real spectral line.
Thus this second estimate preserves full phase rotations instead of
replacing every phase difference by a monotone cost in height. The same
complete fixed polynomial is present throughout; no special coefficient
family, numerical optimizer or zero-location assumption is used.

## The whole carrier and the remaining obligation

`replacementCofactors` includes every cofactor satisfying the explicit
support, coprimality and saturation tests for the selected prime triple.
If `q!=a,b`, prime divisibility proves the two image families disjoint;
multiplication is injective within each image. Every selected original
integer is therefore spent exactly once. The triple is arbitrary and may
be selected separately at each order; no fixed schedule is imposed.

For each pair let `C_n` be the smaller of the two complete proved costs,
and set

```math
S_n=\max\{|B(qn)|+|B(abn)|-C_n,0\}.
```

[`norm_actual_band_le_mass_sub_saving`](../RiemannGaussian/ZetaRieszReplacementFamily.lean)
proves for the **whole original carrier**

```math
\left|\sum_{k\in\mathcal B_N}B(k)\right|
 \le\sum_{k\in\mathcal B_N}|B(k)|-\sum_n S_n.
```

`actual_band_eq_replacement_add_remainder` retains the exact complex
identity before this relaxation. The new bound cannot worsen the triangle
bound. No uniform positive lower bound for the saving sum is proved, and
this does not improve every previous whole-carrier bound. The unmatched
integers and interactions between different prime triples remain. A
source-scale estimate for the whole signed sum is still open.

Finite floating-point exploration suggested useful pair cancellation but
left substantial unmatched mass. It is not a certificate, an asymptotic
estimate, or evidence of a zero-free region. No numerical exploration is
run in ordinary CI. These identities carry no historical novelty claim.

The [centered-cofactor refinement](zeta-riesz-centered-cancellation.md)
halves the complete profile costs and combines all eligible prime-insertion
families through a disjoint matching, with the unmatched remainder retained.
