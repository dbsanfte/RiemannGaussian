# The smallest remaining contradiction target

The user requested this reassessment on 2026-09-09 before further investment
in prime-pair decompositions. The global goal remains open. This document
compares existing checked statements and proposes a research priority; it
does not prove a new arithmetic bound, exclude another zero, or claim a
new RH criterion as mathematical progress.

## What can actually be weakened

Ruling out every nontrivial zero with real part greater than one half,
together with the proved reflection symmetry, proves RH. A shorter proof
may exist, and a sufficient estimate may be much weaker quantitatively
than the estimates we have been pursuing. Neither observation establishes
that its remaining open direction is easier to prove.

There are two distinct choices:

1. Keep the full goal, but ask for the least arithmetic control needed
   by the existing contradiction.
2. Prove an exclusion for a restricted region or configuration. Such a
   result can be strictly weaker than RH. It must discharge its arithmetic
   hypotheses for that actual region, rather than append an unproved
   estimate to a hypothetical zero.

The first choice remains the active goal. The second is a useful way to
test whether a proposed new estimate has any concrete consequence.

## The earlier linear carrier already suffices

Let `rho=beta+i*gamma` be a hypothetical nontrivial zero with `beta>1/2`,
let `m>=1` be its actual multiplicity, and put `u=3/2-beta`, so `1/2<u<1`.
The fixed polynomial `P_rho` comes from the complete local zero divisor
and cancels all competing local zero modes and the pole at one.

Define the real, normalized finite ordinary-prime sum

\[
b_N=u^{N+1}\Re\sum_{p\in\mathcal B_N}
 \frac{\log p}{p^{3/2+i\gamma}}
 \sum_k (P_\rho)_k\frac{(\log p)^{N+k}}{(N+k)!},
\]

where `B_N` contains the primes with
`N*log(2)/4 < log(p)` and `p <= 2^(32*N)`. Theorems
`zetaOrdinaryPrimeBandFilter_eq_prime_sum` and
`tendsto_zetaRightHalfOrdinaryPrimeBandFilter_re` identify this literal
sum and prove

\[
\boxed{b_N\longrightarrow-m.}
\]

The proper-prime-power contribution, both arithmetic tails, the canonical
analytic residual, and the reflected modes have already been controlled.
See [the exact filter](zeta-zero-mode-filters.md) and
[the finite band](zeta-prime-moment-band.md).

For this carrier it is enough to prove, independently, that for this
`rho` there is an `epsilon>0` such that

\[
\boxed{b_N\ge-m+\epsilon\quad\text{for arbitrarily large }N.}
\]

The contradiction is elementary: convergence gives
`b_N < -m+epsilon/2` at every sufficiently large order. The asserted
cofinal set would contain an order beyond that threshold. For example,
the lower bound `b_N >= -m/2` would suffice.

This asks for one real component, one fixed zero-dependent filter, and
arbitrarily large orders. It requires neither an absolute-value bound,
control at every order, decay to zero, uniformity over ordinates, nor a
prime-pair estimate. This observation was already stated in the exact
filter documentation; restating it is not an additional theorem advance.

One suitably late finite witness would also contradict the proved
eventual bound. However, the existing asymptotic theorem does not supply
a computable uniform onset. A favorable early order or a finite numerical
scan does not by itself meet the required threshold. The filter itself
also depends on the actual local zero divisor.

## Audit of the available routes

| Route | Available checked input | Remaining obstacle |
| --- | --- | --- |
| Linear ordinary-prime band | Exact negative multiplicity limit; all discarded terms bounded | A one-sided cofinal lower bound for the same signed sum |
| Signed Chebyshev integral | Exact Abel transform; density and endpoints negligible | The same cancellation expressed against the Chebyshev error |
| Distinct-prime quadratic | Whole mixed term and same-prime term negligible; exact nonzero source | A signed bound for a more complicated bilinear carrier |
| Positive prime Gram matrices | Exact complex energy, strict finite witnesses, full finite rank | No lower bound for the required signed linear functional |
| Prime-power phase recurrence | Positive return for a fixed phase block; quantitative arithmetic floor | Different quantifiers and weights from the moving ordinary-prime band |
| Suzuki/Landau | Full analytic implication from a signed-work floor to RH | The independent arithmetic floor remains open |
| Symmetric quartet/Pick models | Finite model identities and defect inequalities | Background positivity and the actual global transport must be justified |

The Gram identity is genuinely arithmetic and retains every cross term,
but each mixed zeta argument lies in `Re(s)>1`, where the positive Euler
series converges. Analytic continuation of the response does not establish
positivity on a larger domain. Strict positive definiteness also supplies
no uniform conditioning or source-sized margin.

The prime-power recurrence varies the multiple of a fixed angle. The
linear target varies moment order and its entire prime-weight distribution
at fixed `gamma`. A positive return in the former is not a positive return
in the latter. Moreover, the proper-prime-power contribution to the linear
target is already proved negligible. Further estimates confined to that
contribution cannot cancel the retained source.

The new separation identity for `p^a*q^b` is exact, but its nonnegative
logarithmic defect controls a raw arithmetic coefficient. No theorem
transfers that coefficient bound through the complex filter with a useful
signed margin. Further shell or heat decompositions require such a
mechanism before they justify additional investment.

Broad twisted convolution estimates are also established RH
reformulations in the literature: Banks and Sinha prove such connections
for the generalized von Mangoldt functions and fixed convolution powers
of von Mangoldt. Their results do not prove the zero-dependent one-sided
bound above or establish that it cannot have a shorter proof.
See [Banks and Sinha, arXiv:2209.11768v2](https://arxiv.org/abs/2209.11768v2).

## Revised working priority

Pause expansion of the quadratic decomposition. Retain its checked
identities, including the exact two-prime coefficient, as available tools.
Use the earlier linear finite band as the reference contradiction target.

Evaluate a proposed input by the inequality it can actually prove for that
band. It must retain the same filter and source, preserve the sign until
the useful comparison, and supply a positive margin after the proved
errors. A transformation that merely moves or cancels the source is not
such an input. The precise allowance can be zero-dependent and the
favorable orders can be sparse.

Before building another extensive chain, require either this cofinal
estimate or a genuinely proved version on a restricted region that yields
a concrete exclusion there. Another equivalent criterion, smaller
negligible error, or unconditional positivity result without this
comparison does not establish progress on the open inequality.

No candidate independent lower bound passed that test in this audit.
The next mathematical task is to find such an input, not to repeat the
already completed zero-source extraction.
