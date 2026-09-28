# Signed gains across a growing radial saddle band

Both whole-sum comparisons now accumulate their certified signed gains across
an interval whose width grows like `sqrt(N)`. After the global owner debit,
the retained margin is at least `(N/16) * sourceCredit`, replacing the earlier
single-credit margin `(sqrt(N+1)/16 - 1/8) * sourceCredit`. The final independent
whole floor `-79/1000` and ceiling `3/2` remain open.

## The literal populations and uniform bounds

For fixed `|y| >= 54`, choose the already-proved negative phase peak
`2N <= v <= 2N+1/2`. Put

\[
M_N=1+\left\lfloor\frac{|y|\sqrt N}{4\pi}\right\rfloor,
\qquad v_i=v+\frac{2\pi i}{|y|}\quad(0\le i<M_N).
\]

Every center lies in `[2N,2N+sqrt(N)]`. The full logarithmic periods
`(v_i-pi/|y|, v_i+pi/|y|]` are disjoint. Each period uses the existing literal
balanced-triple, adverse-four, five-prime supply, full positive-five interior,
small-prime five-prime head, signed unbalanced-triple, and allocation-transition
six-prime populations. They are intersected with the original `coreBand`.
No prime, factorial order, allocation factor, complex phase or physical mask
is replaced by a limiting model.

`ZetaRieszSaddleBand` extends the actual cutoff ratio, signed factorial prime
period and allocation-transition payment uniformly across this growing band.
The length is still `SquarefreeVaughanLogSource.length u N`, not a frozen
multiple of `N`. The cutoff remains in the checked bin
`693/1000 <= L/T <= 1733/2500` eventually. The radial estimate retains

\[
\frac{e^{-v_i/2}v_i^N}{N!}\ge
\frac{e^{-1}2^N}{3\sqrt N}.
\]

The numerical covers are reused unchanged. Their application is still
independent of any zero or simplicity hypothesis, for
`1/2 < u <= 10001/20000` and fixed height `y`.

## Summing credits without repeating the whole sum

`CheckRieszSaddleBandLocal` extracts a bound for each paid finite population
`E_i`, before adding the complementary carrier or paying global errors. With
`f_N(n) = residualCoefficient(A,L,N,n) * zetaPrimeLogKernel(N,3/2+iy,n)`, its
floor is

\[
u^{N+1}O_i^-+\frac{\sqrt{N+1}}{16}G_N-a_N
\le u^{N+1}\operatorname{Re}\sum_{n\in E_i}f_N(n).
\]

Here `G_N=sourceCredit u y N`, `a_N=allocationBound N`, and `O_i^-` retains
the favorable positive observations of the previously paid groups. The ceiling
uses its own original populations and negative observations `O_i^+`, with the
opposite credit. The two ledgers are separate and their credits are never
added to each other.

The exact disjoint union `E=union_i E_i` lets Lean sum these local inequalities.
This does not add repeated inequalities for the same whole sum. The remaining
owner population is `D=JointOwnerPayment.population (S\E) A`; its debit is
paid once. The literal remaining labels are exactly

`S \ (E union D)`.

The resulting whole floor has margin

\[
\left(\frac{M_N\sqrt{N+1}}{16}-\frac18\right)G_N,
\]

plus every separate favorable observation; the whole ceiling subtracts this
margin and retains its corresponding negative observations. Lean proves

\[
\frac{M_N\sqrt{N+1}}{16}-\frac18\ge\frac N{16}\qquad(N\ge1).
\]

All `M_N` triple-completion errors are paid: eventually `M_N <= N+1`, and
`(N+1)*allocationBound N -> 0`. The companion/core transfer error is paid
once. `CheckRieszSaddleBandWhole` then applies the preceding twice-reflected
six-prime estimates only to the exact unpaid rest. No period or owner payment
is repeated. The earlier fixed collection of six-prime centers is among the
new centers, but its old credit is not added again.

## Numerical check and limits

The optional [geometry probe](../scripts/probe_riesz_saddle_packing.py) checks
the packing and radial ratios without attempting any prime computation.
At `|y|=54`, it gives 430, 4298, 42972 and 429719 periods for `N=10^4,10^6,
10^8,10^10`. The last/first radial ratio is about `0.969`.
The narrow cutoff bin fails at the first two diagnostic orders; it fits the
asymptotic length at the last two. These floating values certify neither an
initial order nor an arithmetic bound. The Lean result is eventual, with an
existential threshold depending on the fixed parameters.

This is a concrete increase in the whole signed credit and in the covered
radial width. It covers a growing part of the right side of the saddle, not
the entire core or every prime-count/share configuration. The exact signed
rest must still satisfy a sufficient independent bound. No zero exclusion or
RH contradiction is claimed, and no simplicity premise enters these estimates.

## Checked sources

- [Uniform arithmetic band](../RiemannGaussian/ZetaRieszSaddleBand.lean)
- [Disjoint packing and accumulated inequalities](../RiemannGaussian/ZetaRieszSaddlePacking.lean)
- [Local certified signed bounds](../scripts/CheckRieszSaddleBandLocal.lean)
- [Both accumulated whole comparisons](../scripts/CheckRieszSaddleBandJoint.lean)
- [Both whole comparisons with the earlier reflection savings](../scripts/CheckRieszSaddleBandWhole.lean)
- [Verification and cached-cover audit](riesz-central-capacity-audit.json)

The optional application files compile against the existing cached finite
covers. Ordinary builds do not rerun exhaustive cover verification.
