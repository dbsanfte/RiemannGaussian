# A quantitative bound for the whole signed carrier

The all-height, fixed-strip ceiling remains **open**. This local slice proves
an explicit height-dependent upper bound for the entire existing
`joinedPhysical` carrier, and a near-target constant bound on a finite height
range. It changes no carrier, radius, phase, mask, allocation, prime-count
cutoff, moving length, diagonal or factorial endpoint.

For an original exposed candidate zero, put

\[
u=\tfrac32-\Re\rho\in(\tfrac12,\tfrac{10001}{20000}],\qquad
L=\log(|\Im\rho|+2),\qquad m=\operatorname{ord}_\rho\zeta\ge1.
\]

The existing source theorem gives

\[
u^{N_j+1}\operatorname{joinedPhysical}_j\longrightarrow
-m+m^2c_{\mathrm{ret}}(u).
\]

The **independent arithmetic input** is the complete, already-proved Gaussian
contact-family inequality. Exposure enters only when this arithmetic
multiplicity bound is transferred to the existing carrier source.

## Exact prices and quantitative saving

Define the full arithmetic price

\[
B(q,L)=36922q+\frac L{35}+57\log L+840,
\qquad A_0=\frac{984028661}{312500},\qquad A_1=6200.
\]

The slice proves, for every eligible actual height in the original fixed strip,

\[
A_0m\le B(9/100,L),\qquad A_1m\le B(1,L).
\]

There is no unevaluated prime-mass assumption: the existing exact contact
family discharges every premise. At the lower heights the previous simplicity
theorem is retained. Thus the explicit all-height cap is

\[
M(L)=
\begin{cases}
1,&L\le60000,\\
\min\{B(9/100,L)/A_0,\ B(1,L)/A_1\},&L>60000.
\end{cases}
\]

For every fixed original exposed candidate, every \(\varepsilon>0\), and
eventually along the original dyadic schedule,

\[
\boxed{\Re\bigl(u^{N_j+1}\operatorname{joinedPhysical}_j\bigr)
<-M(L)+c_{\mathrm{ret}}(u)M(L)^2+\varepsilon.}
\]

This is a bound for the **whole signed carrier**, rather than a population
payment or a positive majorant growing with the factorial order. It still
grows with **height**, and therefore cannot provide the uniform \(42/25\)
ceiling.

At \(L\ge10^7\), Lean proves

\[
\frac{B(1,L)}{A_1}\le\frac47\frac{B(9/100,L)}{A_0},
\qquad
-M+c_{\mathrm{ret}}M^2
\le\frac{16}{49}\left[-\frac{B(9/100,L)}{A_0}
+c_{\mathrm{ret}}\left(\frac{B(9/100,L)}{A_0}\right)^2\right].
\]

The \(33/49\) saving is in the **comparison certificate price**. It is not
a percentage of the RH proof, measured cancellation, or constant-ceiling
credit. At \(u=10001/20000,L=10^7\), the two prices are approximately
\(7754.7613\) and \(2466.5921\), respectively. Both remain far above \(1.68\).
As \(L\to\infty\), the quadratic price ratio tends to approximately
\(0.2579479457\). The complete growing height term remains explicit.

## A near-target numerical ceiling and its exact gap

Retaining integrality yields a second useful estimate. Lean proves

\[
3A_0-left(36922\frac9{100}+\frac{160000}{35}+57\cdot12+840\right)
=\frac{61833131}{2187500}>0.
\]

The bound \(\log160000\le12\) is proved using a rational lower bound for
\(e^{12}\); it is not a numerical assumption. Consequently every actual
candidate in the original strip with \(L\le160000\) has \(m\le2\).
This needs no exposed-zero premise. It does **not** prove simplicity there.

Using the existing exact bound \(c_{\mathrm{ret}}<4601/5000\), the same
native carrier therefore satisfies

\[
\boxed{\Re\bigl(u^{N_j+1}\operatorname{joinedPhysical}_j\bigr)
<\frac{2101}{1250}=1.6808\quad\text{eventually},\qquad L\le160000.}
\]

Its gap to the required \(42/25=1.68\) is exactly
\(1/1250=0.0008\), **above** the target. This is not a zero exclusion.
At the radius ceiling the retained double source is approximately
\(1.6805128118602233\), so the near-target bound is consistent with the
still-unexcluded double source. No claim of a smaller source is made.

## Proof mechanism

The new dilation-one lower price comes from the **second actual half-Gaussian
moment**, keeping the signed recurrence joined. For every real \(x\),

\[
\operatorname{halfGaussian}(1,x)\ge\frac{x}{x^2+2}.
\]

Scaling to the physical Gaussian gives the exact lower bound
\(1125050000000/57143889>19650\). The cotangent cost is at most five,
the contact-family first coefficient is at least \(79/250\), and the full
Poisson reserve is nonnegative. Hence the price per actual multiplicity is
at least \(6200\). All multiplicities, phases and source terms are retained.

The earlier all-family positive-Gaussian-budget no-go remains valid.
Nothing here pays the linear height term uniformly. The necessary next
estimate must use actual signed arithmetic/divisor correlations to remove
that growing price, or directly prove the constant native ceiling. Further
Gaussian dilation tuning cannot be reported as closure of that gap.

The literature check is consistent with this limitation:
[Ivić's near-one multiplicity estimate](https://arxiv.org/abs/1706.08268)
retains growing logarithmic height terms. It does not imply all-height
simplicity in a fixed-width strip. The present Lean proof uses the
repository's complete Gaussian inequality, rather than assuming that
literature estimate or an unspecified starting height.

## Local validation and preserved scope

The leaf is
[ZetaRieszCeilingWholeHeightBound.lean](../RiemannGaussian/ZetaRieszCeilingWholeHeightBound.lean).
The principal endpoints are `eventually_joinedPhysical_height_ceiling`,
`eventually_joinedPhysical_reduced_ceiling`, and
`eventually_joinedPhysical_near_ceiling`.

The optional 360-bit probe and independent 420-bit replay check the complete
scalar prices at 17 logarithmic heights, including \(10^{1000}\), with
interval widths retained. They sample no actual zeros, enumerate no native
core, and certify no finite native entry order. Lean proves the all-height
statement; those rows are regression controls, not extrapolations.

The scoped leaf build, 14 linters and transitive standard-axiom audit are
recorded in [the audit](riesz-ceiling-whole-height-bound-audit.json).
All 285 preceding proof/probe pins are preserved. Work stays local:
no commit, push, root registration, public explorer/README update or CI
change. Concurrent semiprime work is not part of this slice.

The full all-height \(42/25\) ceiling, simple-zero floor and RH contradiction
remain open. The active goal is unchanged.
