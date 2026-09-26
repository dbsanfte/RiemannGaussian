# Ordered least-prime Euler completion of the marked packet

The follow-on [ordered Euler correction bound](zeta-riesz-ordered-euler-bound.md)
pays the exponential prime head and the full nonlinear correction, including
its leading quotient multiplier, through this exact marked operator.

The literal signed packet now has a **proved source-equivalent ordered
Euler-product completion**, and both physical prime endpoints can be
removed with a vanishing source-scale error. The unrestricted arithmetic
series is also the limit of its finite Euler integrals at each fixed order.
These are comparison theorems, not a bound on the common main term or a
zero exclusion. All previous negative audits remain in force.

The first completion theorem is
[`ZetaRieszOrderedEulerCompletion.tendsto_completion_sub_current`](../RiemannGaussian/ZetaRieszOrderedEulerCompletion.lean).
For every fixed real height `y` and
`1/2 < u <= 10001/20000`, it proves, on the original dyadic schedule,

\[
u^{N_j+1}\left(\mathcal E_{N_j}
 -\left[\operatorname{lowerThresholdPacket}_{N_j,K_j}
       -\operatorname{shortOverflowPacket}_{N_j,K_j}\right]\right)
\longrightarrow 0.
\]

There is no hypothetical-zero assumption and no new cancellation premise.
The target retains exactly the old signed counts `3..55` minus upper
least-order overflow counts `3..13`.

## The completed object

Let `A_N = intermediatePrimes u N`, with the original strict physical
endpoints `N^2 < p < (linearDampedCutoff u N + 2)^2`. Put

\[
s_0=\frac32+iy,\qquad
\Phi_p(\xi)=1-p^{-i\xi},\qquad
G_p(t;\xi)=\sum_{k\ge0}\Phi_p(\xi)
 \frac{(\log p)^k}{k!}p^{-s_0}t^k.
\]

Here `G_p` is a formal power series, so no analytic convergence or
coefficient interchange is being assumed. In particular, orders zero
and one are retained.

For a canonical least prime `r` and a distinct marked prime `p>r`, the
middle product is

\[
E_{p,r}(t;\xi)=
\prod_{\substack{q\in A_N\\q>r,\ q\ne p}}
 \left(1+G_q(t;\xi)\right).
\]

The marked prime need not be the largest prime. Every marked incidence is
counted once. For the **existing** finite set `rectangleOrders N j`, define

\[
\mathscr R_{N,p,r}[E](\xi)=
\sum_{j=0}^{N+1}\ \sum_{h\in\operatorname{rectangleOrders}(N,j)}
 [t^j]G_p\,[t^h]G_r\,[t^{N+1-j-h}]E.
\]

Thus the correlated total order, original owner band, shifted least-prime
condition `h+1`, and all remaining factorial orders stay exact. They are
not replaced by share indicators or separately convergent prime legs.
Set

\[
\mathscr S_N(\xi)=\sum_{r\in A_N}\sum_{\substack{p\in A_N\\r<p}}
 \mathscr R_{N,p,r}[E_{p,r}](\xi).
\]

The completion appearing in the terminal theorem is

\[
\boxed{
\mathcal E_N=\frac{N+1}{2\pi L_N}
\int_0^\infty
 \frac{e^{i\xi L_N}\mathscr S_N(\xi)
       +e^{-i\xi L_N}\mathscr S_N(-\xi)}{\xi^2}\,d\xi.
}
\]

Both frequencies are kept together. `integrable_orderedPair` proves
integrability of the paired expression, including at frequency zero.
`completePacket_eq_completion` identifies it exactly with the finite
arithmetic sum over all squarefree subsets of `A_N`, using the original
Riesz coefficient and marked rectangle mass. The completion has no
whole-integer window, share cut, nondominant selection or prime-count
ceiling. Its physical prime set is unchanged.

## Why the completion error is paid

The new [marked completion module](../RiemannGaussian/ZetaRieszMarkedCompletion.lean)
supplies the missing arithmetic estimates:

1. **Radial tails.** `exists_complete_radial_error` applies the existing
   logarithmic-deviation theorem to the entire physical subset universe.
   The total marked factorial mass remains at most one at `N>=21`.
2. **Share exteriors at all counts.** `markedMass_exterior` proves
   `markedMass <= 6 log(n) exp(-N/1600)`. It combines the canonical
   rectangle tail with every wrong-owner incidence. The actual factor
   count costs only `omega(n) <= 2 log(n)`, with no fixed count ceiling
   assumed on the completed universe.
3. **Source-scale exterior bound.** `log_norm_kernel` pays that logarithm
   by shifting the factorial kernel once. Consequently
   `exteriorPacket_bound` gives

   \[
   \|u^{N+1}\operatorname{exteriorPacket}_N\|
   \le 6U a^{-1}(N+1)r^N C_\sigma,
   \quad a=\frac{131071}{262144},\quad
   r=Ua^{-1}e^{-1/1600}<1,\quad
   U=\frac{10001}{20000}.
   \]

   The summable arithmetic majorant is
   `C_sigma = zetaMoebiusLogMajorantMass (1+1/262144)`.
4. **Original masks on the retained interior.**
   `core_interior_mem_fullBand` proves them rather than assuming them.
   The least-share condition implies `omega<=200`; the dyadic count
   ceiling eventually exceeds this. The largest share is below `3/5`,
   so neither old dominant/cancelling sector can occur. Every physical
   and original-window condition is checked against the existing chain.
5. **Existing paid comparisons.** The interior is exactly
   `rawInteriorPacket`. The previously proved old-allocation, ownership,
   count-tail and least-order-overflow comparisons then give
   `tendsto_complete_sub_current`.

## Exact algebra, not a surrogate product

The [factorial/Fourier bridge](../RiemannGaussian/ZetaRieszMarkedEuler.lean)
proves `rectangle_eq_marked` and `marked_atom_eq_integral` at each actual
squarefree label. `rectangle_middleEuler` sums all middle subsets before
any norm. The empty middle subset vanishes exactly because the two marked
orders cannot fill `N+1`; no semiprime correction has been suppressed.

The [ordered reindexing](../RiemannGaussian/ZetaRieszOrderedEulerCompletion.lean)
is a bijection between `(least prime, marked prime, nonempty middle subset)`
and `(squarefree integer, distinct marked incidence)`. It proves the
least-prime identity, squarefreeness and both inverse maps. This supplies
`orderedSymbol_eq_labels`, with no symmetry-factor approximation, prime
density replacement, composite-cofactor completion or phase limit.

## Remaining obligation

### The physical endpoints are also paid

The follow-on
[`ZetaRieszPhysicalCompletion`](../RiemannGaussian/ZetaRieszPhysicalCompletion.lean)
removes both remaining physical prime endpoints. This does not change the
factorial rectangle or replace the arithmetic measure by a prime density.

On the core and share interior, Lean proves

\[
\log\min\operatorname{PrimeFactors}(n)>
\frac1{200}\log n>\frac{39}{4000}N>2\log N
\]

eventually, while

\[
\log\max\operatorname{PrimeFactors}(n)<
\frac35\log n\le\frac{609}{500}N<\frac54N\le L_N.
\]

Consequently every such label already meets both original physical
endpoints. Any missing label is in the radial or share exterior, and both
errors have bounds uniform over **all finite partial sums**. The missing
arithmetic series is absolutely convergent at `Re s=3/2`, so these bounds
pass to its actual infinite sum:

\[
\left\|u^{N+1}\left(\mathcal P_N-\mathcal E_N\right)\right\|
\le C_{\rm rad}r_{\rm rad}^{N}
  +C_{\rm share}(N+1)r_{\rm share}^{N},
\qquad r_{\rm rad}<1,\quad
r_{\rm share}=Ua^{-1}e^{-1/1600}<1.
\]

Here `r_share` is approximately `0.99948275824`; its strict inequality is
proved in Lean, not inferred from this decimal. The estimate holds eventually
for each `1/2<u<=U`, uniformly in height. The new `packet` is the original
marked arithmetic atom summed over **all** squarefree labels with at least
three prime factors.

`tendsto_packet_sub_current` proves its source equivalence to the same
counts `3..55` minus overflow counts `3..13` target.
`prefixEuler_eq_sum` and `tendsto_prefixEuler` identify it, for each fixed
`N>=21`, as the limit of the ordered Euler integrals over `primesLE X`.
This is convergence of genuine arithmetic sums on the safe axis. It is
not a passage to an infinite zero-mode product, an interchange of the
`N` and `X` limits, or analytic continuation past a singularity.

### The signed main term

The coupled Euler response itself still needs a signed estimate at source
scale. The new theorem pays its difference from the **same** retained
packet; it does not establish decay or a floor for either side. After
such an estimate, the complementary carrier still needs its independent
one-sided bound. Neither RH nor a new zero-free region follows here.

The optional owner/radial/least-share numerical run remains a separate
synthetic continuum diagnostic. It is not used in these Lean proofs.
