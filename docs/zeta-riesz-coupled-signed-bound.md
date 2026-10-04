# The whole joined signed inequality

`ZetaRieszCoupledSignedBound` proves a one-sided bound for the **literal
whole** `prefixPairDefect`, including `balancedPrefix + maskRest`. The
independent target `399/5000 = 0.0798` remains open globally.

Let `a_i = ordinaryArray u y i`, `K = 13N/32`, and
`b = (N+1)/(u * length u N)`. Define

\[
w_i=\frac1N+
 \mathbf1_{K\le i<N-K}\frac1{N-i},\qquad
v_i=\mathbf1_{i\le N-K}\frac1{N+1-i},\qquad
r_i=\frac{w_i-bv_i+w_{N-1-i}-bv_{N-1-i}}2.
\]

The checked identity first aligns the two adjacent factorial degrees,
then joins swapped incidences:

\[
H_N=\sum_{i<N}r_i a_i a_{N-1-i}
 +b\sum_{i<N}v_i a_i(a_{N-1-i}-a_{N-i}).
\]

No order-zero endpoint, diagonal, complex phase or original prefix is
removed. Writing `sgn(r)=1` for nonnegative `r` and `-1` otherwise gives
the exact real-product identity

\[
r\Re(zw)=\frac{|r|}2(|z|^2+|w|^2)
 -\frac{|r|}2|z-\operatorname{sgn}(r)\overline w|^2.
\]

Accordingly the main real part is exactly `D_N-Q_N`, where `D_N` is the
joined diagonal energy and `Q_N` is the complete nonnegative correlation
credit. The checked whole-prime inequality is

\[
\Re\,\mathrm{prefixPairDefect}_N
 \le D_N-Q_N+\mathrm{advancePrice}_N
   +\mathrm{wholeCompletionBudget}_N+\mathrm{squareBudget}_N.
\]

Only the adjacent-order difference receives the new norm allowance. The
old **whole-support** and single-diagonal payments are used once. This
does not complete the balanced hard mask independently or transfer separate
complete-leg limits through it. The same inequality holds for the original
balanced contribution **together with its original rest**.

## Quantitative results

Lean proves, uniformly for every `N >= 65536` and `b >= 1`,

\[
\sum_{i<N}|r_i|\le
 \sum_{i<N}(w_i+bv_i)-\frac13.
\]

This is a coefficient-price contraction on the entire native order band,
not an arithmetic proof of the missing `0.0798` bound. On the literal
radius strip the checked moving length gives `1 <= b <= 3/2`.

Under the existing exposed-zero hypotheses, with analytic multiplicity
`m` and the proved finite ordinary-prime source-error mass `M`,

\[
\mathrm{advancePrice}_N\le
 \frac{12(m+M)M}{N+1}.
\]

The source-error hypothesis is explicit; this pays only the adjacent-order
error, not the signed main.

## Sharpness and numerical controls

A constant complex array attains `Re H_N = D_N-Q_N` exactly. For the
coherent array `a_i=-1`, the checked cofinal limit is
`1-retainedCost(u)`, strictly above `399/5000`. The checked
`no_generic_constant_credit_target` rules out obtaining an extra target
credit **for all arrays** from the coefficient algebra alone. It is not an
impossibility theorem for actual prime arithmetic.

At `u=10001/20000` the limiting source is approximately
`0.0798717970349442`. The difference `0.0000717970349442` is the extra
upper-bound saving needed to reach `0.0798` in that coherent source model.
It is not an already-earned arithmetic credit. At `N=1048576` the literal
coherent value is about `0.0798450241993419`, already above the target.
Some smaller native orders lie below it; their finite damping does not
establish a cofinal bound.

The optional ball probe has 12 coefficient rows and four actual finite-prime
controls. At the last ceiling row the separate coefficient price is about
`2.67913347789`, the joined price `0.131174332584`, and the coherent credit
`0.0513293083846`. These are sampled certificates, not a Lean proof of a
uniform `0.14` price or a new global floor saving. The actual-prime controls
are at `N=256`, below native entry order, and their heights are not asserted
zero ordinates. Producer precision is 512 bits for those controls because
energy and credit cancel by about 33 decimal digits. The independent replay
uses 640 bits there and passes 140 ball-containment and width checks.

See `scripts/CheckRieszCoupledSignedBound.lean` and
`docs/riesz-coupled-signed-bound-audit.json` for the local Lean/axiom and
preservation audit. Numerical scripts are optional, never proof dependencies
or ordinary CI work. The next arithmetic estimate must apply to **actual**
`D_N-Q_N` without losing its credit. The independent radius estimate in
`ZetaRieszCoupledArithmeticBound` resolves that quantity on existing height
coverage; its uncovered-height limitation is documented separately.
