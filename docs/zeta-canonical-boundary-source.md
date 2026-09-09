# Boundary weights and a signed source throughout the right half-strip

The source inequality now covers **every actual zero with real part greater
than one half**. The former `beta >= 3/4` restriction came from a fixed local
disc. An adaptive disc and a signed estimate using Jensen boundary weights
remove that restriction without an unweighted count of zeros near the
boundary.

The exact canonical source is retained in the arbitrary phase-family
theorem. Its simpler positive lower bound is a separate consequence.
The independent arithmetic estimate needed to beat the analytic allowance
is still open. This slice proves no further numerical zero exclusion and
does not establish mathematical priority or prove RH.

The subsequent [exact zero-mode filter](zeta-zero-mode-filters.md) retains
this complete canonical decomposition through all higher signed
derivatives. It isolates an actual zero in convergent prime moments and
proves that both normalized analytic error channels vanish. Its independent
signed arithmetic bound remains open.

## The information preserved by a complete canonical term

For a local zero displacement `w`, a real evaluation point `v`, and disc
radius `R`, define

\[
C_R(w,v)=\frac1{v-w}+\frac{\overline w}{R^2-\overline wv}.
\]

The first term is singular; the second is its regular canonical
correction. `zetaCanonicalZeroResponse_eq_radial` proves the full complex
identity

\[
\boxed{
C_R(w,v)=\frac{R^2-|w|^2}{|R^2-\overline wv|^2}
 \left[\frac{R^2-v^2}{v-w}+v\right].
}
\]

The factor `R^2-|w|^2` retains proximity to the boundary. Bounding the
regular correction separately by its norm loses this factor.

The real response need not be nonnegative. The exact geometric example
`R=1`, `w=-5/8+(3/4)i`, `v=-3/8` gives `Re C=-6/2725`, despite
`|w|<R` and `Re w<v`. The theorem does not assert that this example is a
zero of zeta.

For `3/4 <= R <= 1`, `0<|w|<R`, `|v|<=1/2`, and `Re w<v`, the compiled
`zetaCanonicalZeroResponse_re_add_log_nonneg` instead proves

\[
\boxed{\Re C_R(w,v)+32\log(R/|w|)\ge0.}
\]

The negative response is paid by its logarithmic boundary weight. The
proof first retains `R^2-|w|^2`, then bounds it by `2 log(R/|w|)`.

## The actual zeta divisor has a uniform weighted allowance

Translate the literal entire pole-removed zeta function about
`3/2+i*y`. For any prescribed `3/4 <= r < 1`, the adaptive construction
selects `r<R<1` with no zeros on its boundary and removes the complete
interior divisor. Let `g` be the resulting nonvanishing analytic residual
and `d_w` the actual divisor multiplicities. Define

\[
J_R(y)=\sum_w d_w\log(R/|w|).
\]

`adaptiveZetaJensenWeight_eq_log_ratio` and
`adaptiveZetaJensenWeight_le` prove

\[
\boxed{
J_R(y)=\log\frac{|g(0)|}{|\zeta_1(3/2+iy)|}
\le4\log(|y|+22).
}
\]

The original eta upper envelope and Moebius center floor discharge the
analytic inputs. The constant is uniform as `R` approaches one. There is
no claim of a uniform unweighted zero count in those growing discs.

For `0<x<=1`, set `v=x-1/2`. Every actual interior zero is to the left of
this evaluation point. Summing the compensated terms gives the exact
nonnegative quantity

\[
\sum_w d_w\Re C_R(w,v)+32J_R(y)\ge0.
\]

The selected term can be retained separately. The complete complex
logarithmic-derivative identity also remains available in
`neg_logDeriv_riemannZeta_eq_adaptive`. Only the analytic residual is then
bounded by `320 log(|y|+22)`. Paying the other canonical terms uses at most
`32*4 log(|y|+22)`, giving the same combined allowance `448 log(|y|+22)`.

## Every hypothetical right-half zero contributes a positive source

Take a literal zero `rho=beta+i*gamma` with `beta>1/2`, write
`delta=1-beta` and `u=3/2-beta`, and choose

\[
r=\frac{1+u}{2}=\frac54-\frac\beta2<R<1.
\]

The actual zero lies strictly inside this adaptive disc. Translation
preserves its full analytic multiplicity `m(rho)`. The exact source is

\[
S_\rho(x)=m(\rho)\Re C_R(-u,x-1/2).
\]

`neg_logDeriv_add_halfStripCanonicalSource_le` retains this source in
the literal inequality

\[
\boxed{
\Re\!\left(-\frac{\zeta'}\zeta(1+x+i\gamma)\right)+S_\rho(x)
\le\frac{x}{x^2+\gamma^2}+448\log(|\gamma|+22).
}
\]

For every `0<x<=1`, the downstream lower bound is

\[
\boxed{
S_\rho(x)\ge
\frac{m(\rho)(\beta-1/2)}{3(x+1-\beta)}>0.
}
\]

`halfStripCanonicalSource_pos` proves strict positivity. All logarithmic
derivatives are evaluated in `Re s>1`; the argument does not assume
nonvanishing in the unknown part of the critical strip.

## The same source couples to arbitrary arithmetic phases

For nonnegative summable coefficients `a_n`, arbitrary real frequencies
`omega_n`, and any index `k` with `omega_k=1`, write

\[
P(t)=\sum_n a_n\cos(\omega_nt),\qquad
W_\sigma(y)=\sum_{m\ge1}\frac{\Lambda(m)}{m^\sigma}P(y\log m).
\]

If the actual height costs are summable,
`zetaPhase_halfStripCanonicalSource_add_primeWork_le` proves

\[
a_kS_\rho(x)+W_{1+x}(\gamma)
\le\sum_n a_n\frac{x}{x^2+(\omega_n\gamma)^2}
 +448\sum_n a_n\log(|\omega_n\gamma|+22).
\]

The signed arithmetic sum is complete, with genuine convergence. Kernel
positivity is not needed for this theorem. When `P>=0`, every finite
arithmetic window can replace the full sum as a lower bound, via
`zetaPhase_halfStripCanonicalSource_add_finite_primeWork_le`.

For integer frequencies, finite mass and a logarithmic moment suffice.
With `M=sum(n>=1) a_n`, `B=sum(n>=1) a_n log n`, `x=kappa*delta`, and
`0<kappa*delta<=1`,
`phase_halfStrip_source_add_primeWork_le_split_budget` proves

\[
\begin{aligned}
\delta a_1S_\rho(\kappa\delta)-\frac{a_0}{\kappa}
 +\delta W_{1+\kappa\delta}(\gamma)
\le{}&448\delta[a_0\log22+M\log(|\gamma|+22)+B]\\
 &+\frac{\kappa M\delta^2}{\gamma^2}.
\end{aligned}
\]

This keeps the **exact** source. Replacing it by the simpler critical-distance
lower bound can lose useful strength, so that replacement is confined to
a separate theorem. A positive selected source does not by itself imply
that the contrast `delta*a_1*S-a_0/kappa` is positive.

## The remaining research obligation

The analytic source interface now has the full right-half-strip domain.
What is missing is an independent signed arithmetic inequality that beats
the displayed allowance for each hypothetical zero. A positive source,
a positive prime-power floor, or a finite phase optimum alone does not
establish that inequality. The exact source, canonical responses, weighted
zero mass, multiplicities, and signed prime sum remain available to test
stronger coupled estimates.

The separate Suzuki actual-cutoff arithmetic bound remains unproved.
This prime-phase work has not been identified with that distinct signed
Suzuki work. The previous numerical exclusion from
[the exact-family budget](zeta-phase-zero-budget.md) remains valid.

## Local validation

The five modules contain 50 public theorems and are root-imported. All
passed direct warning-as-error elaboration, the focused build (4,410 jobs),
the full build (9,790 jobs), whole-project declaration lint, and root-import
module lint. Every new public theorem has only the standard logical axioms
in its transitive dependencies. No commit or remote CI run is part of this
local iteration.
