# Exact zero geometry in signed prime moments

The compiled chain now constructs a fixed, exact polynomial filter from
the actual local zero divisor. It annihilates zeta's pole and all but one
local singular zero mode. After normalization, its literal signed prime
sum converges to the negative analytic multiplicity of the selected zero.
The analytic residual and all reflected canonical modes are proved to
vanish at that scale.

This supplies an arithmetic signal for every hypothetical zero right of
the critical line, without a height restriction. It does not prove an
independent arithmetic bound on that signal, exclude a new zero, or prove
RH. Lagrange interpolation, Cauchy's estimate, and geometric mode extraction
are standard mathematics; this formal combination is new to the repository,
and no claim of mathematical priority is made.

The subsequent [arithmetic prime-band theorem](zeta-prime-moment-band.md)
removes proper prime powers and both ordinary-prime tails with independent
bounds. The same multiplicity signal survives in one finite signed sum
over ordinary primes. Its independent lower bound remains open.

## The literal prime carrier

For `Re s > 1`, define

\[
M_n(s)=\frac{(-1)^n}{n!}
 \frac{d^n}{ds^n}\left(-\frac{\zeta'(s)}{\zeta(s)}\right).
\]

`hasSum_zetaPrimeLogMoment` proves genuine convergence of

\[
M_n(s)=\sum_{m\ge1}\frac{\Lambda(m)(\log m)^n}{n!m^s}.
\]

For any polynomial `P(X)=sum_k p_k X^k`, the finite consecutive filter is

\[
F_{P,N}(s)=\sum_k p_kM_{N+k}(s).
\]

`hasSum_zetaPrimeLogFilter` proves that this is the convergent arithmetic sum

\[
\boxed{
F_{P,N}(s)=\sum_{m\ge1}\frac{\Lambda(m)}{m^s}
 \sum_k p_k\frac{(\log m)^{N+k}}{(N+k)!}.
}
\]

Coefficients may be complex. The factors `exp(-i Im(s) log m)` and every
finite cross-phase cancellation are retained. The filter polynomial in
moment order is distinct from the displayed log-weight polynomial, whose
factorials depend on `N`.

## Two exact modes for every actual local zero

Use the [adaptive canonical disc](zeta-canonical-boundary-source.md)
centered at `s0=3/2+i*y`, with zero-free boundary `r<R<1`. Let `S` be its
finite set of distinct zero displacements and `d_j` their actual analytic
multiplicities. Write

\[
b_j=-\frac1j,\qquad c_j=-\frac{\overline j}{R^2},
\qquad b_{\rm pole}=\frac1{1/2+iy}.
\]

For the complete canonical response, Lean proves

\[
\frac{(-1)^n}{n!}C_R^{(n)}(j,0)
 =b_j^{n+1}-c_j^{n+1}.
\]

In particular, the reflected correction is kept with its original sign.
`zetaPrimeLogMoment_eq_adaptive_modes` gives the exact actual identity

\[
M_n(s_0)=b_{\rm pole}^{n+1}-E_n
 -\sum_{j\in S}d_j\bigl(b_j^{n+1}-c_j^{n+1}\bigr),
\]

where `E_n` is the signed moment of the logarithmic derivative of the
actual zero-free canonical residual. For every `0<q<R`,
`norm_adaptiveZetaResidualMoment_le` proves

\[
|E_n|\le (n+1)\frac{8\log(|y|+22)}{R-q}\,q^{-n}.
\]

Consequently, `a^(n+1) E_n -> 0` whenever `|a|<R`. The proof chooses a
strictly intermediate `q`, so the geometric gap absorbs the factor `n+1`.
This is decay relative to the selected source; it is not absolute decay
of the unnormalized derivatives.

## A unique minimum-degree exact isolator

Select `i in S`. The pole node is different from every zero node: actual
zero displacements have real part strictly less than `-1/2`, whereas the
pole displacement is `-(1/2+iy)`. The inverse map preserves distinctness.
Set

\[
\boxed{
P_i(X)=\frac{X-b_{\rm pole}}{b_i-b_{\rm pole}}
 \prod_{j\in S\setminus\{i\}}\frac{X-b_j}{b_i-b_j}.
}
\]

The definition `adaptiveZetaZeroModeFilter` uses the exact Lagrange basis.
Lean proves

\[
P_i(b_i)=1,\quad P_i(b_j)=0\ (j\ne i),\quad
P_i(b_{\rm pole})=0.
\]

It also proves that `degree P_i = |S|`, that every polynomial satisfying
these exact isolation conditions has degree at least `|S|`, and that the
one of degree at most `|S|` is unique. The relevant theorems are
`adaptiveZetaZeroModeFilter_natDegree`,
`adaptiveZetaZeroModeFilter_minimal_natDegree`, and
`adaptiveZetaZeroModeFilter_unique`.

This count has a specific geometric meaning: it counts distinct local
zeros for exact cancellation of all competing singular modes and the
pole. Multiplicity changes the amplitude, not the degree. Degree `|S|`
uses a window of `|S|+1` consecutive moments; some coefficients may vanish.
It is not a theorem about the smallest support, the fewest heights in a
phase inequality, the minimum degree needed merely for asymptotic
extraction, or a global invariant of zeta. In particular, cancelling
strictly smaller competing modes need not be necessary for an asymptotic
limit.

## The normalized limit is the selected multiplicity

The exact filtered identity retains both errors:

\[
F_{P_i,N}(s_0)=-d_i b_i^{N+1}
 -\sum_k p_k E_{N+k}
 +\sum_{j\in S}d_j c_j^{N+1}P_i(c_j).
\]

Each normalized reflected mode has magnitude
`|i| |j| / R^2 < 1`. The finite analytic filter also tends to zero after
normalization; its coefficients are fixed as `N` grows. Therefore
`tendsto_zetaPrimeLogFilter_selected_zero` proves

\[
\boxed{(-i)^{N+1}F_{P_i,N}(s_0)\longrightarrow-d_i.}
\]

No uniform bound on the inverse Vandermonde matrix is needed for this
pointwise limit. Closely spaced modes can still make coefficients large
and delay the effective onset; this theorem gives no uniform cutoff in
height, spacing, or multiplicity.

For an actual zero `rho=beta+i*gamma` with `beta>1/2`, choose its adaptive
disc as before and let `u=3/2-beta`, so `1/2<u<1` and `i=-u`. The fully
specialized theorems `tendsto_zetaRightHalfZeroModeFilter` and
`zetaRightHalfZeroModeFilter_eventually_negative` prove

\[
\boxed{u^{N+1}F_{P_\rho,N}(3/2+i\gamma)\longrightarrow-m(\rho),}
\]

and, for all sufficiently large `N`,

\[
\boxed{\Re F_{P_\rho,N}(3/2+i\gamma)
 <-\frac{m(\rho)}{2u^{N+1}}.}
\]

The degree, coefficients, and errors all arise from literal zeta objects.
The construction applies to each hypothetical right-half zero and is not
restricted to a chosen numerical phase family.

## The remaining arithmetic task

The unproved step is a lower bound for the same signed arithmetic sum,
independent of the zero-side decomposition. For example, infinitely many
orders with a normalized real value greater than a fixed constant strictly
above `-m(rho)` would contradict the proved limit. Any uniform sub-source
bound suffices; a full power saving is unnecessary.

The next useful investigation is the actual log-weight kernel
`sum p_k (log m)^(N+k)/(N+k)!`, retaining its complex prime phases and all
cross terms. The [prime Gram kernel](zeta-prime-gram-separation.md) supplies
exact mixed arithmetic identities, but its positivity is not yet a lower
bound for this signed linear functional. Taking absolute values before
using the phases would return to the positive real-axis moments and can
lose the cancellation being sought.

The analytic error has now been closed for this filter. The arithmetic
bound remains open; no RH completion or new numerical zero exclusion is
claimed. The earlier Suzuki arithmetic target is a separate open route,
and this theorem does not discharge its residual bound.

## Local validation

The slice consists of `ZetaPrimeLogMoments.lean`,
`ZetaCanonicalMoments.lean`, and `ZetaZeroModeFilter.lean`, imported by the
root library. All three direct warning-as-error checks passed. The focused
build passed with 4,261 jobs and the full build with 9,793 jobs. Whole-package
declaration lint and module audits passed. All 36 public theorems were
explicitly audited from a root import and depend only on `propext`,
`Classical.choice`, and `Quot.sound`. Source and whitespace checks passed.
Commits and remote CI remain held at the user's request.
