# Local ordinate windows for the squarefree quotient

[ZetaSquarefreeLocalWindow](../RiemannGaussian/ZetaSquarefreeLocalWindow.lean)
proves the geometric transport needed to use a finite-height zero-free band
without imposing an unnecessary condition on all lower zeros.

For the actual quotient `Q(s)=zeta(s)/zeta(2*s)`, a Cauchy disc of radius `r`
about `3/2+i*y` meets denominator zeros only in the exact doubled window
`abs(Im(rho)-2*y)<=2*r`. The theorem `doubled_window` preserves this window
before taking any absolute-height ceiling.

For `abs(y)>1` and `0<m<1/4`, put
`R=1+min((abs(y)-1)/2,m/2)`. A proved right-zero margin `Re(rho)<1-m`
only for zeros in that local window supplies:

- `disc_safe`: both genuine poles and every denominator zero are absent
  from the complete closed disc.
- `analyticOnNhd_response`: the actual quotient is analytic on a
  neighbourhood of that entire closed disc.
- `exists_response_bound`: all finite excluded prime sets, valid squarefree
  marks, complex polynomial filters and moment orders inherit this radius.
  The signed first and doubled prime phases remain in the original envelope.

The window margin is an explicit premise of these transport theorems.
The [Gaussian-band application](zeta-squarefree-gaussian-band.md) now
discharges it at explicit center ordinates and proves uniform complete
matrix decay for the growing quadratic sieve. This generic module retains
its window premise. The separate independent ordinary-prime floor needed
by the RH contradiction remains open.

The module is imported by the root library. Its four public theorems pass
strict Lean elaboration and standard-only transitive axiom audits; the
whole-project gates check its integration with the existing proof chain.
