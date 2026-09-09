# Pole cancellation and the signed prime discrepancy

The [finite ordinary-prime band](zeta-prime-moment-band.md) now has an
exact, quantitatively controlled representation as an integral against
the actual Chebyshev error. Polynomial cancellation of zeta's pole becomes
a continuous primitive. Both endpoints and the continuous background are
independently bounded by a fixed constant times `2^(-N)`. The selected
zero's full negative multiplicity therefore survives in the remaining
signed integral, including its imaginary phase channel.

The independent opposite signed estimate is still open. This slice proves
no additional zero exclusion and does not prove RH. The connection is new
to this Lean chain; mathematical novelty relative to the literature has
not been established.

The next [Möbius pole-jet and tail result](zeta-moebius-pole-jet-tail.md)
removes an exponentially growing divisor head with an independent
geometric bound. It transfers the selected source to a literal signed
composite convolution. Its remaining opposite arithmetic bound is open.

## A general filter calculus

For any complex polynomial `P(X) = sum p_k X^k`, define

\[
\Phi_{P,N}(t)=\sum_k p_k\frac{t^{N+k}}{(N+k)!},\qquad
K_{P,N}(s,x)=\Phi_{P,N}(\log x)e^{-s\log x}.
\]

`hasDerivAt_zetaPrimeFilterKernel` and
`hasDerivAt_mul_zetaPrimeFilterKernel` prove, for `x>0`,

\[
\partial_x K_{P,N+1}
=\frac{K_{P,N}-sK_{P,N+1}}x,
\qquad
\partial_x[xK_{P,N+1}]
=K_{P,N}-(s-1)K_{P,N+1}.
\]

The coefficients stay coupled. These identities hold for every polynomial,
degree, complex parameter, and moment order. They do not depend on a
numerically selected coefficient family.

The second identity explains exactly what cancelling the pole does to
the continuous density. Put `b_p=(s-1)^(-1)` for `s != 1`, and define the
polynomial by exact division:

\[
Q_{P,s}=-b_p\bigl(P\mathbin{/_{\rm monic}}(X-b_p)\bigr).
\]

`zetaPoleCancelPolynomial_primitive` proves the general identity

\[
Q_{P,s}-(s-1)XQ_{P,s}=P-P(b_p).
\]

Consequently, whenever `P(b_p)=0`,

\[
\boxed{K_{P,N}(s,x)=\partial_x[xK_{Q_{P,s},N+1}(s,x)].}
\]

`zetaPrimeFilterKernel_integral_eq_primitive` proves the corresponding
finite integral identity with genuine integrability. The theorem
`zetaRightHalfZeroModeFilter_eval_pole` discharges the pole condition for
the actual filter of every hypothetical right-half zero.

## Exact Abel transport and independent error control

Use the already retained band endpoints

\[
a_N=\exp(N\log2/4),\qquad b_N=2^{32N}.
\]

`zetaPrimeLogBand_eq_Ioc` verifies the exact floor convention: the
integers in the band are precisely `floor(a_N) < n <= floor(b_N)`.
For `s=3/2+iy`, the literal prime band is

\[
B_{P,N}(y)=\sum_{a_N<p\le b_N\atop p\ {m prime}}
 (\log p)K_{P,N}(s,p).
\]

Define the complete complex integral

\[
E_{P,N}(y)=\int_{a_N}^{b_N}K'_{P,N}(s,x)(x-\theta(x))\,dx.
\]

`zetaOrdinaryPrimeBandFilter_sub_integral` gives the exact relation

\[
B_{P,N}-E_{P,N}
=\int_{a_N}^{b_N}K_{P,N}(s,x)\,dx
 +K_{P,N}(s,b_N)(\theta(b_N)-b_N)
 -K_{P,N}(s,a_N)(\theta(a_N)-a_N).
\]

All terms are retained as complex values before bounding the error.
Write

\[
C(P)=\sum_k|p_k|(4^{-k}+4^k).
\]

`norm_zetaPrimeBand_endpoints_le` proves, uniformly in `y`,

\[
|b_NK_{P,N}(s,b_N)|+|a_NK_{P,N}(s,a_N)|\le2^{-N}C(P).
\]

The actual elementary bound `theta(x) <= log(4) x`, together with
nonnegativity of `theta`, bounds the two Abel boundary terms. For a
pole-annihilating `P`, the explicit primitive bounds the continuous
integral by the same endpoint estimate applied to `XQ`. Thus
`norm_zetaOrdinaryPrimeBandFilter_sub_chebyshevIntegral_le` proves

\[
\boxed{|B_{P,N}(y)-E_{P,N}(y)|
\le2^{-N}\{C(XQ_{P,s})+(\log4+1)C(P)\}.}
\]

This is an independent estimate on the actual discrepancy, with no zero
hypothesis and no assumed bound on `theta(x)-x`. The polynomial condition
only cancels the known pole. For fixed `P,y` the entire error tends to zero
even before source normalization. The primitive's coefficients depend on
`s`; no uniform conditioning bound in `y` is asserted for this last constant.

## The resulting property of every hypothetical off-critical zero

For an actual nontrivial zero `rho=beta+i gamma`, with `beta>1/2`, let
`u=3/2-beta` and use its mathematically defined local-divisor filter `P_rho`.
The existing prime-band source limit now gives

\[
\boxed{u^{N+1}E_{P_\rho,N}(\gamma)\longrightarrow-m(\rho).}
\]

This is `tendsto_zetaRightHalfPrimeBandChebyshevIntegral`. The theorem
`zetaRightHalfPrimeBandChebyshevIntegral_eventually_negative` proves

\[
\Re E_{P_\rho,N}(\gamma)<-\frac{m(\rho)}{2u^{N+1}}
\quad\hbox{for all sufficiently large }N.
\]

The limit is pointwise for each selected zero, with its true analytic
multiplicity. There is no ordinate restriction and no claimed effective
uniform starting order.

The exact real channel is also exposed. At order `N+1`, its integrand is

\[
\frac{\Re K_{P,N}-\tfrac32\Re K_{P,N+1}
       +y\Im K_{P,N+1}}x\,(x-\theta(x)).
\]

`zetaPrimeBandChebyshevIntegral_re_lowering` verifies this identity for
the actual integral. In particular the imaginary channel is weighted by
the ordinate; discarding it changes the signed quantity we must control.

## A proved obstruction to automatic positivity

Conjugate pairing of polynomial coefficients does not by itself preserve
positivity through factorial weighting. For every order `N`, Lean proves

\[
\Phi_{(1-X)^2,N}(N+1)=-\frac{(N+1)^N}{N!(N+2)}<0.
\]

The exact value and strict real sign are
`zetaFactorialPolynomial_square_exact` and
`zetaFactorialPolynomial_square_re_neg`. The polynomial `(1-t)^2` is
nonnegative for real `t`, but its factorial transform is not. This refutes
a general positivity shortcut; it does not show that every specially
constructed paired filter fails.

## The next mathematical obligation

An independent lower estimate for the signed integral must beat the
negative source. For example, for each hypothetical zero it would suffice
to show its normalized real integral is at least `-m(rho)/2` for infinitely
many orders. A full power-saving estimate is not required.

The new interface locates this obligation in the correlation between the
actual prime discrepancy and the two coupled filter channels. The endpoints,
continuous pole background, proper prime powers, and exterior prime tails
cannot carry the missing source. Available norm estimates on the whole
central carrier have not supplied the needed opposite inequality. The next
attack should use signed prime structure inside this integral, rather than
further sharpening its already negligible boundaries.

## Local validation

The four new modules are imported from `RiemannGaussian.lean`. All direct
checks with warnings as errors passed, as did the focused build (4,281 jobs),
full build (9,800 jobs), whole-project declaration lint, and source and
whitespace scans. A root-import audit covered all 44 new public theorems:
their only axiom dependencies are `propext`, `Classical.choice`, and
`Quot.sound`. Work remains local under the user's hold on commits; no remote
CI result is claimed.
