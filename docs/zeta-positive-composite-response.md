# A positive arithmetic convolution with a universal signed zeta source

The signed composite Möbius coefficients become nonnegative after one
complete logarithmic convolution. Their actual Dirichlet series represents
one fixed function of zeta, independent of any selected zero or phase
optimiser. At every nontrivial zero with real part greater than one half,
this function has a double pole with coefficient exactly `-m^2`, where `m`
is the zero's genuine analytic multiplicity. The unknown leading zeta
phase cancels.

This is a structural theorem and an arithmetic inequality for actual
zeta. It supplies no new zero exclusion yet. Literature priority has not
been established; the proof uses Mathlib's Möbius inversion and
von-Mangoldt identities.

## The complete signed convolution

Write `*` for Dirichlet convolution, `1` for the constant arithmetic
function on positive integers, and define

\[
a(n)=\begin{cases}0&n\text{ prime},\\\mu(n)\log n&\text{otherwise},\end{cases}
\qquad r(n)=\mathbf1_{n\text{ prime}}\log n,\qquad L(n)=\log n.
\]

The previous literal Möbius coefficient is unchanged:
`zetaMoebiusCompositeArithmetic_cast` identifies it exactly. Möbius
inversion gives

\[
D=1*a=1*r-\Lambda,\qquad
D(n)=\sum_{p\mid n}\log p-\Lambda(n)\ge0.
\]

Theorems `zeta_mul_compositeArithmetic`,
`zetaMixedPrimeArithmetic_apply`, and `zetaMixedPrimeArithmetic_nonneg`
prove the exact divisor identity and its sign. At a prime power, the
prime base already accounts for the von-Mangoldt term. At every other
integer the von-Mangoldt term is zero, and the divisor sum is nonnegative.

Because `L=Lambda*1`, the same identity yields

\[
\boxed{B=L*a=\Lambda*D\ge0\quad\text{coefficient by coefficient}.}
\]

These are `zetaPositiveCompositeArithmetic_eq` and
`zetaPositiveCompositeArithmetic_nonneg`. The signed finite convolution
remains available in `zetaPositiveCompositeArithmetic_convolution`.
Adding the second logarithmic convolution also preserves nonnegativity,
by `zetaDoubleLogCompositeArithmetic_nonneg`. No absolute value replaces
the original Möbius sum in these equalities.

## The fixed zeta function and its poles

Let `h=zeta'`, `ell=zeta'/zeta`, and let `E` be the existing proper-prime-power
series, proved analytic throughout `Re s>1/2`. Define

\[
T(s)=-h(s)\left(\frac{h(s)}{\zeta(s)^2}-\ell(s)-E(s)\right).
\]

The actual arithmetic identity is

\[
\boxed{T(s)=\sum_{n\ge1}B(n)n^{-s}\qquad(\Re s>1).}
\]

`LSeriesHasSum_zetaPositiveCompositeResponse` proves genuine absolute
convergence and equality, using the existing differentiated reciprocal
series. `zetaPositiveCompositeResponse_eq` retains the exact decomposition

\[
T=-\ell^2+h\ell+hE.
\]

At a zero `rho` of multiplicity `m>=1`, `ell` has coefficient `m` at its
simple pole. The other two terms have strictly smaller singular order
than `ell^2`. Consequently,

\[
\boxed{\operatorname{ord}_{\rho}T=-2,\qquad
\lim_{s\to\rho}(s-\rho)^2T(s)=-m^2.}
\]

The limit is punctured. The compiled statements are
`meromorphicOrderAt_zetaPositiveCompositeResponse`,
`meromorphicTrailingCoeffAt_zetaPositiveCompositeResponse`, and
`tendsto_zetaPositiveCompositeResponse_mul_sq`. They apply to every
nontrivial `rho` with `Re rho>1/2`, without a simplicity assumption.
`meromorphicTrailingCoeffAt_logDeriv_of_order` proves the phase
cancellation for a general meromorphic function of finite nonzero order.

The pole at one remains present:

\[
\operatorname{ord}_{1}T=-3,\qquad\operatorname{lead}_{1}T=1.
\]

Both `_one` order and trailing-coefficient theorems check this explicitly.
Coefficient positivity therefore cannot be interpreted as analyticity
past the real abscissa at one.

## All moments and arbitrary complex probes

Put `M_k(f)=(-1)^k f^(k)/k!` and `b_k(n)=B(n)(log n)^k/k!`. Every `b_k(n)`
is nonnegative, and `hasSum_zetaPositiveCompositeMoment` proves

\[
M_k(T)(s)=\sum_n b_k(n)n^{-s}\qquad(\Re s>1).
\]

For any finite collection of complex probes `s_i` with `Re s_i>1/2`, and
arbitrary complex coefficients `c_i`, the complete mixed identity is

\[
\boxed{\sum_{i,j}\overline{c_i}c_j
 M_k(T)(\overline{s_i}+s_j)
 =\sum_n b_k(n)\left|\sum_i c_i n^{-s_i}\right|^2.}
\]

`hasSum_zetaPositiveCompositeMomentGram_energy_complex` proves this as a
genuinely convergent complex series, before taking its real part.
`zetaPositiveCompositeMomentGram_energy_nonneg` is the downstream
nonnegative-energy theorem. Every cross term, unequal real part, and
complex coefficient remains available. There is no prescribed frequency
count or optimiser family. The arguments of `T` in this identity have
real part greater than one; the theorem does not extend Gram positivity
by meromorphic continuation through zeros.

The scalar consequence, `norm_zetaPositiveCompositeMoment_le_real`, is

\[
|M_k(T)(\sigma+it)|\le M_k(T)(\sigma)\qquad(\sigma>1).
\]

The real right-hand side is nonnegative. The order-zero theorem
`norm_zetaPositiveCompositeResponse_le_real` applies directly to `T`.

## Connection to the existing source and the open step

The subsequent [prime-colour coupling](zeta-prime-colour-cancellation.md)
proves disjoint support, the exact factorization `T=F V`, and geometric
decay of the common prime/mixed-prime moment after removing its pole at
one. It also retains the complete quadratic form and its nonzero zero
source. The linear common sum cancels that source, so its bound is not
the missing contradiction.

For the previous composite Wronskian `Q_rho`, the exact bridge is

\[
Q_\rho(s)=\frac{-\zeta'(s)}{(s-\rho)^{m-1}}T(s).
\]

`zetaMoebiusCompositeWronskian_eq_positiveResponse` proves it pointwise.
The full filtered moments use the cofactor
`A_rho=-W_rho*zeta'/(s-rho)^(m-1)`.
`hasSum_zetaWronskianCompositeMoment_positive` transports them to the
nonnegative coefficients `B(n)` while retaining every derivative of
`A_rho` in their exact complex kernel. Their
[proved source and error allowance](zeta-wronskian-global-moments.md)
therefore apply to this same convergent arithmetic sum.

The remaining task is an independent signed inequality for that whole
filtered kernel, or a new construction using the fixed response's mixed
energies that handles the pole at one and contradicts a right-half zero.
`B(n)>=0` does not imply that an arbitrary complex, pole-clearing filter
has a nonnegative sum. The Euler norm bound also retains the real pole at
one. Neither result presently supplies the independent bound needed for RH.

## Local verification

The three modules `ZetaMoebiusConvolutionPositivity`,
`ZetaPositiveCompositeResponse`, and `ZetaPositiveCompositeMoments` are
imported by the root library. Validation covers direct warnings-as-errors
elaboration, focused and full builds, whole-project declaration lint,
root-imported module lint, all public-theorem axiom checks, and source and
whitespace checks. Work remains local under the user's commit hold.
