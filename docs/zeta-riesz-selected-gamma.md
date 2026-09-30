# Exact inversion of the selected shifted resonance

The selected resonance now has an exact physical-space formula in Lean.
It is **not bounded to zero**, and no new joint floor, ceiling or zero
exclusion is claimed. The source remains present.

For `u>0`, positive marked order `j`, and real frequency `xi`,
`ZetaRieszSelectedGamma.selected_shiftedMark_eq_laplace` proves

\[
u^j\operatorname{shiftedMark}(-u,j,\xi)
=\frac1j\int_0^\infty\Gamma_{j,u}(t)e^{-i\xi t}\,dt,
\qquad
\Gamma_{j,u}(t)=\frac{u^jt^{j-1}e^{-ut}}{(j-1)!}.
\]

The density is nonnegative, integrable and has mass one. The integral
identity is proved for complex damping with positive real part; no
frequency or Gamma approximation is used.

## The actual finite quotient

Write `f_p(s)=p^(-s)` and `E_p(xi)=p^(-i*xi)`. The existing ordered
cofactor's middle product has the exact expansion

\[
\prod_{p\in Q}\frac{1-f_p(s)E_p(\xi)}{1-f_p(s)}
=\sum_{U\subseteq Q}
 \left(\prod_{p\in U}\frac{f_p(s)}{1-f_p(s)}\right)
 \prod_{p\in U}(1-E_p(\xi)).
\]

For a least prime `r` and a nonempty subset `U` of the larger primes,
put `a=r*prod(U)` and `k=N+1-j-h`. Define the exact complex weight

\[
W_{N,j,h}(r,U;s)=K_h(s,r)\,
 \operatorname{signedTaylorMoment}_k
 \left(\prod_{p\in U}\frac{p^{-s}}{1-p^{-s}}\right)(s).
\]

The literal rectangle forces `k>0`, so the empty middle subset is zero.
No other factorial order is deleted. The physical response is

\[
\mathcal R_{N,j,h}(x;s)=
 \sum_{(r,U)\in\operatorname{indices}(A)}
 W_{N,j,h}(r,U;s)\,R_x(r\textstyle\prod U).
\]

`ZetaRieszSelectedCofactor.selected_atom_fourier_eq_physical` proves that
the original paired selected atom, multiplied by `-u^j/(2*pi)`, is
exactly

\[
\frac1j\int_0^\infty\Gamma_{j,u}(t)
 \mathcal R_{N,j,h}(L-t;s)\,dt.
\]

This keeps the original finite prime set, least-prime ordering, rectangle,
correlated total order, full phase, Euler denominators and moving length.
The cofactor is not completed. Two Fourier zeros give genuine absolute
integrability for Fubini; the arithmetic sum is not replaced by its norm.
The translated response is explicit, rather than another unspecified
Fourier integral. For each composite label `a` it vanishes exactly outside
`L-log(a)<t<L`, including both endpoints.

## Entire selected response and the joint ledger

Let `S_N` be the selected shifted response with the repository's original
positive prefactor `(N+1)/(2*pi*L)`. Define

\[
\mathcal A_N=
\sum_{j\in\operatorname{range}(N+2)}
\sum_{h\in\operatorname{rectangleOrders}(N,j)}
\frac{u^{N+1-j}}j\int_0^\infty
\Gamma_{j,u}(t)\mathcal R_{N,j,h}(L-t;s_0)\,dt.
\]

`selectedResponse_eq_gamma_average` proves exactly

\[
u^{N+1}S_N=-\frac{N+1}{L}\mathcal A_N.
\]

The residue sign agrees with the existing
`ZetaRieszUnshiftedPayment.selected_principal_split`: the selected moment
has negative residue, while `shiftedMain` negates the complete shifted
moment. Its contribution to that main is therefore `+m*S_N`.
`joint_real_eq` retains any unchanged complex complement `C`:

\[
\Re\bigl(u^{N+1}(mS_N+C)\bigr)
=\Re(u^{N+1}C)-\frac{m(N+1)}L\Re\mathcal A_N.
\]

This identity does not declare all other channels paid. Existing channel
reductions and their hypotheses must still be applied in their proved
scopes. In particular, an endgame floor needs an **upper** bound on this
correlated physical average relative to the signed complement. Kernel
positivity alone supplies neither whole-sum bound.

## Fixed-atom and cross-count numerical checks

The optional script `scripts/probe_riesz_selected_gamma.py` uses
`N=100,j=55,h=1,u=10001/20000` and the exact repository length
`2*log(floor(u^(-N)/(N+1))+2)`, approximately `129.37919607824`.
For least prime `17` and middle prime `23`, the normalized physical value
before the complex coefficient is `0.00216574466881`. Direct Fourier
quadrature agrees to the working precision. Lean proves the equality
independently of this numerical test.

The two-prime physical factor is nonnegative: it is a Gamma average of
the exact compact two-prime tent. The arithmetic coefficient still has
both signs in real part. For example its real part divided by its norm
is about `-0.99654` at height `60`, and `+0.59807` at height `100`.
These heights are not asserted to be hypothetical zeros.

The finite all-count check uses `A={17,23,29,31,37}` and every nonempty
middle subset. At height zero the cofactor-count contributions, in units
of `1e-12`, are approximately:

| Cofactor prime count | Real contribution |
| --- | ---: |
| 2 | +1.85271 |
| 3 | -4.05561 |
| 4 | +0.00037 |
| 5 | +0.37237 |
| Total | -1.83017 |

Even before arithmetic phase is introduced, averaged higher-count Riesz
kernels need not be nonnegative. In this test the four-prime kernels have
both signs. Thus there is no numerical basis for assigning a favorable
sign to each count separately. The result points to a bound for the
**joined weighted physical sum**, with the complement retained.

These are finite diagnostic computations, not a source-normalized
cofinal bound, full-prime computation, certificate or obstruction theorem.
The full output is in `riesz-selected-gamma-probe.json`. Run locally with
`../.venv/bin/python scripts/probe_riesz_selected_gamma.py`; it is not part
of ordinary CI.

## Checked proof endpoints

- `ZetaRieszSelectedGamma.complex_factorial_laplace`
- `ZetaRieszSelectedGamma.integral_gammaKernel`
- `ZetaRieszSelectedPhysical.gamma_pair_integrable`
- `ZetaRieszSelectedPhysical.selected_cofactor_two_primes_eq_gammaTent`
- `ZetaRieszSelectedPhysical.gammaTent_bounds`
- `ZetaRieszSelectedCofactor.selected_atom_fourier_eq_physical`
- `ZetaRieszSelectedCofactor.selectedResponse_eq_gamma_average`
- `ZetaRieszSelectedCofactor.physical_atom_eq_zero_outside`
- `ZetaRieszSelectedCofactor.joint_real_eq`

The independent joint `-79/1000-o(1)` floor and `3/2+o(1)` ceiling remain
open. This slice provides the requested exact physical object on which
to seek them, with integrability and signs audited.

## Gamma/count collapse and the actual complement

The local continuation proves exact recombination at common arithmetic
coordinates, an all-count finite Euler identity, and a geometric payment
for the literal marked order-zero boundary. It does **not** prove the
virtual-to-literal marked-prime transfer or either joint endgame inequality.

Write `M=N+1`, `a=log r`, `b` for the middle log mass, and `T=t+a+b`.
`ZetaRieszGammaCollapse.gamma_factorial_collapse` gives

\[
\frac{u^{M-j}}j\Gamma_{j,u}(t)
=u^M e^{-ut}\frac{t^{j-1}}{j!}.
\]

`rectangle_factorial_collapse` sums the exact three factorial slots:

\[
\sum_{j,h\in\mathrm{rectangle}}
\frac{t^ja^hb^{M-j-h}}{j!h!(M-j-h)!}
=\frac{T^M}{M!}\Theta_N(t,a,b).
\]

Here `continuousRectangleMass` is exactly the existing `rectangleMass`
with conditional shares `(a+b)/T` and `a/(a+b)`. It lies in `[0,1]`
for nonnegative log coordinates with `a+b>0`. All original integer
rectangle endpoints remain. `selectedResponse_eq_collapsed_integral`
puts every marked and least order inside one signed physical integral
after this Gamma normalization is cancelled.

### All middle counts joined by a finite Euler identity

Set `q_p=p^(-s)` and `H_r(d)=(d)_+-(d-log r)_+`. Lean proves

\[
\sum_{\varnothing\ne U\subseteq Q}
\left(\prod_{p\in U}\frac{q_p}{1-q_p}\right)
R_d\left(r\prod_{p\in U}p\right)
=
\left(\prod_{p\in Q}(1-q_p)^{-1}\right)
\sum_{V\subseteq Q}(-1)^{|V|}
\left(\prod_{p\in V}q_p\right)H_r\left(d-\sum_{p\in V}\log p\right)
-H_r(d).
\]

This is `ZetaRieszAllCountBoundary.all_count_riesz_eq`. It follows
from `sum_odds_difference`, an exact finite subset identity for any
complex test function. The final prime hinge is the empty-middle
correction; it is retained. There is no infinite Euler-product inverse.
`boundary_moment_eq` proves that the equality commutes with the actual
signed Taylor moments, including order zero.

Consequently `physicalCofactor_eq_eulerBoundary` replaces all nonempty
middle subsets/counts by one signed boundary response per least prime:

\[
\mathcal R_{N,j,h}(d;s)
=\sum_{r\in A}K_h(s,r)\,
\operatorname{signedTaylorMoment}_{M-j-h}
\bigl(\mathcal B_{r,\{p\in A:p>r\}}(\cdot,d)\bigr)(s).
\]

Every Euler denominator, least-prime ordering and phase survives. This
is the finite-Euler alternative to an infinite middle-integer expansion.
No subset or count is assigned a separate positive allowance.

### Where the literal complement really matches

`ZetaRieszGammaComplement.selection_eq_continuous` identifies the
current literal selection on **all of fullBand** with

\[
\Theta_N(\log p,\log r,\log n-\log p-\log r),
\qquad p=\operatorname{largestPrime}(n),\quad r=\min\operatorname{Fac}(n).
\]

`selection_complement_eq` identifies `1-selection` with the exact
complementary factorial antidiagonal. This requires no old fixed
least-share box and no deletion of individual small factorial orders.

For a squarefree composite cofactor `a=n/p`, saturation `log a<=L`
gives `R_L(a)=0`. Hence the actual atom is

\[
c_L(n)K_N(s_0,n)=\frac{M}{L}R_{L-\log p}(a)K_M(s_0,n).
\]

`literal_complement_atom_translated` keeps both `1-selection` and
`1-boundedShare` in this equality. On the core upper window
`log n<=203N/100`, `L>=11N/8` and `log p>=log n/3` suffice for
saturation (`cofactor_saturated_on_core`).

Let `D_N` be exactly those labels in the current fullBand with saturated
canonical cofactor, and put

\[
F_N(n)=\frac{M}{L}(1-\mathrm{boundedShare}(n))
R_{L-\log p}(n/p)K_M(s_0,n).
\]

The checked `rest_physical_ledger` is

\[
C_N=\sum_{n\in D_N}(1-\Theta_N(n))F_N(n)+B_N,
\]

where `B_N` is the **original signed complementary sum** over
`coreBand \ D_N`. Its exact masks are retained: outside fullBand, or
an unsaturated canonical cofactor. It is not declared negligible.
`joint_matched_ledger` then gives the exact requested residual:

\[
mS_N+C_N=\sum_{n\in D_N}F_N(n)+B_N+\Delta_N,
\qquad
\Delta_N=mS_N-\sum_{n\in D_N}\Theta_N(n)F_N(n).
\]

The Theta fractions therefore cancel exactly on a common literal
label. They do **not** change the discrete marked-prime measure into
the selected continuous density. That remaining signed discrepancy
is `Delta_N`; the Gamma/all-count identity explicitly evaluates its
selected part. No source-o(1) bound is proved for `Delta_N` or `B_N`.
This difference retains any allocation, Euler-power and support
discrepancies not already transferred in their proved scope; it is not
asserted to be a bare prime-density error.
Other shifted spectral channels must also stay in the exact ledger
unless their removal is justified by an existing theorem in its scope.

### A boundary that is genuinely paid

The full positive marked-order mass is `1-((a+b)/T)^M`, rather than
one. The exact factorial sum is

\[
\sum_{j=1}^{M}\sum_{h=0}^{M-j}
\frac{t^ja^hb^{M-j-h}}{j!h!(M-j-h)!}
=\frac{T^M-(a+b)^M}{M!}.
\]

This is `positive_factorial_collapse`. After division by `t`, the
numerator retains its exact zero-order subtraction.

For the literal arithmetic boundary, `zeroOrder_literal_bound` proves

\[
\left\|u^M\sum_{n\in D}
(1-\log p_n/\log n)^M
\operatorname{residualCoefficient}(n)K_N(s_0,n)\right\|
\le (9/10)^N\operatorname{zetaMoebiusLogMajorantMass}(9/8)
\]

whenever `0<=u<=10001/20000`, `1/3<=log p_n/log n<=1`, and `L>0`.
The finite mask `D`, physical allocation and phase are unchanged;
the height may move. `tendsto_zeroOrder_literal` proves source-o(1).
This is a concrete geometric boundary saving, **not** a bound for the
main signed carrier or the virtual Gamma zero-order term. Middle
orders zero and one are never deleted.

### Finite matching regression

`scripts/probe_riesz_gamma_join.py` is optional and stays outside CI.
It uses `N=320`, the literal length and Mersenne prime factors with
exponents `19,61,89,107,127,521`. Its mask model explicitly records
the core window, count, nondominance, physical-prime and cancelling
sector checks. Earlier adaptive deletions at this small order are not
certified, so this is **not** a numerical evaluation of coreResponse.

The matched five- and six-prime labels have rectangle masses about
`0.001471419` and `0.544941133`. Their complementary fractions add
to one, their saturated unshifted hinges vanish, and the translated
complement identity agrees to working precision. The separate finite
all-count Euler check has residual about `1e-75` at 75-digit precision.
The selected Gamma expression and the arithmetic mask model are
deliberately not assumed equal. Their difference also includes radial
masks and Euler proper powers; the probe does not attribute the whole
difference to one cause or certify any cofinal saving.

Output: [finite matching diagnostics](riesz-gamma-join-probe.json).

### Recombination with the whole shifted response

[ZetaRieszGammaJoint.lean](../RiemannGaussian/ZetaRieszGammaJoint.lean)
now removes the unsaturated **selected** boundary independently. On the
core, if `log(n/largestPrime n)>L` and `L>=11N/8`, the largest-prime
share is below `1/3`. In particular this cannot happen to a three-prime
label in fullBand. The original factorial rectangle has

\[
\Theta_N(n)\le 3e^{-N/16}
\]

there (`weight_small_mark`). Combining this with the original coefficient
and kernel bounds gives the checked estimate

\[
\left\|u^{N+1}\sum_{n\in\mathrm{fullBand}\setminus D_N}
  \Theta_N(n)\,\operatorname{residualCoefficient}(n)K_N(s_0,n)\right\|
\le 2(19/20)^N\operatorname{zetaMoebiusLogMajorantMass}(257/256).
\]

This is `unsaturatedPacket_bound`. It is uniform in height and retains
the old allocation and all finite masks. Its length premise holds
eventually for `0<u<=10001/20000`. The summable majorant is a fixed
constant. The same bound applies to the difference between coreResponse
and the following existing physical expression (`core_joined_bound`):

\[
\mathcal P_N=\sum_{n\in D_N}F_N(n)+B_N.
\]

The original signed boundary `B_N` is still present with its original
complementary weights. This theorem does **not** bound `B_N` by the
selected-rectangle tail.

`tendsto_joint_sub_joined` combines this estimate with the already paid
literal errors to prove, independently of any zero hypothesis,

\[
u^{N+1}\bigl(J_N+C_N-\mathcal P_N\bigr)\longrightarrow0.
\]

The theorem permits arbitrary moving counts and heights along orders
tending to infinity. Under the original exposed-zero hypotheses,
`tendsto_shifted_joint_sub_joined` also proves

\[
u^{N+1}\bigl(\mathrm{shiftedMain}_N+C_N-\mathcal P_N\bigr)
\longrightarrow0
\]

along the original dyadic schedule, with **no simplicity assumption**.
Every remaining shifted channel is retained.

More precisely, `selected_discrepancy_eq_joint` identifies

\[
\Delta_N+\bigl(\mathrm{shiftedMain}_N-mS_N\bigr)
=\mathrm{shiftedMain}_N+C_N-\mathcal P_N.
\]

Thus the selected-to-literal discrepancy and the other shifted channels
cancel in this joined comparison. Neither is asserted small separately.
This uses the proved transfer of the **whole** shifted expression; it
does not infer a masked selected-mode limit from complete-leg limits.

The remaining arithmetic target is now a signed bound on
`sum F_N + B_N` together. The rectangle has full mass in the matched
sum, while the precise unmatched masks remain in `B_N`. No independent
`-79/1000-o(1)` floor or `3/2+o(1)` ceiling has yet been proved for that
joint expression. Its existing nonzero source is unchanged.
