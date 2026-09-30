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
