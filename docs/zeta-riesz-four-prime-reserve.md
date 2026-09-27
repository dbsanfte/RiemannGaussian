# Exact four-prime negative part inside the joint floor

The subsequent [five-prime reserve theorem](zeta-riesz-five-prime-reserve.md)
uses this identity on the largest-prime cofactor. It makes the five-prime
negative-cosine debit exact in the joint comparison below as well.

[`ZetaRieszFourPrimeReserve`](../RiemannGaussian/ZetaRieszFourPrimeReserve.lean)
sharpens the one-sided bound for **every four-prime core label** and combines
it with the paid balanced triple band. No carrier, completion, zero
hypothesis or prime-density approximation is introduced. The full cofinal
`-79/1000-o(1)` floor for `J_N+C_N` remains open; no zero exclusion follows.

## Exact arithmetic debit

For a squarefree four-prime integer, write `T=log n`, `D=T-L` and

\[
F_L(n)=3L-2T-\sum_{p\mid n}(\log p-D)_+,
\qquad x_+=\max(0,x).
\]

If `0<L<=T` and `2T<=3L`, `negativeAllowance_eq` proves

\[
\boxed{\max(0,-\Re c_L(n))=\frac{T}{L}\max(0,F_L(n)).}
\]

Nonsquarefree labels have zero coefficient and zero allowance. Small
primes, hinge equalities and the moving length are all included.
`negativeAllowance_le_gap` proves this exact debit never exceeds the old
`(T/L)*max(0,2L-T-log P)`, where `P` is the largest prime.

The proof retains every divisor hinge. `triple_clipped_sum` identifies
the positive part of the three-leg difference with
`max(0,min(D,a)+min(D,b)+min(D,c)-2D)`. Reflecting the four-prime response
to `D` either reduces to that cofactor identity or leaves only singleton
divisors. `riesz_four_clipped_sum` proves `F_L<=R_L` and `(R_L)_+=(F_L)_+`.
The coefficient identity `c_L=-(T/L)R_L` gives the result. Separately
charging the pair hinges would destroy cancellation used here.

## Original phase and combined compensation

Let `b_-=negativeAllowance L n`, `b_+=(T/L)*(log P+T-2L)_+` and
`x=cos(y*T)`. With `d_4=b_-*x_++b_+*(-x)_+`, Lean proves

\[
\boxed{\Re f_N(n)\ge\max(\Re f_N(n),0)-w_N(n)d_4(n).}
\]

The original weight includes `1-boundedShare`. The inequality is exact
when the cosine is nonnegative (`re_four_atom_eq_keep_positive`).
`fourDebit_le_gap` proves the debit is pointwise no larger than the old
phase debit. No absolute cosine is used; all positive credit remains.

`eventually_re_core_ge_four_five_credit` combines this with the existing
clipped five-prime bound on the original core, uniformly in height and
count endpoint for `1/2<u<=10001/20000`. Other counts and the five-prime
positive-cosine terms stay signed.

`eventually_compensated_core_floor` then applies that comparison only to
the untouched complement of the [radial compensation](zeta-riesz-radial-compensation.md).
For its triple sum `X`, positive supply `Y` and complementary lower
comparison `B_W`, it proves

\[
\boxed{
\Re(u^{N+1}\mathrm{coreResponse})\ge
u^{N+1}\bigl(B_W+\max(\Re X,0)+\Re Y/2\bigr)-Cr^N,
\quad 0\le r<1.
}
\]

This uses fixed `|y|>=16`, available for hypothetical right-half zeros,
and some conservative positive balanced share width. The supply is
excluded before applying the debit, so it is never spent twice. The only
error is the existing radial-edge allowance. The **whole** expression in
parentheses still needs an independent numerical floor; separate decay
of the packet and complement is unnecessary.

## Optional numerical check

The [capacity probe](../scripts/probe_riesz_joint_capacity.py), with
[output](riesz-joint-capacity-probe.json), compares the allowances in the
same density-model samples:

| Order `N` | Sobol seed | Old allowance | Exact negative part |
| --- | --- | ---: | ---: |
| 65536 | 17 | 0.050291 | 0.029023 |
| 65536 | 29 | 0.052416 | 0.028988 |
| 1048576 | 17 | 0.053342 | 0.029258 |
| 1048576 | 29 | 0.061828 | 0.029222 |

These are coefficient-over-`N` density integrals at `T=2N`, omitting common
radial and phase factors. They are **not** bounds for actual prime sums.
Small primes, larger counts, radial transport and certified quadrature
errors are omitted; the old-debit values show sampling sensitivity.
The identity is independently proved in Lean. The probe stays optional
and outside ordinary CI.
