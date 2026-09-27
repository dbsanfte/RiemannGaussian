# A largest-prime gap bound for every four-prime term

[`ZetaRieszFourPrimeFloor`](../RiemannGaussian/ZetaRieszFourPrimeFloor.lean)
proves an independent signed inequality for the **whole four-prime class**
of the original core. It is not limited to the preceding compensating
grid, the old reflected-linear class, or primes above `sqrt(n)`.
It introduces no new carrier and assumes no zero or prime-density model.

Write `T=log n`, `P=largestPrime n` and

\[
g_L(n)=\log P+T-2L.
\]

For any actual integer with exactly four distinct prime factors, if
`0<L<=T` and `2T<=3L`, `actual_four_signed_gap` proves

\[
\boxed{
-\frac{T}{L}\max(0,-g_L(n))
\ \le\ \Re c_L(n)\ \le\
\frac{T}{L}\max(0,g_L(n)).
}
\]

Nonsquarefree integers have zero coefficient, as in the original
definition. `coefficient_four_sign` proves `g_L(n)*Re(c_L(n))>=0`.
`coefficient_four_eq_zero_at_gap` proves the complete coefficient is
exactly zero when `log P+T=2L`. The sign statement is **weak**: coefficients
can also vanish away from that transition.

## Why the inequality holds

Reflect the complete signed divisor sum to `D=T-L`. Four-prime Möbius
parity is positive, so this preserves the Riesz response.

If `log P>=D`, inserting the largest prime has a nonpositive shifted
cutoff and contributes zero there. The response is exactly the
three-prime cofactor's Riesz response at `D`. The cofactor midpoint is
`(T-log P)/2`; its distance from `D` is precisely half the displayed gap.
`riesz_three_signed_gap` bounds both signs using the previously proved
three-prime reflection and midpoint estimates.

If `log P<=D`, every prime log is at most `D`. Since `3D<=T`, every
two-prime divisor has log at least `D`; only the unit and single primes
contribute. The exact four-prime response is `T-3D=3L-2T`.
It obeys the same signed gap bounds. No cofactor is completed and no
subset sign is omitted in either case.

## The literal core and phase remain

On the restricted radius interval `1/2<u<=10001/20000`, the proved
eventual length bounds and unchanged core window are

\[
137N/100\le L\le7N/5,\qquad39N/20<T\le203N/100.
\]

They imply all the hypotheses above. `gap_transition_bounds` also proves

\[
\frac{71}{203}T\le2L-T\le\frac{17}{39}T.
\]

Thus the exact sign boundary depends on the actual moving `L/T`; it must
not be replaced by a frozen `T=2N` boundary. In particular, the previous
sign theorem requiring a prime above half the total log covered only a
part of the now-controlled class.

Let `w_N(n)` be the original nonnegative factorial weight, including
`1-boundedShare`, and let `f_N(n)` be the actual complex residual atom.
`re_four_atom_ge_keep_positive` proves

\[
\boxed{
\Re f_N(n)\ge
\max(\Re f_N(n),0)
-w_N(n)\frac{T}{L}\max(0,-g_L(n)\cos(yT)).
}
\]

Every actual positive contribution is kept. The debit charges only an
opposite-sign gap and cosine. It vanishes identically on favorable
observations (`re_four_atom_nonneg`) and at the exact sign transition.
This sharpens sign information, not every earlier amplitude bound in
every configuration.

The terminal `eventually_re_core_ge_four_credit` applies this inequality
to **all** four-prime core labels, uniformly in the height and count
endpoint. It leaves the sum over every other prime count signed and
unchanged, and retains the positive four-prime contributions in the same
source-normalized lower bound. There is no new error term from this
comparison. The displayed adverse-phase budget is still unpaid; a
source-scale floor for the whole joint expression remains open.

## Capacity diagnostic and next obstruction

The preceding [actual compensation theorem](zeta-riesz-quadruple-compensation.md)
pays one fixed-width triple box using a four-prime population. The optional
[capacity probe](../scripts/probe_riesz_joint_capacity.py), with
[output](riesz-joint-capacity-probe.json), checks whether merely enlarging
that population appears sufficient for the full triple class.

It samples only `T=2N`, replaces prime measures by ordinary densities,
retains the model's binomial allocation, and includes only primes above
`N^2` and counts three through nine. It does not estimate omitted small
primes, larger counts, radial transport or the actual fixed-height sum.
Positive and negative columns refer to **coefficient** sign, before
observing a cosine. None of these numerical data enter the Lean proofs.

At `N=65536`, one sample gives:

| Prime count | Positive coefficient mass | Negative coefficient mass |
| --- | ---: | ---: |
| 3 | 0.68994 | 0 |
| 4 | 0.19801 | 0.02902 |
| 5 | 0.00629 | 0.43133 |

The common radial factors are omitted from this diagnostic. It suggests
that favorable four-prime terms alone cover only a small fraction of
the full triple mass on a negative-cosine slice, while five-prime terms
are substantial. This is **not** a proved arithmetic capacity obstruction.
Higher-count samples are visibly less stable, and there is no omitted
count-tail bound. The probe is optional and outside ordinary CI.

The next joint estimate must retain the unused positive credit from the
existing compensation, the new signed four-prime debit, and the other
prime-count classes together. Neither a four-prime sign theorem nor a
density-model surplus closes the cofinal `-79/1000-o(1)` target. No new
zero exclusion is claimed.

### The five-prime follow-up

A scalar probe suggested the following five-prime upper bound, now
proved by the subsequent slice. If `P>Q` are the two largest primes of
a squarefree label, `T=log n` and `2T/3<=L<=3T/4`, then

\[
\Re c_L(n)\ \le\ \frac{T}{L}
\max\bigl(0,\min(2\log P+T-3L,
\log P-\log Q+T-2L)\bigr).
\]

It confines positive five-prime coefficients to the simultaneous
inequalities `2*log P+T>3L` and `log P-log Q+T>2L`, directly targeting
their adverse negative-cosine contribution on the existing coefficient.

Testing 300,000 sorted Dirichlet(1,...,1) five-share samples with
`L/T` uniform in `[2/3,3/4]` (NumPy seed `519`) found a maximum apparent
upper-bound violation of `8.9e-16`, consistent with floating-point
roundoff. These samples do not prove it. They also found no positive
coefficient when the largest share is below the reflected cutoff.

The subsequent [five-prime slice](zeta-riesz-five-prime-floor.md) now proves
this inequality in Lean, including the central four-prime and all-small
five-prime chambers. It also caps the upper allowance by three least-prime
logarithms and applies the combined four/five-prime comparison to the
literal core, retaining all positive credit and signed complements. Its
aggregate source-scale debit and the whole joint floor remain open.

The subsequent [four-prime reserve slice](zeta-riesz-four-prime-reserve.md)
now evaluates the negative coefficient exactly using the excess of every
prime log above `T-L`. Its phase debit is pointwise no larger than the gap
debit here. The sharpened four/five-prime comparison is combined with the
radial triple compensation on the untouched complement, without spending
any supply twice. The whole joint numerical floor remains open.
