# A fixed positive-five sector paid in the whole joint estimates

The new checked comparison pays actual positive-coefficient five-prime
labels whose four nonlargest prime logarithms lie between `1/10` and `9/80`
of the total logarithm. It applies across a complete central phase period
on every sufficiently large original dyadic moment. The lower and upper
comparisons retain half the old central reserve, every favorable observation
of the newly paid population, and one exact signed complement.

The final whole-sum floor `-79/1000-o(1)` and ceiling `3/2+o(1)` remain open.
This result does not exclude a zero or assume that the selected zero is simple.

## Literal arithmetic estimate

Write `T=log n` and let `p` be the largest prime factor. The new population
is a subset of the original support `S`, with squarefreeness, five prime
factors, positive real arithmetic coefficient, and

```math
\frac{1}{10}T\le\log q\le\frac{9}{80}T
\qquad(q\mid n,\ q\ne p).
```

All four cofactor primes are counted on literal logarithmic prime intervals.
Their reciprocal masses are each at most `63/500`. The last-prime interval
is `(t-log(cofactor),t-log(cofactor)+h]`; it is not replaced by an independent
prime box. Its reciprocal mass is at most `(183/100)h/t`. The proof safely
overcounts the ordered cofactor tuples, without claiming a factorial credit.
Together these give reciprocal mass at most `h/(2000t)`.

The existing exact positive-five coefficient costs one marked logarithm.
On the selected box and `69t/100<=L<=7t/10`, its norm is at most `t/6`.
Consequently, with the unchanged residual coefficient, factorial kernel,
physical masks, moving length, allocation factor and full phase,

```math
\sum_{n\in B(t)}\left|
 c^{\rm residual}_{L,N}(n)K_N(3/2+iy,n)\right|
 \le\frac{1}{10000}\,
 \frac{e^{-t/2}(t+h)^N}{N!}\,h.
```

This is an actual prime-sum bound, independent of any zero hypothesis or
continuum model. It is uniform in the real phase height. The starting
moment is existential.

Proofs: [local population bound](../RiemannGaussian/ZetaRieszPositiveFiveBudget.lean),
[full-period bound and spending ledger](../RiemannGaussian/ZetaRieszJointPositiveFiveBounds.lean).

## Whole-sum application and exact spending

Let `P_j` be the previously paid central triple/four/five population, and
select the new box only from `S_j \ P_j`. Call that full-period selection
`B_j`; this explicitly prevents double spending. Define `R_j` to be the
original signed sum over `S_j \ (P_j union B_j)` and `b_j` to be the original
signed sum over `B_j`. These names abbreviate finite sums, not new carriers.

The old central period margin is `m V0 h/500`, where `m` is the phase mesh
size, not zero multiplicity. The new debit is at most `m V0 h/1000` after
paying the original radial variation at every phase, including boundaries.
The remaining margin transports to half the old explicit source credit

```math
G_N=\frac{\pi u e^{-1}}{24000|y|}\frac{(2u)^N}{N+1}.
```

The cached central-capacity application proves, for
`1/2<u<=10001/20000` and fixed `|y|>=54`, the following alternative whole-sum
comparisons, each with its own paid population and signed rest:

```math
\begin{gathered}
u^{N_j+1}\bigl(\operatorname{Re}R_j+
 \max(\operatorname{Re}b_j,0)\bigr)+\frac{G_{N_j}}2-e_j
 \le\operatorname{Re}\bigl(u^{N_j+1}(J_j+C_j)\bigr),\\
\operatorname{Re}\bigl(u^{N_j+1}(J_j+C_j)\bigr)
 \le u^{N_j+1}\bigl(\operatorname{Re}R_j+
 \min(\operatorname{Re}b_j,0)\bigr)-\frac{G_{N_j}}2+e_j,
 \qquad e_j\longrightarrow0.
\end{gathered}
```

The lower and upper credits must not be added: they use alternative
spending ledgers. All old central triple/four/five payments remain in
place. The earlier SevenCountTail/reflection comparisons are preserved as
separate bounds; their supplies are not combined with this one.

The terminal proofs are
`RieszCentralCapacityTransfer.eventually_joint_positive_five_floor` and
`RieszCentralCapacityTransfer.eventually_joint_positive_five_ceiling` in
[CheckRieszCentralCapacityTransfer.lean](../scripts/CheckRieszCentralCapacityTransfer.lean).
They import the already verified optional angular assemblies; no open
counting or payment estimate is an assumption of these terminal theorems.
[The audit](riesz-central-capacity-audit.json) records their source hash,
validation and standard axioms. The ordinary root library contains the
population estimates and explicit spending implications, while the cached
application discharges their central-payment inputs.

Reproduce the optional application without rerunning either exhaustive cover:

```bash
lake env bash -c 'LEAN_PATH="$PWD/.lake/riesz-four-capacity-bin2:$PWD/.lake/riesz-five-capacity-bin2:$LEAN_PATH" lean -DwarningAsError=true scripts/CheckRieszCentralCapacityTransfer.lean'
```

## Scope and next obstruction

This removes one fixed positive-five prime-share sector from the unpaid
rest of a whole-sum comparison, rather than improving a coefficient in
isolation. It does not pay every positive-five label, every radial period,
or other remaining prime counts. The retained source credit grows for
`u>1/2`; under a finite whole source its opposing signed rest must still
compensate it. The next estimate must control more of that actual rest,
without treating it as an independently small error.

The optional [numerical probe](../scripts/probe_riesz_positive_five_payment.py)
and [its output](riesz-positive-five-payment-probe.json) compare the
conservative debit to an angular prime-density model. Its sampled box mass
is about `1.4e-6..1.6e-6` in coefficient/total-log normalization. Those
numbers do not certify literal counts or phase cancellation and are not
used by the Lean proofs. The literal bound uses only the proved prime
window estimates and the exact arithmetic coefficient.
