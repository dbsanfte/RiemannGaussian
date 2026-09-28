# Larger six-prime cofactors in both whole comparisons

The independent signed payment now includes a further five-prime cofactor
band. Lean proves that the new population strictly contains the preceding
wide population at sufficiently large radial centers. Both whole
comparisons retain the same margin, allocation treatment and earlier
reflection savings against the resulting smaller signed rest. The final
numerical whole floor and ceiling remain open.

## Exact enlargement

Write `n=p*a` with `p` its unique largest prime. Besides every cofactor
already in `ZetaRieszWideSixPeriod.cofactors v`, the new set includes

\[
\frac35v<\log a\le\frac{133}{200}v,\qquad
\log q\le\frac{33}{100}v\quad(q\mid a),
\]

with `a` squarefree and having exactly five distinct prime factors.
The finite definition uses the already counted broad cofactor set at
scale `133v/120`, filtered by the displayed lower bound and prime cap.
The largest prime still runs over the whole original period

\[
v-\pi/|y|<\log(pa)\le v+\pi/|y|.
\]

The extra band reaches largest-prime shares down to about `0.335`.
Its cofactor primes stay below the owner, so there is no extra incidence
or overlap charge. Every small prime, the full phase, coefficient signs,
original core masks and allocation remain.

`wide_population_subset` proves inclusion of the old payment.
`eventually_added_population_nonempty` proves that the difference contains
actual labels at every sufficiently large center. Its construction uses
least prime two, four distinct ordinary primes in separated logarithmic
windows, and one prime in the full final phase period. Unique ownership
proves these integers could not already have been counted in the old band.
The old payment is replaced, never spent twice.

## Signed estimate and local allocation cost

The exact moving coefficient remains

\[
c_L(pa)=-\frac{\log(pa)}L\mathcal R_{\log(pa)-L}(a).
\]

The new upper cofactor bound is still below `L>=67v/100`. The response
bound `abs(R_D(a))<=3 log(minFac(a))` and slope-eight cutoff estimate
therefore apply without fixing a sign chamber. The signed last-prime
period is summed first.

Actual logarithmic cofactor mass remains `<=C1*v`, and unweighted mass
remains `<=C2*sqrt(v)`, now with constants four times the original broad
constants. The wider denominator costs at most `5/v`; the existing
`1000*eta` and `100` relative signed charges still suffice. The unsigned
local mass used solely to pay allocation is `<=240*C1*m*V*h`.
The unchanged `6*exp(-N/100000)` allocation fraction is absorbed locally.

For each fixed `|y|>=54` and `epsilon>0`, Lean proves eventually,
uniformly in every finite eligible prime set `A`, every `2N<=v<=2N+1`
with `cos(y*v)=-1`, and `L>=67v/100`,

\[
\left|\operatorname{Re}\sum_{n\in Z(v,y)}
 \operatorname{residualCoefficient}(A,L,N,n)K_N(3/2+iy,n)\right|
\le\epsilon\frac{\pi}{4|y|}\frac{e^{-v/2}v^N}{N!}.
\]

The theorem is `eventually_residual_population_small` in
[`ZetaRieszSixCofactorPeriod.lean`](../RiemannGaussian/ZetaRieszSixCofactorPeriod.lean).
It is relative local `o(radial)`, **not source-o(1)**. The starting order
is existential and may depend on height and precision. No zero hypothesis
or simplicity assumption is used.

## Whole-sum applications

[`CheckRieszSixCofactorJoint.lean`](../scripts/CheckRieszSixCofactorJoint.lean)
pays this population in both whole comparisons at the same local debit
`m*V*h/100000`. The margin remains

\[
\left(\frac{\sqrt{N+1}}{16}-\frac18\right)G_N,
\]

with all favorable signed observations and only the preceding triple
payment's separate geometric allocation error. The exact unpaid rest is
`S \ (P union I union H union Q union Z union D)`, with this enlarged `Z`.
[`CheckRieszSixCofactorWhole.lean`](../scripts/CheckRieszSixCofactorWhole.lean)
keeps the earlier second-reflection costs on precisely that rest.
The optional numerical-cover premises use unchanged cached assemblies.

Other labels and phase periods still need independent signed estimates.
This slice does not establish the final `-79/1000` whole floor or `3/2`
whole ceiling, a zero exclusion, or RH.

## Diagnostic only

Four scrambled Sobol replicates give about 96.3–96.5% coverage of the
sampled negative one-large six-prime angular mass, compared with
92.5–92.7% for the preceding wide band. These percentages omit radial and
phase weights and are not certified arithmetic bounds. They play no role
in the Lean proof. See the optional
[`probe_riesz_six_cofactor_period.py`](../scripts/probe_riesz_six_cofactor_period.py)
and its [recorded output](riesz-six-cofactor-period-probe.json).
