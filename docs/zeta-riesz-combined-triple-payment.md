# Combined signed payments for the whole Riesz carrier

The new triple-period estimate is spent in the same lower and upper
comparisons as the existing three-, four- and five-prime payments. The
comparison is with the original whole `J+C`, not a completed carrier.
Every removed population has a proved cost; the remaining sum stays signed.
Neither final numerical whole-sum bound is proved.

## Exact populations and retained observations

Let `S` be the original `coreBand`, `f_N` its original residual atom, and
`G_N=sourceCredit u y N`. On the original dyadic schedule, the existing
period grid supplies the following populations:

- `P`: the earlier balanced triples, four-prime payment and negative-five
  supply, with the respective floor or ceiling selection;
- `I`: the complete positive-five interior inside `S\\P`;
- `D`: the owner band inside `S\\(P union I)`;
- `H`: the small-prime five-factor boundary outside the earlier selections;
- `Q`: the literal unbalanced triples from the complete-period cancellation
  theorem, with middle-prime log in `(9v/25,2v/5]` and least-prime log in
  `(2v/25,v/10]`.

Lean proves that `Q` is disjoint from every previously paid population:
three-factor geometry separates it from the balanced triples, factor counts
separate it from the four/five-factor populations, and its largest share
at most `9/16` separates it from the owner band starting at `119/200`.
All original core, phase, allocation and physical masks remain.

The final exact rest is

```math
E=S\setminus(P\cup I\cup H\cup Q\cup D).
```

The lower comparison retains the positive part of every individual `I`
atom and the positive real parts of the complete `H`, `Q` and `D` sums.
The upper comparison retains the corresponding negative parts. Bounding
the coupled `Q` sum precedes taking its absolute value; no sum of triple
atom norms is substituted.

## Debit and remaining margin

The earlier interior and small-prime payments leave `m*V0*h/4800`.
The triple period costs `m*Vq*h/6250`, with an independently proved
allocation error tending to zero. Both radial constants are bounded by
the same actual kernel, and

```math
0<V_q\le \frac{e^{-v/2}v^N}{N!}\le\frac{501}{500}V_0.
```

The checked arithmetic leaves at least

```math
\frac{m h}{25000}\frac{e^{-v/2}v^N}{N!}
```

before the owner payment. The resulting whole comparisons have margin

```math
M_N=\left(\frac2{25}\sqrt{N+1}-\frac18\right)G_N,
\qquad
G_N=\frac{\pi u e^{-1}}{24000|y|}\frac{(2u)^N}{N+1}.
```

Write `O_+` and `O_-` for the favorable observations described above.
For fixed `54<=abs(y)` and `1/2<u<=10001/20000`, there is a nonnegative
`err_j -> 0` such that eventually

```math
u^{N+1}\left(\Re\sum_{n\in E}f_N(n)+O_+\right)+M_N-\mathrm{err}_j
\le \Re\bigl(u^{N+1}(J_N+C_N)\bigr),
```

and, with the upper comparison's own population witnesses,

```math
\Re\bigl(u^{N+1}(J_N+C_N)\bigr)
\le u^{N+1}\left(\Re\sum_{n\in E}f_N(n)+O_-\right)-M_N+\mathrm{err}_j.
```

These are alternative bounds on the same whole expression. Their margins
cannot be added. The older, larger margin belongs to a larger unpaid rest
and cannot be reused here. `G_N` grows for `u>1/2`; this payment is not a
source-normalized decay theorem.

## Six-prime refinement and the open target

The two additional terminal theorems apply the existing centered six-prime
charge only to `E`. One reflected-large prime costs at most
`(log n/L)*min(3*log(minFac n),4*abs(2*(log n-L)-log(activePart)))`;
two cost one least-prime unit; three cancel exactly. The original phase,
allocation, favorable observations and every other count remain intact.
No numerical six-prime density assumption is used.

The [second-reflection refinement](zeta-riesz-six-second-reflection.md)
now reduces those directed costs further inside the one-large sector.
Its concrete whole applications retain the same rest and margin above;
no population is removed and no earlier credit is spent again.

The unpaid rest still includes other triple geometries, negative-five
labels, remaining six- and higher-factor labels, and other radial periods.
Its independent signed estimate must dominate the explicit remaining
budget. The whole endgame still requires a cofinal `-79/1000-o(1)` floor
for simple-zero sources and a `3/2+o(1)` ceiling for higher multiplicities.
Exposure does not imply simplicity. This slice supplies no zero exclusion.

## Proofs and reproduction

- [Disjointness and exact signed spending](../RiemannGaussian/ZetaRieszJointTriplePayment.lean).
- [Whole applications with an explicit finite cover premise](../scripts/CheckRieszTriplePeriodJoint.lean).
- [Concrete cached-certificate applications](../scripts/CheckRieszCertifiedTriplePeriod.lean).
- [Triple-period estimate](zeta-riesz-triple-period-cancellation.md).
- [Complete positive-five payment and cover reproduction](zeta-riesz-full-positive-five-payment.md).
- [Source fingerprints and check results](riesz-central-capacity-audit.json).

After the cover assemblies and `CheckRieszFullPositiveFive.lean` are checked,
use the same pinned optional import path documented for the positive-five
payment, then run:

```sh
"$riesz_lean" -DwarningAsError=true --root="$PWD/scripts" -o .lake/riesz-positive-five-application/CheckRieszTriplePeriodJoint.olean scripts/CheckRieszTriplePeriodJoint.lean
"$riesz_lean" -DwarningAsError=true --root="$PWD/scripts" -o .lake/riesz-positive-five-application/CheckRieszCertifiedTriplePeriod.olean scripts/CheckRieszCertifiedTriplePeriod.lean
```

The optional applications print their terminal axioms and run all declaration
linters. Ordinary builds import the disjointness and signed-spending module;
they do not repeat the exhaustive cover.
