# Reflected large primes sharpen the literal signed costs

The [active-prime proof](../RiemannGaussian/ZetaRieszReflectedPrimeBounds.lean)
and [second-reflection proof](../RiemannGaussian/ZetaRieszSevenPrimeReflection.lean)
uses the actual reflected cutoff to improve both coefficient signs on the
unpaid interior. It retains the original integer label, complex phase,
factorial kernel, allocation fraction and every core mask. No signed
supply is spent, no prime-density model is used, and no zero hypothesis
enters the estimates.

Write `T=log n`, `D=T-L`, `k=omega(n)`, and let `o` be the number of prime
factors satisfying **`log p>=D`**, including equality. These are reflected
large primes, not the separate physical threshold `p>N^2`.

In units `(T/L)*log(minFac n)`, the following intervals are proved:

| Prime count | Previous interval | One reflected large prime | Two reflected large primes |
| ---: | ---: | ---: | ---: |
| 6 | [-3,4] | [-3,3] | **[-1,1]** |
| 7 | [-5,10] | **[-4,6]** | **[-1,3]** |
| 8 | [-15,13] | **[-10,10]** | **[-6,4]** |
| 9 | [-35,27] | **[-20,15]** | **[-10,10]** |
| 10 | [-49,56] | **[-35,35]** | **[-15,20]** |

The count-dependent theorem covers every higher count, not just these
four rows. `activeCapacity_table` checks the active-count integers; the
seven-prime/two-outer entry is further sharpened from `[-3,3]` by
`coefficient_seven_two_outer_sharp`. The new
allowance is intersected with the previous even/odd interval, so neither
signed charge increases. Counts below seven remain unchanged in the
earlier terminal comparison. The subsequent six-prime theorem separately
sharpens the two-large sector and feeds it into the expanded whole
comparisons.

There is also an exact deletion: on the literal core, **every label with
at least five prime factors and three reflected large primes has zero
coefficient**. This is cancellation within the original divisor sum,
not decay or an allowance paid by another population.

## Why the active count is smaller

Factor the squarefree label as `n=b*a`, where `b` contains the prime factors
with `log p>=D`, and `a` contains all remaining prime factors. The existing
exact prime-insertion identity gives

\[
R_D(n)=R_D(a).
\]

Any divisor involving a prime of `b` has zero truncated hinge, including
the cutoff endpoint. Reflection then gives the original coefficient

\[
c_L(n)=-\frac TL(-1)^k R_D(a).
\]

The parity here is **the original count `k`**, not the active count `k-o`.
The ordinary prime factors in `b` still belong to `n`, its phase and its
allocation. The proof does not complete or average a prime incidence.

Let `E_j,O_j` be the previously proved largest even/odd binomial-layer
capacities. When `a` has at least two prime factors, the signed divisor
bound applied to this actual cofactor is

\[
-O_{k-o-2}\log p_{\min}\le R_D(a)
\le E_{k-o-2}\log p_{\min}.
\]

`activePart_minFac` proves that the least prime is unchanged. Therefore
the coefficient capacities are `(E,O)` for even `k` and `(O,E)` for odd
`k`, at the smaller index `k-o-2`. This accounts for both signs in the table.

The core supplies `D>7T/25>T/4`, with the moving `L_N` retained. Four
reflected large primes cannot fit in the logarithmic budget. Thus `o<=3`
and, for `k>=5`, the active cofactor has at least two prime factors.
If `o=3`,

\[
\log a\le T-3D<D.
\]

The active composite is fully saturated. Its complete Möbius mass and
first logarithmic moment both cancel, so `R_D(a)=0` exactly.

## A second reflection saves two negative units

For seven prime factors and exactly two reflected large primes, the active
cofactor has five prime factors and `A=log a<=T-2D`. The literal core gives
the sharper **`D/T>289/1000>2/7`**, so `2A<3D`. Reflecting its exact divisor
sum once more gives

\[
R_D(a)=-R_{A-D}(a),\qquad 3(A-D)\le A.
\]

`riesz_five_lower_third_le` proves `R_E(a)<=log(minFac a)` whenever
`3E<=log a`, with every five-prime cutoff chamber included. If a prime
is above the cutoff it is deleted from the divisor response exactly,
leaving the four-prime bound. When all five logarithms are below the
cutoff, the full signed hinge sum is nonpositive between the first quarter
and third, and equals `A-4E` below the first quarter; the latter is at most
any one prime logarithm. The proof retains the signs through both cases.

Consequently `R_D(a)>=-log(minFac a)`. The unchanged total count is odd,
so the original coefficient is `(T/L)R_D(a)`, and its interval improves
from **`[-3,3]` to `[-1,3]`**. The least prime is the original label's
least prime. The second reflection is not a new carrier or completion.

For `b=(T/L)log(minFac n)` and the original phase `c=cos(y log n)`,
`seven_cost_savings` proves the exact reductions

\[
\text{old floor charge}-\text{new floor charge}=2b\max(c,0),
\qquad
\text{old ceiling charge}-\text{new ceiling charge}=2b\max(-c,0).
\]

These are alternative one-sided bounds, not additive credits. The
two-thirds reduction concerns only the affected coefficient/phase charge,
not the size of the complete signed sum. No source mass is estimated by
this identity.

## Connection to the same signed carrier

The [six-prime continuation](../RiemannGaussian/ZetaRieszSixPrimeReflection.lean)
uses the same second reflection. Its active cofactor now has four prime
factors, and `2*log a<=3D` again follows from `D/T>=2/7`. For
`E=log a-D`, the exact four-prime response satisfies

```math
-\log(\minFac a)\le R_E(a)\le\log(\minFac a),\qquad 3E\le\log a.
```

For the new lower bound, a prime at or above `E` is deleted from the
response and leaves the three-prime bound. If all four logs are below
`E`, the response equals `log a-3E>=0`. The reflection has positive sign
because the active cofactor has four factors. The original total count
is also even, so the coefficient interval is exactly bounded by
`[-1,1]`, compared with the earlier `[-3,4]`.

The literal `core_reflected_subset_bounds` theorem retains every favorable
signed observation and every other count. It also applies the independently
proved one-large interval `[-3,3]` and exact three-large zero, so the costs
are 3, 1 and 0 for the three reflected-count cases. It applies from `N>=2`
on any selected core subset. The corresponding whole comparisons in
[the optional full-five application](../scripts/CheckRieszFullPositiveFive.lean)
use this bound only on their exact unpaid remainder, preserving all
previous payments and the whole-sum margin. The numerical cover premise
in that application is still under verification. The exact rational
probe attains both interval endpoints in logarithmic models; it is not
a prime-density or source-mass certificate.

The [centered refinement](../RiemannGaussian/ZetaRieszSixPrimeCentered.lean)
improves the one-large sector further. Its five active factors have
`R_(log(a)/2)(a)=0` by odd reflection. The proved cutoff slope therefore
gives the original coefficient bound

```math
|c_L(n)|\le\frac TL\min\{3\log(\minFac n),4|2D-\log a|\}.
```

`centeredSixCost_le_reflected` proves that neither directed charge
increases. `core_centered_subset_bounds` applies this to the same unpaid
core, and the optional whole comparisons now use this sharper bound.
The factorial allocation and complex phase are unchanged; the midpoint
is cancellation inside the original divisor response.
The [cached whole application](../scripts/CheckRieszSixCenteredJoint.lean)
already applies it to both earlier certified comparisons without using
the pending positive-five cover. It preserves their original payments
and margin; the two different population ledgers must not be combined.

`core_sum_eq_outer_filter` removes this zero sector from **any subset**
of the original core, preserving its full complex sum. In particular,
`nonzero_core_outer_le_two` applies to any unpaid high-count label in an
earlier ledger. This does not require a new carrier definition.

`ZetaRieszSevenPrimeReflection.eventually_core_subset_bounds` transfers
the further improved coefficient interval
to both source-normalized signed comparisons. It keeps the observed
cosine, the original nonnegative factorial/allocation weight, every
favorable selected observation, and all other counts exactly. The theorem
holds for every selected core subset, all heights and count ceilings, on
`1/2<u<=10001/20000`. The quarter-cutoff deletion itself holds from `N>=2`;
the complementary one-third condition used with earlier bounds is eventual.

The earlier [seven-prime head payment](zeta-riesz-seven-prime-head.md),
[count-tail payment](zeta-riesz-log-count-tail.md), all signed credits and
their spending restrictions remain available. These pointwise savings are
not additional additive credits.

## Improvement of the whole joint estimates

The [joint proof](../RiemannGaussian/ZetaRieszJointReflectionBounds.lean)
does not stop at those component inequalities.
`eventually_joint_floor` and `eventually_joint_ceiling` apply them directly
to the **same `J+C`** in the multiplicity-aware endgame, on the original
dyadic schedule. They require `1/2<u<=10001/20000` and fixed `|y|>=16`,
with no hypothetical-zero assumption.

Let `E` be exactly the unpaid rest in
`ZetaRieszSevenCountTail.eventually_core_full_floor` (or its ceiling
counterpart). All earlier triple, four-prime, five-prime, exponential-head
and logarithmic-count payments, their favorable observations and the
one-sixty-fourth reserve are retained. Inside this **unpaid** population set

\[
E_7=\{n\in E: n\text{ squarefree},\ \omega(n)=7,\ o(n)=2\},\quad
b_n=\frac{\log n}{L}\log(\minFac n),\quad c_n=\cos(y\log n).
\]

Here `w_n` is the original nonnegative factorial/allocation weight.
`sum_observation_savings` proves that the earlier coefficient-charged
joint comparisons improve by exactly

\[
G_N^+=2u^{N+1}\sum_{n\in E_7}w_nb_n\max(c_n,0),\qquad
G_N^-=2u^{N+1}\sum_{n\in E_7}w_nb_n\max(-c_n,0).
\]

If `L_old` and `U_old` denote those earlier signed comparisons, including
their retained payments, the terminal theorems give

\[
L_{\mathrm{old}}+G_N^+-e_j
\ \le\ \Re\bigl(u^{N+1}(J_N+C_N)\bigr)
\ \le\ U_{\mathrm{old}}-G_N^-+e'_j,
\qquad e_j,e'_j\longrightarrow0.
\]

Each comparison retains its own original payment witnesses. The errors
are proved to vanish using the existing radial and joint-boundary bounds;
they are not new arithmetic assumptions. Both gains are nonnegative, and
no paid population is charged or credited again. Lower prime counts in
the unpaid rest remain signed and exact.

This is a checked improvement in the **whole-sum estimates**, but the
size of either total gain has no certified positive source-scale lower
bound here. The remaining task is to bring the complete lower comparison
to `-79/1000-o(1)` and the upper comparison to `3/2+o(1)`. The model probe
does not evaluate that remaining numerical deficit.

The independently required whole-sum bounds remain open: the
[multiplicity-aware endgame](zeta-riesz-joint-floor.md) requires a cofinal
`-79/1000-o(1)` floor for simple zeros and a cofinal `3/2+o(1)` ceiling for
multiple zeros. Neither follows from the coefficient table. In particular,
terms with zero, one or two reflected large primes still need joint signed
control, and none of the percentage coefficient savings is a certified
percentage reduction of the whole carrier.

## Optional quantitative regression

The [probe](../scripts/probe_riesz_reflected_primes.py) and its
[recorded output](riesz-reflected-primes-probe.json) use exact rational
weights modeling prime logarithms. They verify the removal identity and
display the resulting intervals on deterministic samples. These are not
actual prime labels, certified extrema, prime densities or source bounds.
The probe stays outside ordinary CI.

```sh
../.venv/bin/python scripts/probe_riesz_reflected_primes.py
```
