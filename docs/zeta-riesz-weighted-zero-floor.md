# Join weighted zero responses and complete affine tails in the native floor

Two additional exact cancellations now act inside the **same whole native
floor**. Both retain the original phase, factorial and allocation masks.
They add no funding cost or source error. The independent numerical floor
remains open.

The modules are
[ZetaRieszWeightedZeroFloor](../RiemannGaussian/ZetaRieszWeightedZeroFloor.lean)
and
[ZetaRieszClosedTailFloor](../RiemannGaussian/ZetaRieszClosedTailFloor.lean).
They build on the previous
[exact zero-response comparison](zeta-riesz-zero-response-floor.md).

## Use the complex zero, rather than one tied real projection

For each previously selected `zeroLabels` label, its original Riesz
coefficient is exactly zero. Therefore **any label-dependent complex
observation** has zero complete response. `complexPrefix_zero_weighted`
proves this directly from the original arithmetic coefficient, before
taking a real part or norm.

The new `weightedIncrement` multiplies the original `sourceWeight` by a
complex coefficient `v_j(n)` only in that exact null correction. The base
carrier keeps its original weight. `sum_weightedIncrement_zero` proves

$$
\sum_k Z_j(v_j;k)=0
$$

for every coefficient family. No boundedness or growth hypothesis is
needed. The previous real correction with its tied imaginary coefficient
is the exact special case

$$
v_j(n)=r_j+i\,r_j\operatorname{nativeTilt}_j.
$$

This permits independent complex coefficients and coefficients depending
on the literal label. It does not alter the phase of the nonzero carrier
or infer masked convergence from separate prime-leg limits.

## Extend the cancellation inside nonzero-response labels

For a squarefree native label `n`, let `R` be its canonical two least
primes and `B=n/R`. The closed-tail indices are

$$
(d,e)\in\operatorname{divisors}(B)\times\operatorname{divisors}(R),
\qquad D_j\le d,
$$

where `D_j=physicalCutoff u j` is the **original integer hinge**, with
`L_j=log D_j` exactly.

Their product `d*e` is an original divisor of `n`.
`tailIndices_injective` uses squarefreeness and coprimality to prove that
each incidence occurs once. `tailDivisors_subset` checks literal support.
No owner/cofactor completion or polynomial size cap is introduced.

On each selected complete block the corrected profile is affine in
`log e`. Thus its constant and first-log moments cancel jointly:

$$
\sum_{e\mid R}\mu(de)
 \operatorname{correctedProfile}_{X_j,L_j}(de)=0.
$$

`affine_tail_block_zero` and `tailDivisors_pairing_zero` prove this with
the exact endpoint and Möbius signs. `tailDivisors_complex_pairing_zero`
keeps an arbitrary common complex phase/allocation weight until after
this sum is zero. This applies even when the **whole label's Riesz
response is nonzero**.

The underlying affine Möbius annihilation is already known in the repo.
The new application is to these original divisor incidences inside the
current native whole-period floor price, at every selected count and
arbitrary rough-prime sizes.

`tailIncrement` is their actual cutoff-prefix increment. The finite Abel
identity proves `sum_tailIncrement_zero` exactly. Arbitrary moving
label-dependent complex coefficients `w_j(n)` are again free. Its base
profile is flat before the hinge, so `tailIncrement_zero_early` supplies
no early-cutoff debit. Orders zero and one are retained.

## The checked joint floor

Write `T_j` for the existing increment with its log, log-square, cubic
and tangent corrections; `V_j` for the independently paid original owner
rows; `Z_j(v_j)` for the weighted whole-zero correction; and `H_j(w_j)`
for the closed affine-tail correction. The joined cost is

$$
D_j=\operatorname{blockCost}
 \bigl(T_j-V_j-Z_j(v_j)-H_j(w_j)\bigr).
$$

Every count and cutoff increment is assembled into complete periods
before the one-sided price is taken. No label, divisor or count is
assigned an additional positive main-term allowance.

`eventually_joined_floor_with_closed_tail_credit` proves

$$
\operatorname{Re}\bigl(u^{N_j+1}\operatorname{joinedPhysical}_j\bigr)
\ge-\operatorname{tailPrice}_j-\operatorname{nativeError}_j
\quad\text{eventually},
$$

where

$$
\operatorname{tailPrice}_j
=\min\left(\operatorname{weightedPrice}_j,
             D_j+\operatorname{nativePaidBudget}_j\right).
$$

The whole previously credited price is retained as an alternative.
Coefficient zero recovers it exactly. This is one joint price, not a sum
of separately spendable credits. The all-prime allocation in `T_j,Z_j,H_j`
and the distinct owner allocation in `V_j` are kept. The signed-row budget,
count-crop/endpoint payments and `nativeError` are unchanged and charged
once.

The arithmetic comparison needs `1/2<u<=10001/20000` and `54<=abs(y)`,
with **no zero hypothesis**. Under the existing exposed-zero hypotheses,
the same `nativeError` tends to zero. The terminal
`false_of_cofinal_tail_price` still leaves the independent premise

$$
\operatorname{tailPrice}_j\le399/5000=0.0798\quad\text{cofinally}
$$

explicit and unproved. Neither a simple-zero exclusion, multiplicity
ceiling nor RH contradiction is claimed.

## Quantitative diagnostic, with earlier candidates retained

The optional
[probe](../scripts/probe_riesz_weighted_zero_floor.py) reuses the four
frozen factored-integer samples: orders `32,64`, seeds `317,919`, and
heights `54,65,100`. The original sample importance weights, phases and
masks remain in the base sum. The imaginary tilt and bounds on every
earlier null coefficient stay fixed when adding directions.

The comparisons are nested:

1. Freeing both complex coefficients improves all 12 finite prices beyond
   the previous real/tilted zero direction.
2. Label-dependent coefficients improve all 12 further. Their supports
   have `18,31,56,40` labels respectively.
3. With `--closed-tail`, complete affine blocks are available inside
   `129,110,154,145` labels. This includes labels with nonzero whole
   responses. All 12 prices improve again; two are near floating zero.

For example, at order64, seed919, height65, the successive prices are
approximately

$$
0.0285944\;\longrightarrow\;0.0285908\;
\longrightarrow\;0.0242468\;\longrightarrow\;0.0043683.
$$

The complex correction is replayed exactly as a feasible label-dependent
candidate up to floating arithmetic. In closed-tail mode, the complete
earlier label-dependent fit is also repriced as a feasible candidate;
the maximum repricing discrepancy is below `2e-18`. Thus the gains do
not result from forgetting old credits or changing their constraints.
The extra label bound only makes those earlier choices feasible; the
Lean identities impose no coefficient bound.

The phase-aligned label basis uses a factor `exp(i*y*log n)` **only in an
exact zero correction**. This removes phase from that basis column, not
from the original signed carrier. Integer comparisons classify both
whole gap-zero labels and closed-tail blocks. Tiny floating responses
are never used as selection criteria.

These remain finite diagnostics: probable-prime decisions, floating logs,
phases, interpolated large period edges and LP coefficients are not
certificates. These orders are not native cofinal points, do not apply
the native count crop, and do not include the native paid-owner packet
or its eventual budget. No native population coverage, source-rate
saving, deficit fraction or cofinal cost bound follows.

The unresolved arithmetic consists of genuinely active hinge crossings
and their joint signed correlations. Complete affine-tail responses are
now exact free corrections inside the whole price, including at growing
counts. This does not yet bound those remaining crossings.

Validation is local: focused warning-as-error Lean/build, compiled ordinary
root plus explicit new modules, namespace lint and transitive axiom checks.
No full-root source rebuild, commit, push, wider CI, README or public
endpoint change is included. The probe stays outside ordinary builds/CI.
