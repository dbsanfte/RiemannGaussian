# Multi-order cluster test for the unchanged ceiling

The **all-height, fixed-strip ceiling remains open**. This slice is a
kernel-checked no-go for one proposed method: combining more complete-moment
majorants with negative integral local residues, exposure, half-plane geometry
and a free analytic remainder does not force the ceiling. It supplies **zero
new arithmetic ceiling credit** and no zero exclusion.

The leaf is
[`ZetaRieszCeilingClusterPowerAudit.lean`](../RiemannGaussian/ZetaRieszCeilingClusterPowerAudit.lean).
It preserves the previous actual arithmetic isolation-sector payment and the
gap-free signed constraint. No literal carrier, prime population, mask, moving
length, phase, factorial index, incidence or diagonal is replaced.

## Exact cancellation before numerical detection

Take

$$
u=\frac{10001}{20000},\qquad M=131072,\qquad
\zeta=e^{2\pi i/M},\qquad v_i=u+(1-u)\zeta^i.
$$

The model singular residues are all the negative integer $-2$. The selected
node is $v_0=1$; every other node has modulus strictly below one. Character
orthogonality, applied **before norms or numerical evaluation**, gives

$$
\sum_{i=0}^{M-1}v_i^k
=M\sum_{\substack{0\le j\le k\\M\mid j}}
\binom{k}{j}u^{k-j}(1-u)^j.
$$

In particular, for $k<M$ this is exactly $Mu^k$. The explicit regular term
$2Mu^k$ is retained at every order. Thus the whole model array

$$
a_n=-2\sum_i v_i^{n+1}+2Mu^{n+1}
$$

vanishes identically when $n+1<M$, including orders zero and one. This is an
exact cancellation identity, not a fitted fractional-residue cloud or a
decision to omit low orders. `sum_root_powers`, `sum_node_powers` and
`modelArray_eq_zero` prove the low-power identities in Lean. The full
divisible-harmonic formula is used by the optional numerical replay.

The cancellation lasts far beyond the order-4096 test window. Widening a
finite detector window alone is therefore insufficient. The integer example
below also passes the majorant for **every** order, not merely the sampled
window.

## Exposure and local strip geometry

Assign the synthetic physical denominators

$$
D_i=\frac{u}{v_i}.
$$

Lean proves $\Re D_i\ge u$, and $|D_i|>u$ for every $i\ne0$. Thus the selected
mode is exposed and no synthetic competitor is farther right than the
selected one. The positions are distinct; repeated indices do not disguise
fractional multiplicities.

Retain only indices with $|D_i|<4/5$. They include the selected index and give
synthetic coordinates

$$
\tau_i=\frac32+i y-D_i,\qquad 0<\Re\tau_i<1.
$$

These coordinates are **not** `NontrivialZetaZero` objects. The construction
asserts no actual zeta zero. Its local population is only a model population.
The optional replay counts 74731 local modes and checks the adjacent cutoff
nodes; this count is not needed by the Lean theorem.

## The exact analytic remainder is included

Moving omitted nodes into the regular part gives the exact local ledger

$$
a_n=-2\sum_{i\in S}v_i^{n+1}+h_n,
\qquad
h_n=2Mu^{n+1}-2\sum_{i\notin S}v_i^{n+1}.
$$

`model_eq_local` proves this identity before any estimate. The leaf also proves

$$
|h_n|\le4M(3/4)^{n+1}.
$$

Its explicit generating function is

$$
H(t)=\frac{2Mu}{1-ut}-2\sum_{i\notin S}\frac{v_i}{1-v_i t}.
$$

`localGenerating_analytic` proves analyticity on the closed disk $|t|\le4/3$;
`hasSum_localRegular` identifies its coefficients **exactly** with the $h_n$
of the local ledger. The order-zero and order-one channels are retained.

The first term of $H$ has a **synthetic positive pole** at $t=1/u$, outside
this local disk. It is not asserted to be a genuine zeta remainder. This is
not a counterexample to the complete global all-negative xi divisor or its
functional equation. The precise point is that local analyticity and a
geometric coefficient bound alone do not exclude this correction.

## All-order majorant and the same joined evaluator

After the exact cancellation, $|a_n|\le3M$ for every $n\ge1$. Rational block
certificates establish

$$
\left(\frac{10001}{10000}\right)^{256}\ge\frac{641}{625},
\qquad
\left(\frac{641}{625}\right)^{512}\ge3M.
$$

Consequently `model_complete_moment_bound` proves

$$
|a_n|\le(2u)^{n+1}\qquad\text{for every }n\ge0.
$$

This is the pole majorant underlying the complete-moment test, satisfied here
by a model, not an identified complete-prime array. Below $M$ the array is
exactly zero; beyond $M$ the growth budget covers its full finite mass.

`modelArray_tendsto` proves $a_n\to-2$. Evaluating the **same** existing signed
joined expression, with its actual moving length, factorial prefixes and
diagonal retained, therefore gives

$$
-2+4c_{\rm ret}(u)
=1.68051281186022328837\ldots>\frac{42}{25}.
$$

`model_joined_gt_ceiling` proves the eventual strict violation for this array.
It does not change the actual arithmetic target or identify the array with
prime moments. No native entry order is supplied.

## What the audit settles and what remains

The signed counterweight seen at one moment order can persist consistently
across all orders in this local model, then eventually disappear and expose
a double source. Negative integer residues, rightmost half-plane geometry,
exposure, local analyticity and the complete-moment majorant are insufficient
by themselves. Another window extension using only those inputs cannot earn
ceiling credit.

A useful next estimate must constrain the **actual complete arithmetic
measure** or the **actual remainder**, beyond these local hypotheses. The
synthetic regular pole exposes exactly where that additional information is
missing. It does not prove that such information is unavailable, or refute the
ceiling for actual primes.

The earlier actual isolation result remains valid. The original all-height
ceiling and the independent simple-zero floor are still open. No RH or
zero-free claim follows from this audit.

## Local validation

The optional namespace check compiles the leaf, runs the 14 linters and checks
all transitive theorem axioms, including private and automatic helpers.
Only standard Lean axioms are allowed. The exact count is in the scoped audit.

`probe_riesz_ceiling_cluster_power.py` collects the exact root harmonics before
evaluation. `check_riesz_ceiling_cluster_power.py` independently replays the
two rational certificates with FLINT integers, fourteen collected power rows
and eight geometry rows with 420-bit Arb intervals. Neither script imports
the other. Neither uses prime or actual-zero data.

All artifacts are scoped to `.lake/riesz-ceiling-cluster-power-audit`. Previous
source/proof/probe hashes are checked without rewriting their bytes. There
are no commits, pushes, subagents, root registration, public metadata changes,
ordinary CI additions or wider gates in this slice.
