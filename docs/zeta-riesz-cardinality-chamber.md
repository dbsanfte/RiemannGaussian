# Signed count-boundary audit

**The retained signed prime-sum bound and complementary floor remain open.**
The target stays `u^(N+1)*(lowerThresholdPacket(3..55)-shortOverflowPacket(3..13))`.
This pass proves coefficients for unequal prime logarithms and tests a
complete-count coherent modal contribution. No original mask is removed.

## Exact subset cancellation

Let `k` be the cofactor count, `s` its total logarithm, and `d` the reflected
cutoff. Suppose every subset of at most `m` coordinates lies below `d`,
and every larger subset lies above it. For `k>=2`, `m>=1`,
[`kernel_chamber` and `chamberKernel_eq`](../RiemannGaussian/ZetaRieszCardinalityChamber.lean)
prove, before any norm,

\[
\boxed{H_k(d;\mathbf x)
 =(-1)^m\left[{k-1\choose m}d-{k-2\choose m-1}s\right].}
\]

Every coordinate occurs in `choose(k-1,j-1)` subsets of size `j`. Thus
redistribution inside the same chamber changes neither the kernel nor its
sign. Prime logarithms need not be equal. `kernel_near_threshold` verifies
all subset tests from `x_i>=r`, `e=s-kr`, and `mr+e<=d<=(m+1)r`.
This finite identity does **not** prove a derivative jump of an integrated
count convolution or a nonzero asymptotic residue of the full carrier.

## Actual prime coefficients

Write `n=P*a`, `T=log n`, `v=log P`, with `P` prime and `n` squarefree.
The existing saturated-prime identity gives `c_L(n)=(T/L)H_k(L-v)`.
The new theorems discharge saturation on these explicit chambers.

For thirteen-prime labels, assume

\[
v\ge\frac{21T}{40},\quad
\frac{693T}{1000}\le L\le\frac{347T}{500},\quad
\log p\ge\frac{79T}{2000}\ (p\mid a).
\]

`thirteen_prime_coefficient` proves

\[
c_L(n)=\frac TL(330L-210v-120T),\qquad
\operatorname{Re}c_L(n)\le-\frac{123T^2}{100L}.
\]

For forty-nine-prime labels, assume

\[
\frac{21T}{40}\le v\le\frac{52501T}{100000},\quad
\frac{6931T}{10000}\le L\le\frac{1733T}{2500},\quad
\log p\ge\frac{1979T}{200000}\ (p\mid a).
\]

`fortyNine_prime_coefficient` proves

\[
\operatorname{Re}c_L(n)\ge
\frac3{500}{47\choose16}\frac{T^2}{L}>0.
\]

These are arithmetic coefficient estimates under stated geometric tests.
They do not sign `c_L(n)n^(-iy)`, compare prime populations, or bound their
weighted sum. All other labels remain unpaid.

The [optional regression](riesz-cardinality-chamber-probe.json) has distinct
13- and 49-prime examples at `N=2048` with checked Proth primality witnesses.
They meet the recorded core, physical, owner, least and nondominant tests;
their original rectangle weights are approximately `0.2793` and `0.2632`.
These are chosen examples, not a population estimate or a formal embedding
of the whole sector. Their logs, weights and phases are exploratory.
A separate exact rational dynamic program sums all `2^12` and `2^48`
signed subsets of distinct coordinates and agrees with the Lean formula.

## A sign transition missed by a coarse ratio

At owner share `14/25` and 44 equal cofactor shares `1/100`, Lean proves

\[
H_{44}(\lambda-14/25;1/100,\ldots,1/100)
 ={43\choose13}\left(\frac{149}{215}-\lambda\right).
\]

The earlier positive regression at `lambda=693/1000` remains correct.
But `source_ratio_in_chamber` proves, for `1/2<=u<=10001/20000`,

\[
\frac{149}{215}<\frac{6931}{10000}
 <-2u\log u<\frac{1733}{2500}.
\]

`interior_kernel_source_negative` therefore proves the opposite sign at
the canonical limiting source ratio. This neither freezes moving `L_N/T`
nor signs every finite order. It prevents importing the coarse regression's
sign into a global residue claim. The earlier 13/49-corner reinforcement
theorem retains its precise scope; other counts remain essential.

## Coherent modes with every count retained

Fix owner share `p>1/2` on the positive-frequency synthetic mode. Let `a,b`
be the cofactor shares on that same mode and the neutral selected mode;
the rest is on its conjugate. The coupled denominator is

\[
w=(u-\delta+\delta b)+i\eta(2p-1+2a+b).
\]

[`coherent_normSq_gap`](../RiemannGaussian/ZetaRieszMinimumCollisionAudit.lean)
proves, for `a+b>=r>=0` and `0<=delta<=u`,

\[
|w|^2-|u-\delta+i\eta(2p-1)|^2
 \ge2\eta^2(2p-1)r+\eta^2r^2.
\]

`coherent_denominator_strict` gives strictness for a different cofactor
assignment. This sums shares before comparing norms. It does not prove
dominance of the full integral or transfer separate prime-leg limits.

When all cofactors carry one mode, their common exponential depends only
on their total log, independently of count. The [new probe](../scripts/probe_riesz_coherent_counts.py)
evaluates the remaining one-mode cutoff response, with both empty atoms.
At `p=21/40`, `lambda=34657/50000`:

| Negative-mode multiplicity | Cutoff `r=1/100` | Cutoff `r=1/25` |
| --- | ---: | ---: |
| 1 | `1.12977e-52` | `1.6185129263e-8` |
| 3 | `5.79218e-30` | `0.05526229644` |

Only 47 and 11 cofactor primes fit, so the model caps 54 and 12 omit no
possible count. The one-cofactor head is independent of `r` and cancels
in the matched **point-profile** difference. The original two factorial-face
integrals have not been evaluated here.

The [report](riesz-coherent-counts-probe.json) pays renewal evaluation and
projection errors and repeats at higher precision and Taylor degree. Three
owner shares and three ratios were tested; every matched difference is
negative within its ball. This is not a uniform theorem or Lean certificate.

The coherent denominator has norm about `0.50002509`, although each separate
mode norm is about `0.500060997>u=0.50005`. Its constant-amplitude complete
radial moment has candidate log rate `4.98163e-5`. The varying Riesz amplitude,
moving length, both factorial faces and owner integration are not paid by
that rate calculation. No full modal divergence or decay theorem follows.

The remaining estimate must control the joint weighted cutoff response and
its exterior boundaries, or supply a zeta-specific arithmetic correlation.
Neither the finite subset identity nor the complete-count point test bounds
the retained prime sum. No new packet or zero exclusion is claimed.
