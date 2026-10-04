# Global factorial-prefix payment of the literal pair masks

The [checked module](../RiemannGaussian/ZetaRieszPairPrefixPayment.lean)
pays the difference between the current literal signed pair defect and one
symmetric exact factorial-prefix sum. It proves a geometric error bound on
the whole retained population, without an exposed-zero hypothesis:

$$
\left\|D_N-D_N^{\mathrm{prefix}}\right\|
\le 12e^2(N+1)e^{-N/1600},\qquad N\ge65536.
$$

Here `1/2 <= u <= 10001/20000` and `54 <= |y|`. Both sums use the SAME
original complete-period labels and actual phase. No ordinary prime series
or radial support is completed. This is a bound on their **difference**;
the independent signed upper bound for the prefix sum remains open.

## The precise signed main

For the unique distinct pair `n=p*q`, `p>q`, write
`x=log p`, `z=log q`, `T=x+z`, and `L=length u N`. Define the exact binomial
prefix, retaining order zero and the literal floor:

$$
F_N(v)=\sum_{k=0}^{\lfloor13N/32\rfloor}
\binom{N+1}{k}v^k(1-v)^{N+1-k}.
$$

The symmetric comparison coefficient is

$$
Q_N(x,z)=T\left(1-\frac TL\right)
-\frac TL\left[(L-x)F_N(z/T)+(L-z)F_N(x/T)\right].
$$

`prefixCoefficient` also retains the exact original radial flag: if `n`
is outside `primeLabels N union semiprimeLabels N`, it subtracts the original
`completedCoefficient`. This flag is essential at a possible period
endpoint; it is not silently filled. `prefixPairDefect` uses
`prefixCoefficient - selbergCoefficient` on the same nonprime support as
`literalPairDefect`. Every surviving integer is a genuine distinct-prime
pair. The ordinary-prime terms were already proved to vanish in the defect.

## What is paid globally

The proof joins the original completed coefficient, head and unallocated
correction on each label before comparing coefficients. Put
`G_N(v)=lowerMass (N+1) (N/5+1) v` and
`alpha=T*(L-x)/L`. Relative to the canonical one-prefix expression, the
exact owner error is respectively

| Actual owner range | Exact signed error |
| --- | --- |
| `x < 51N/50` | `alpha * F_N(z/T)` |
| `51N/50 <= x <= 5N/4` | `alpha * G_N(z/T)` |
| `5N/4 < x` | `alpha * (F_N(z/T)-1)` |

On the actual contracted core,
`1971N/1000 <= T <= 2029N/1000` and
`277N/200 <= L <= 7N/5`. These three errors are separated from their
factorial transitions. The additional nonowner prefix has `x/T>=1/2`
and is also paid. Explicit tilts prove

$$
\left|\operatorname{joinedLogCoefficient}_N-Q_N\right|
\le 3T e^{-N/1250}.
$$

The actual sieve and head support are proved from the original integer
cutoffs. In particular, `cube_below_core` proves the required roughness
already for `N>=65536`, rather than leaving it as a new arithmetic premise.

Only this coefficient **error** is normed. The exact identity

$$
\log n\,\|K_N(3/2+iy,n)\|
=(N+1)\frac{\operatorname{radial}_{N+1}(\log n)}n
$$

and the existing summed integer radial mass pay all labels together.
The maximum source growth satisfies
`log(2*10001/20000) < 1/10000`; it is strictly smaller than the proved
`1/1250` coefficient saving. The conservative final rate is `exp(-N/1600)`.
There is no prime-density approximation, separate phase replacement, or
population maximum.

## Payment in the original floor

`eventually_native_prefix_floor` spends the error exactly once:

$$
\operatorname{Re}(u^{N_j+1}\operatorname{coreResponse}_j)
\ge -\operatorname{Re}D_{N_j}^{\mathrm{prefix}}
-\operatorname{nativeSelbergBudget}_j-\operatorname{prefixBudget}(N_j).
$$

Under the existing simple exposed-zero hypotheses,
`exists_native_prefix_payment_simple` proves that the combined budget tends
to zero. The new global comparison error itself requires no zero hypothesis.

The remaining decisive theorem is still an independent cofinal bound

$$
\operatorname{Re}D_{N_j}^{\mathrm{prefix}}\le399/5000+o(1).
$$

The payment does not prove this inequality or remove the selected signed
source. It neither improves the floor constant nor establishes a zero
exclusion. The higher-multiplicity ceiling is also open. The approximately
`0.000071797` source/target difference remains a contradiction margin, not
a measured remaining error or an achieved saving on the signed main.

## Optional quantitative regression and local validation

[The optional probe](../scripts/probe_riesz_pair_prefix.py) replays the
existing actual-prime cache, keeping exact integer masks and factorial
prefixes. All 9,216 Cartesian pair incidences agree with the exact error
formula to within `2.3e-13` in floating-point arithmetic. Shared primes do
not make these independent samples. These cached `N=256` cases are below
the formal large-order threshold and provide algebraic regression only.
They certify neither an asymptotic error nor the signed floor.

The diagnostic tilt exponents are approximately `0.0009424`, `0.0063875`
and `0.0300948`. Lean certifies conservative rational rates rather than
assuming these decimals. The global proved budget is approximately
`9.45e-12` at `N=65536` and `2.77e-18` at native order `N=90112`; these
bound only the comparison error, not the main contribution.

Focused validation uses a strict explicit-leaf compile and
[the namespace/standard-axiom checker](../scripts/CheckRieszPairPrefixPayment.lean).
The module remains local and outside root registration while wider checks
are held. Probe output is stored in `.lake/riesz-pair-prefix-payment/probe.json`;
the scoped [audit](riesz-pair-prefix-payment-audit.json) records source pins
and checked results. Ordinary CI does not run the probe.
