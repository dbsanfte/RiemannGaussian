# Prime jumps, preceding error and the exact signed work

Lean now proves an exact quadratic correlation identity for the actual
integer samples of the Chebyshev discrepancy, and an independent geometric
bound for its complete local forcing diagonal. The original linear carrier's
required cofinal lower bound is still open. This is an arithmetic tool, not
a new zero-free region, an RH proof or a claim of historical novelty.

All declarations below are in
[`RiemannGaussian.PrimeDiscrepancyWork`](../RiemannGaussian/ZetaPrimeDiscrepancyWork.lean).
The module belongs to **Euler & prime structure** and is imported by the root.

## The actual arithmetic and the correlation it retains

Let

```math
\lambda_n=\begin{cases}\log n,&n\text{ prime},\\0,&\text{otherwise},\end{cases}
\qquad d_n=n-\theta(n).
```

These use ordinary primes, including their actual integer positions; proper
prime powers do not contribute. `theta_eq_sum`, `error_succ` and
`error_block` prove, at every endpoint and for every complete block,

```math
d_{n+1}=d_n+1-\lambda_{n+1},\qquad
d_{a+L}=d_a+L-\sum_{j<L}\lambda_{a+j+1}.
```

The preceding error carries every earlier prime. For arbitrary finite tests,
`prime_work_eq_ordered_pairs` gives the complex identity

```math
\sum_{n\in S}w_n\lambda_{n+1}d_n
=\sum_{n\in S}w_n\lambda_{n+1}n
-\sum_{n\in S}\sum_{j<n}w_n\lambda_{n+1}\lambda_{j+1}.
```

The inner sum includes the whole preceding prime prefix, even if `S` is a
late or disconnected set. No product cutoff is introduced. This differs
from replacing a triangular interaction by a Dirichlet convolution with
restricted products; the existing
[product-cutoff obstruction](../RiemannGaussian/SuzukiProductCutoffObstruction.lean)
explains why that replacement would need its complement.

## The exact complex-weighted energy identity

`square_increment` proves

```math
2(\lambda_{n+1}-1)d_n
=(\lambda_{n+1}-1)^2-(d_{n+1}^2-d_n^2).
```

For any complex test sequence `w`, write

```math
W=\sum_{j<L}w_j(\lambda_{a+j+1}-1)d_{a+j},\qquad
\Delta=\sum_{j<L}w_j(\lambda_{a+j+1}-1)^2,
```

```math
\Phi=w_Ld_{a+L}^2-w_0d_a^2
-\sum_{j<L}(w_{j+1}-w_j)d_{a+j+1}^2.
```

`weighted_work` proves exactly `2W+Phi=Delta`. Both boundary energies and
all changes of phase remain. The local diagonal includes the unit drift
at nonprimes as well as the prime jumps.

For decreasing real weights with `w_L>=0`, `monotone_work_le` gives the
independent upper bound `2W<=Delta+w_0*d_a^2`. Its sign hypotheses are
essential to that estimate; they are not discharged for the oscillatory
factorial detector. The complete complex identity remains available there.

## The independently controlled part

Keep the original full polynomial filter `p`, including every complex
coefficient, and put

```math
K_{p,N}(s,x)=x^{-s}\sum_{k\in\operatorname{supp}p}
 p_k\frac{(\log x)^{N+k}}{(N+k)!},\qquad
w_j=\frac{K_{p,N}(3/2+i y,a+j+1)}{a+j+1}.
```

`test` is this exact weight; the coordinate divisor is an actual parameter
shift, justified by `zetaPrimeFilterKernel_div_pow`. No phase, coefficient,
factorial or arithmetic cutoff is approximated in that identity.

The finite constant

```math
M=\sum_{n\ge1}(\lambda_n-1)^2n^{-5/4},\qquad
C(p)=M\sum_k|p_k|(4/5)^k
```

is genuinely convergent by `summable_diagonal_mass`. The proof uses only
`(lambda_n-1)^2<=1+log(n)^2` and an exponential-series majorant bounded by
`129*n^(-9/8)`. It does not use a hypothetical zero or a Chebyshev error bound.

`norm_diagonal_le` proves

```math
|\Delta_{p,N,y,S}|\le C(p)(4/5)^N
```

for **every finite index set and every real height**, with the same fixed
filter. Consequently `tendsto_scaled_diagonal` and
`tendsto_scaled_work_add_flux` prove

```math
u^{N+1}(2W_N+\Phi_N)\longrightarrow0\qquad(0\le u\le1)
```

for arbitrary moving complete blocks and heights. There is no limiting-height
or block-growth hypothesis. In particular, the integer endpoints of the
existing expanding prime band are permitted. The polynomial is fixed;
unbounded changes in its coefficient budget are not covered.

## What remains, and what this does not transport

The original source carrier is linear in `x-theta(x)`:

```math
C_N=u^{N+1}\int_{A_N}^{B_N}K'_{p,N}(3/2+i\gamma,x)
 (x-\theta(x))\,dx.
```

Its conditional source limit is `-m_rho`; the independent sufficient floor
is a fixed positive cofinal margin above that value. The new work multiplies
the centered prime forcing by an additional preceding discrepancy. Therefore
`W` is a **quadratic correlation**, not this original linear carrier. Neither
`W=-Phi/2+o(1)` nor even decay of both terms would by itself establish that
linear floor. No such transfer is asserted here.

The next useful estimate must exploit a correlation that retains the linear
resonant source, while controlling the complete signed variation and block
boundary terms. Merely integrating the recurrence back to Abel summation,
dropping a boundary energy, or observing that each squared error is
nonnegative does not provide it. See the
[information audit](signed-prime-carrier-information-audit-2026-09-12.md)
and [source-support audit](zeta-gaussian-source-support.md).

The [linear lattice transport](zeta-prime-lattice-carrier.md) now supplies
a separate route back to the original source: it pairs the full kernel
with first error increments, without the extra preceding discrepancy.
Its complete sampling error is independently geometrically small, and
the original negative multiplicity survives in the finite signed
prime-versus-integer sum. This does not convert the quadratic work above
into an independent bound for that linear sum.

## Literature checks guiding the test

Full additive prime-pair error estimates can be substantially stronger than
the one signed projection needed here. Chou, Haag, Huryn and Ledoan's
Theorem 2 relates their squared pair-error sum to the supremum of zeta-zero
real parts. Their proof retains the zero-frequency pair sum, which contains
the ordinary PNT error. Thus assuming the conjectured pair-error scale
would not supply an independent shortcut. This assessment uses the 2023
first version, not an assertion about subsequent revisions.
[The error term in counting prime pairs, v1](https://arxiv.org/pdf/2308.14888v1).

Broucke constructs generalized-prime systems with prescribed rightmost
zero contours (Theorem 1.6). These motivate testing which hypotheses use the
ordinary integers rather than generic Euler-product structure. They are not
counterexamples to the Riemann hypothesis, and we have not asserted that
they satisfy every repository hypothesis or the classical functional equation.
[On the connection between zero-free regions and the error term in the prime number theorem, v1](https://arxiv.org/html/2507.13780v1).
