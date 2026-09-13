# Common Gaussian prime work and the ceiling for weighted blocks

[ZetaGaussianPrimeBlocks](../RiemannGaussian/ZetaGaussianPrimeBlocks.lean)
keeps the three original prime responses on one common arithmetic measure.
It proves an independent floor from disjoint prime-power blocks and
transports that floor into the actual finite-zero-group inequality.
It also proves a ceiling for the entire class of triangular block
minorants, including growing prime sets and moving coefficient families.
The independent centered-carrier lower bound and RH remain open.

## One prime measure, with the original amplitudes

Let `P(v)=sum_n a_n*cos(omega_n*v)`, with nonnegative summable coefficients.
For the existing strip parameters, write `eta=halfWidth(k,x)`,
`b=verticalScale(k,x)` and `sigma_R=rightLine(k,x)`. At positive prime powers,

```math
\begin{aligned}
W_G(m)&=\Lambda(m)m^{-(1+x)}e^{-B(\log m)^2},\\
W_E(m)&=\Lambda(m)m^{-\sigma_R},\\
W_S(m)&=\frac{\Lambda(m)}{\log m}m^{-\sigma_R}
                  \operatorname{attenuation}(b\log m),\\
W(m)&=W_G(m)+\frac{24B}{\eta^2}W_E(m)+\frac{W_S(m)}{2\eta}.
\end{aligned}
```

For `B>0` and `x>0`, the whole measure is nonnegative and summable.
`hasSum_mixedWork` and `constantWork_eq_sum` prove exactly

```math
\mathcal W(t)=\operatorname{mixedWork}(t)
 =\sum_m W(m)P(t\log m),\qquad
\operatorname{constantWork}=\sum_m W(m).
```

Both prime and frequency sums retain their full convergence proofs.
Nonnegativity of `P` is used only for the downstream floor. This is the
original `mixedWork`, not a new carrier substituted for it.

## Disjoint blocks retain triangular phase information

Assume `omega_0=0` and `P(v)>=0`. Let `A=sum_n a_n`. For an initial block
`p,p^2,...,p^H`, define

```math
R_H=\max\left\{0,\frac{(H+1)((H+1)a_0-A)}2\right\}.
```

The existing
[`zetaPhase_weighted_returns_le`](../RiemannGaussian/ZetaPhaseWeightedRecurrence.lean)
retains the triangular multiplicity of every phase difference in a Gram
block. This is the stronger weighted recurrence already in the repo;
the new result does not replace it with the weaker separate-return bound.

Choose any nonnegative `c_p` satisfying the finite, checkable inequalities

```math
(H_p+1-j)c_p\le W(p^j)\qquad(1\le j\le H_p).
```

`block_lower` pays for `c_p*R_(H_p)` using only that block's own terms.
`blocks_disjoint` uses unique prime factorization to prove that distinct
prime bases cannot share a positive power. Hence `blocks_lower` proves
simultaneously for every finite set `S` of distinct primes,

```math
\sum_{p\in S}c_p R_{H_p}\le\mathcal W(t).
```

Each prime can have its own length and coefficient. No factor counting
the number of primes is lost, and the full prime sum is not charged
separately for each block.

There is a fully discharged positive choice:

```math
c_p^G=(\log p)p^{-(1+x)H_p}
                e^{-B(H_p\log p)^2}.
```

`gaussianCoefficient_triangle_le` proves every required amplitude
inequality for this choice. Thus `gaussian_blocks_lower` is an independent
arithmetic bound with no unproved minorant premise. A sufficiently long
block has positive reserve when `a_0>0`; `mixedWork_pos` proves strict
positivity of the actual coupled work at every height.

`finite_source_add_blocks_le_budget` inserts these same explicit blocks
into the original Gaussian inequality:

```math
a_1\sum_{\rho\in Z}\mathcal Q(\rho)
 +\sum_{p\in S}c_p^G R_{H_p}\le\mathcal B_{\rm exact}.
```

The actual finite zero group, multiplicities, ordinate displacements,
pole/completion terms and signed boundary budget retain their original
hypotheses. This is stronger than discarding all arithmetic work.

## A ceiling for the entire triangular-minorant class

Now use the original dilation family
`k=9`, `B=gaussianScale(q)`, `x=shift(q)`, `q>=1`.
`scaled_blocks_ceiling` proves, when `a_0>=0` and `A>=2*a_0`,

```math
\sum_{p\in S}c_pR_{H_p}
\le432a_0\Re\left(-\frac{\zeta'}{\zeta}(2)\right).
```

This applies to every triangular minorant satisfying the displayed
finite amplitude inequalities, including minorants of the *combined*
three responses. It is not restricted to `c_p^G`.

The proof isolates the reason:

- Blocks of length zero or one have zero reserve when `A>=2*a_0`.
- Every longer block has `c_p<=W(p^H)` by its last amplitude inequality.
- `scaled_amplitude_prime_power_le` bounds this whole combined amplitude
  by `96*log(p)*p^(-H)`, uniformly in the dilation.
- `weighted_damping_le` proves
  `(H+1)^2*log(p)*p^(-H)<=9*log(p)*p^(-2)` for every `H>=2`.
- The sum over distinct primes is bounded by the genuine convergent
  Euler mass `Re((-zeta'/zeta)(2))`. The growing number of blocks costs
  no unproved summation exchange.

For every nonnegative summable family in the current enclosures
`a_0<=37/200` and `a_1>=79/250`, the full mass satisfies `A>=2*a_0`.
`eligible_blocks_ceiling` therefore gives the uniform bound

```math
\sum_{p\in S}c_pR_{H_p}
\le\frac{1998}{25}\Re\left(-\frac{\zeta'}{\zeta}(2)\right).
```

No numerical enclosure of the fixed Euler value is claimed or needed.
The ceiling is independent of height, dilation, prime cutoff and block
lengths. Finally, `tendsto_normalized_block_reserves` proves

```math
\frac{1}{q_N}\sum_{p\in S_N}c_{N,p}R_{N,H_{N,p}}\longrightarrow0
\qquad(q_N\longrightarrow\infty).
```

The coefficient family itself may change with `N`, subject to the same
enclosures; prime sets may grow and lengths and minorants may change
independently. Thus enlarging this class of weighted block certificates
cannot produce a fixed positive fraction of the growing Gaussian budget.

This is **a ceiling on the guaranteed block reserve, not on the actual
prime work**. The two inequalities are `reserve<=work` and
`reserve<=constant`; they do not imply `work<=constant`. The theorem also
does not classify every possible per-prime inequality or other recurrence.
Finite-height gains from the explicit positive reserve remain valid.

## Research consequence and verification

The next leading-scale estimate must use information beyond these
independent triangular minorants. The
[anchored prime-correlation transport](zeta-gaussian-prime-correlation.md)
now isolates the exact cosine energy using both prime ratios and products.
Its independent upper gap, a joint gain with the signed boundary mean,
and new arithmetic constraints remain targets. Their usefulness must be
proved for the actual source;
the [carrier audit](signed-prime-carrier-information-audit-2026-09-12.md)
records the relevant interfaces and the weaker cofinal signed target.

This module makes no historical novelty, new zero-free-region or RH claim.
It is root-imported, its public declarations are included in the compiled
inventory, and the explorer's **Prime work** endpoint separates the
actual source-floor transport, strict positivity and minorant ceiling.
The default explorer endpoint remains the zero-free curve. All work
remains local under the commit hold.
