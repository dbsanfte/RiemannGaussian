# Decay of the complete many-prime contribution

Lean now pays the **whole signed integer contribution** above a growing
prime-count threshold, including all frequencies. This strengthens the
[earlier natural-window deletion](zeta-riesz-prime-count-frequency.md).
Its actual central-band corollary is
[`tendsto_manyPrimeResponse_moving`](../RiemannGaussian/ZetaRieszPrimeCountMass.lean).
The independent joint bound for the surviving lower counts and tapered
wing remains open. No zero-free region follows from this component result.

## The whole arithmetic allowance

Write `k(n)` for the number of distinct prime factors and retain the
original coefficient `c_L(n)` and full polynomial factorial filter
`K_(P,N)(3/2+iy,n)`. For any finite squarefree selection `D` in the original
logarithmic band with `k(n) >= K`, any positive `L`, `0 <= u <= U`,
`0 < q < 1/2` and `r >= 1`, Lean proves

```math
\begin{gathered}
F(P,q)=\sum_{j\in\operatorname{supp}P}|P_j|q^{-j},\qquad
M(\sigma)=\sum_{n\in\mathbb N}\mathrm{zetaPrimeExpWeight}(\sigma,n),\\
\left|u^{N+1}\sum_{n\in D}c_L(n)K_{P,N}(3/2+iy,n)\right|
\le 32U\log2\,F(P,q)\,N\left(\frac Uq\right)^N
       \frac{\exp(2rM(3/2-q))}{r^K}.
\end{gathered}
```

The natural-index envelope `M(sigma)` is genuinely summable for `sigma>1`.
The bound includes every divisor choice, polynomial coefficient, factorial
shift and source factor. It is independent of the height and the selected
finite subband. No hypothetical zero is used.

The prime-count exponential moment supplies the new saving:

```math
\sum_{n\in D}2^{k(n)}e^{-\sigma\log n}
 \le r^{-K}\exp(2rM(\sigma)).
```

For squarefree integers, the complete prime-factor set identifies the
integer uniquely. This injects the selected mass into the finite Euler
product with local factors `1+2r exp(-sigma log p)`. Bounding that product
by the exponential of its full mass proves the inequality. The factor
`2^k` pays all divisor choices. This is a standard exponential-moment
argument, with no historical novelty claim.

## The Euler cost is paid too

Use the already checked schedules

```math
K_j=2^{j+3},\qquad N_j=8(j+4)K_j,\qquad
K_j^{K_j}\ge(17/16)^{N_j}.
```

Setting `r=K_j` gives the complete bound

```math
C(P,U,q)N_j
 \left(\frac{16U}{17q}\right)^{N_j}
 \exp\bigl(2K_jM(3/2-q)\bigr),\qquad
C(P,U,q)=32U\log2\,F(P,q).
```

The remaining Euler exponential is subexponential in the moment order:
`eventually_exp_count_le_geometric` proves that every fixed `exp(C K_j)`
is eventually at most `s^(N_j)` for every `s>1`. For each fixed
`0<U<17/32`, choose `16U/17<q<1/2` and then a sufficiently small geometric
slack. The complete allowance tends to zero. Its starting order is not
numerically evaluated.

`tendsto_normalized_many_sum` allows arbitrary moving heights, radii in
`[0,U]`, positive physical lengths and finite squarefree subbands. The
actual central-band corollary discharges these support conditions for
`manyPrimeBand`, retaining every previous arithmetic mask and the literal
floor-dependent length. The count threshold grows; no fixed small-count
class or proportion of the carrier has been proved negligible.

## The remaining source has two parts

The full many-prime response is exactly its genuine signed frequency
integral. Removing it leaves all frequencies of the original class
`3 <= k < K_j`, coupled to the unchanged wing. Under the original exposed
right-half-zero assumptions, with `u=3/2-Re(rho)<exp(-2/3)` and full analytic
multiplicity `m`, `tendsto_few_add_wing_source` proves

```math
u^{N_j+1}\left(
 \frac1{2\pi}\int_0^\infty F_{3\le k<K_j,N_j}(\xi)\,d\xi+V_{N_j}\right)
 \longrightarrow -m+m^2c(u).
```

Here `c(u)` is the existing paid harmonic cost. The independent joint
bound for **the lower-count signed integral and the tapered wing** is the
remaining arithmetic obligation. Their mutual phases and signs remain
available. Multiplicity is unrestricted; the quadratic cost cannot be
silently replaced by the simple-zero case. The component ceiling `17/32`
is not a zero-free boundary or an enlargement of the source range.

## Frequency pieces remain controlled separately

[`ZetaRieszPrimeCountWindow`](../RiemannGaussian/ZetaRieszPrimeCountWindow.lean)
also proves an independent bound for every frequency prefix of the selected
class. For `k>=B^2`, its paired quotient has allowance
`2|xi|^2 log(n)^4/B^(B^2+4)` throughout `|xi| log(n)<=B`. Thus the entire
prefix up to `B*3/(8(N+1))` has full arithmetic allowance divided by
`B^(B^2+1)`.

For `B=2^(j+3)` and `N=8(2j+7)B^2`, every moving prefix of this enlarged
window tends to zero, uniformly over moving heights and radii in any
fixed interval below `33/64`. Lean checks `exp(-2/3)<33/64`. The earlier
shrinking all-count sector and this enlarged sector are combined by
subtracting their exact overlap; `tendsto_two_cutoff_source` preserves
both complementary integrals and the original wing. These prefix bounds
retain control of frequency pieces alongside the stronger whole-integer
deletion. All intervals have genuine integrability proofs.

## Validation

Both modules belong to the ordinary root. Strict Lean compilation, full
root lint and transitive axiom audits cover all 40 declarations using only
`propext`, `Classical.choice` and `Quot.sound`. The optional exhaustive
numerical certificate is not run. The default whole-carrier endpoint,
proved zero-free region and numerical certificate remain unchanged.

The [supporting explorer](https://dbsanfte.github.io/RiemannGaussian/rh-proof/?endpoint=whole-prime-count-decay)
provides compiled statements, exact source lines and proof audits after
publication.
