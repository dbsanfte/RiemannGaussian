# Complete prime intervals and signed cell cancellation

[Larger owner windows](zeta-riesz-owner-windows.md) strengthen the
independent composite-cofactor deletion below, with a larger cutoff and
a wider source-radius range. The remaining joint signed bound stays open.

The entire original Riesz carrier now has an exact decomposition into
complete intervals of ordinary primes. Every squarefree composite has
one owner: its largest prime, with its remaining nonunit cofactor. A cell
records that cofactor and the literal set of active divisor hinges.
Its support is independent of the complex polynomial filter and height.
Zero filter values are included, so the interval has no hidden holes.

**No sufficient bound for the whole carrier, new zero-free region, or RH
proof is established here.** The result supplies a more precise arithmetic
target and finite bounds which preserve additional cancellation.

## Exact affine arithmetic, with no cell error

For `F(x)=R_L(n)-R_(L-x)(n)`, the active set is
`D={d|n : log d < L-x}`. On one cell the derivative is the signed integer
`S_D=sum_(d in D) mu(d)`. Thus `F(y)=F(x)+(y-x)S_D` exactly.
Crossing a cell boundary introduces only the signed sum of the hinges
actually crossed; the entire divisor mass is not charged again.

Multiplication by `log m` raises the factorial order exactly, retaining
the **original** band mask and the correspondingly raised polynomial.
Consequently each original cell response is

```math
C_K A_K+S_K A_K^+.
```

Both moments keep every complex phase. Their energy retains the signed
covariance; that covariance need not be negative. Taking the two norms
separately discards a correlation that is still present in the theorem.

`ZetaRieszArithmeticCells.actual_band_eq_arithmetic_cells` partitions the
whole carrier with no error or duplicated prime incidence.
`arithmeticCellResponse_eq_prime_moments` rewrites each cell as two coupled
complete prime sums. `ZetaRieszPrimeIntervals.intervalPrime_between` proves
that every prime between two members belongs to the same interval.

## Two stages of cancellation

`ZetaRieszPacketIteration` cancels disjoint packets through their complete
signed sums, using one supported scalar fraction per packet. It retains
the actual earlier fractions and all cross terms in the orientation tests.

`ZetaRieszRetainedCells.available_cell_mass_le_arithmetic_allowance`
proves that regrouping the actual arithmetic-cycle residual into exact
cells never increases the previous allowance. It applies to the full
original band, every complex polynomial, every order and every height.
The prime-by-prime residual weights in that version are explicit; an
analytic prime estimate must also pay for their irregularity.

`ZetaRieszCellCycles` offers a compatible alternative: first retain the
entire signed prime-interval response, then cancel **whole cells**.
Every cell keeps a single scalar in `[0,1]`. No internal phase-dependent
prime mask is created. For every supported finite cycle list, Lean proves

```math
|B_N|\le\sum_K|C_K A_K+S_K A_K^+|-\operatorname{cellSaving}_N.
```

The right-hand side is exactly the sum of the remaining cell norms and
is nonnegative. Independently proved bounds for the complete intervals
can be applied with their actual retained scalars, with no additional
within-interval variation penalty. This is an exact finite bound, not a
proof that enough saving occurs as the order grows.

## An independently paid, exponentially growing class

Write `a=m/P⁺(m)` for the cofactor after removing the largest prime of an
original squarefree composite label. The whole class with **composite a**
and `log a <= N/10` now has a proved absolute bound:

```math
u^{N+1}\sum_{\substack{m\in\mathcal B_N\\a=m/P^+(m)\text{ composite}\\\log a\le N/10}}
|B_{L_N,P,N,t}(m)|\le C(P,u)r^N,
\qquad r=\frac32\exp\!\left(-\frac{631}{1536}\right)<1.
```

This holds eventually for `1/2 <= u < exp(-2/3)`, for every fixed complex
polynomial P, uniformly in t. It even permits an arbitrary moving height.
The finite estimate applies at every `N>=2` once the cofactors lie below
the physical cutoff; Lean proves that condition is eventually automatic.
No numerical starting order is claimed. The explicit constant is
`C(P,u)=u*tiltConstant(P,2/3,257/256)`.

The gain uses the actual arithmetic profile: for a saturated composite
cofactor, the coefficient vanishes when the owner prime is at or above
the Riesz cutoff. All remaining products from this growing class satisfy
`log m <= 3N/2`, where the existing independent logarithmic-window estimate
applies. The original divisor majorant pays all labels at once, avoiding
an additional cost for counting the growing set of cofactors.

`ZetaRieszSmallCompositeCells.tendsto_smallOwner_cell_mass` also controls
the sum of the norms of **all corresponding complete cells**. These cells
can therefore be deleted before further cancellation. Their removal keeps
the full arbitrary-multiplicity pole-jet source in the stated range.
The remaining cells have either a prime cofactor (a semiprime original
label), or a composite cofactor with `log a > N/10`. Their joint signed
bound is still open. This component theorem is not a zero-free region.

## The remaining analytic target

All decompositions and supported cancellation lists preserve the full
pole-jet source at a hypothetical right-half zero, with arbitrary
multiplicity, no exposure assumption, and the full range `1/2<u<1`:

```math
u^{N+1}B_N\longrightarrow-m(\rho),\qquad u=\frac32-\Re\rho.
```

An independent cofinal upper allowance strictly below `m(rho)` suffices.
A cofinal real lower bound strictly above `-m(rho)` also suffices and can
retain more information than the cell-norm sum. Neither is proved yet.
The remaining objects are the coupled ordinary-prime interval moments,
their signed cofactor coefficients, and correlations between cells.

Finite floating-point experiments on the smaller physical annulus with
`P=1` are exploratory only. They are not full-band certificates, an
unbounded-order estimate, or evidence that an unevaluated source threshold
has been crossed. No exhaustive numerical verification is added to CI.
No historical novelty claim is made for the underlying identities.

The supporting `prime-cells` explorer endpoint records the checked chain.
The default RH, zero-free and numerical-certificate endpoints and both
top-ten lists remain unchanged.
