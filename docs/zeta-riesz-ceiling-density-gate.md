# What the joined ceiling still needs

The independent **42/25 = 1.68 ceiling remains open**. This slice gives a
checked negative test of a generic positivity/common-phase argument, with
**zero new arithmetic ceiling credit**. It preserves the preceding central
coefficient saving and every earlier payment and no-go.

The proof is
[ZetaRieszCeilingDensityAudit.lean](../RiemannGaussian/ZetaRieszCeilingDensityAudit.lean).
It does not identify its continuous density with the ordinary-prime measure,
complete a literal masked packet, or assert a counterexample to zeta.

## The unpaid expression is still signed

With the existing normalized ordinary-prime array `a`, let
`K=floor(13N/32)` and `lambda=(N+1)/(u L_N)`. After the independently paid
errors, the current upper expression is

```math
a_N-\sum_{k=K+1}^{N-K}\frac{a_{k-1}a_{N-k}}{N+1-k}
 +\lambda\sum_{k=1}^{N+1-K}\frac{a_{k-1}a_{N+1-k}}{N+2-k}.
```

`current_join_eq` matches this exactly to the existing trace/harmonic APIs.
The Selberg trace has already cancelled. The low orders and the upper
endpoint have not been deleted. The `2/11` coefficient inequality in the
previous slice concerns the central price; it does not bound this complete
real expression by `1.68`.

If `a_k` converges to `-2`, this same expression converges to
`-2+4*retainedCost(u)`. At the radius ceiling that is approximately
`1.680512811860223288`. Source convergence and adjacent-order decay thus
leave the double source above the target. They cannot be spent again as a
fixed negative credit.

## A positive common-phase countertest with the usual leading density

Use `u=10001/20000`, any fixed `|y|>=1`, and the continuous density

```math
\nu(T)=\frac{e^T-4e^{(3/2-u)T}\cos(yT)}{T},\qquad T>40000.
```

Lean proves strict positivity on that entire half-line. Indeed
`(u-1/2)T>2`, so the leading exponential is more than four times the
oscillatory amplitude. It also proves the exact normalization

```math
Te^{-T}\nu(T)-1=-4e^{-(u-1/2)T}\cos(yT),
\qquad |Te^{-T}\nu(T)-1|\le4e^{-(u-1/2)T}.
```

There is no extra real exponential term in this density. This repairs that
specific limitation of the earlier whole-half-line renewal model. It does
**not** repair the missing ordinary-integer/prime interpretation or assert
the exact integer Selberg convolution for this model.

Every logged factorial order uses the same physical density and phase:

```math
D_k=u^{k+1}\int_{40000}^{\infty}
 \frac{T^{k+1}}{k!}e^{-(3/2+iy)T}\nu(T)\,dT.
```

The proof establishes an exact integral identity
`D_k=2*densityMoment_k-tailLeg_k`, retaining the unshifted lower-threshold
channel. Consequently `D_k -> -2`. No independently prescribed low-order
entries or separate limiting prime legs define this array.

`joined_double_tendsto` then gives the double source for the existing joined
expression. `double_cofinal_ceiling_impossible` proves that a cofinal ceiling
`1.68+err_j`, with `err_j -> 0`, is impossible for this **continuous model**.
This is stronger than a finite numerical overshoot, but supplies no reverse
inequality for the actual arithmetic carrier.

The lesson is specific: positivity, leading smooth-density normalization,
a fixed archimedean phase, full factorial-order coupling, and the algebraic
trace join do not justify the desired ceiling. A successful estimate needs
an additional property of the literal ordinary-prime/integer measure.

## The numerical gate exposes a long transient

The optional probe retains the finite lower threshold, all low orders,
the actual moving length and both conjugate channels. At height 54 its
model values are:

| Order `N` | Joined real expression |
| ---: | ---: |
| 65536 | -0.420077 |
| 262144 | 1.222824 |
| 16777216 | 1.673636 |
| 134217728 | 1.679654 |
| 268435456 | 1.680083 |
| 1073741824 | 1.680405 |
| Limit | 1.680513 |

These are **not prime measurements**. For very large orders the regression
retains exact low orders through 65536 and replaces later model orders by
`-2`, with a separately displayed recurrence/Chernoff tail majorant. The
moving-length floor is evaluated explicitly through order 65536 and enclosed
thereafter using `floor(X)+2 in (X+1,X+2]`, where `X=u^-N/(N+1)`. The
`-2log(N+1)` term remains; the saddle is not frozen. These numerical
enclosures are not kernel-certified entry-order bounds.

An independent 80-digit recurrence replay checks 20 rows without importing
the producer or using its floating Poisson routines. Early floating zeros
are labelled as underflow, not exact vanishing. Apparent success at a large
finite order can therefore be a transient even in a positive, phase-coupled
model that provably fails cofinally.

## Multiplicity literature does not pay this target

[Ivić's 1999 paper](https://arxiv.org/pdf/math/0501434), Theorem 3, gives an
upper multiplicity estimate involving both horizontal distance from one and
height. [His 2017 preprint](https://arxiv.org/pdf/1706.08268v1), Corollary 1
on page 10, makes a related bound explicit, eventually for large height:

```math
m(\beta+i\gamma)\le
4\log\log\gamma+20(1-\beta)^{3/2}\log\gamma.
```

At fixed `beta=19999/20000` this grows with height. Even its limiting
zero-gap expression retains `4loglog(gamma)`, so it does not force `m<2`.
The probe evaluates the expression only; the paper's unspecified entry
height is **not** converted into a finite-height certificate.

The repo already has
[`ZetaGaussianMultiplicityDepth.simple_of_near_edge`](../RiemannGaussian/ZetaGaussianMultiplicityDepth.lean),
but its simplicity layer also depends on height. Neither input supplies the
fixed-strip, all-height ceiling. Average simple-zero proportions likewise
do not exclude every possible multiple zero in that strip.

This is an applicability audit of these inputs, not a claim that every
possible literature method has been ruled out. No new literature theorem
has been imported into Lean.

## Local validation and remaining goal

The new leaf has focused namespace-linter and transitive-standard-axiom
checks. Its optional producer/checker remain outside builds and CI. The
existing arithmetic sources and prior audit artifacts are unchanged.

The active objective remains the independent signed `1.68` ceiling for
`joinedPhysical`, with its original masks and cofinal order schedule. The
unpaid step is an actual-prime constraint that bounds the combined ordinary-
prime, central and exterior terms. Another generic source-limit argument,
smaller adjacent-order price or finite positive-model scan cannot supply it.
No commit, push, root registration, wider gate, new zero exclusion or RH
claim is made here.
