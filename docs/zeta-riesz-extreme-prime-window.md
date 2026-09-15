# Exact prime layers and the signed boundary-divisor window

Lean now separates every nonzero survivor into its complete smooth,
intermediate and extreme prime factors. A composite smooth core contributes
only through a strict physical divisor window, with every Möbius sign
retained. Saturated extreme-core coefficients have norm at most the total
logarithm, independently of the number of extreme primes.
**The full joint signed floor remains open.**

Open the [prime-layer and boundary-window theorem chain](https://dbsanfte.github.io/RiemannGaussian/rh-proof/?endpoint=extreme-prime-window)
for exact hypotheses, source lines and axiom audits. The complete support
endpoint is
[`surviving_layers_with_boundary_witness`](../RiemannGaussian/ZetaRieszSurvivingPrimeLayers.lean).
The default RH explorer remains the whole-carrier critical profile.

## Three complete prime layers

Keep the original physical cutoff and length:

```math
D_N=\left\lfloor\frac{u^{-N}}{N+1}\right\rfloor,
\qquad X_N=(D_N+2)^2,\qquad L_N=\log X_N.
```

The [large-smooth-factor deletion](zeta-riesz-large-smooth-factor-deletion.md)
has independently vanishing error on `1/2<u` and `2*u²<1`. For every
nonzero integer in that residual, Lean constructs `n=b*(q*a)` with:

| Factor | Complete prime support |
| --- | --- |
| `a` | Every prime is at most `N²`, and `a<X_N` |
| `q` | Every prime lies strictly between `N²` and `X_N` |
| `b` | Every prime exceeds `N²` and is at least `X_N` |

All factors are squarefree. Their product is the original integer, with
its original band restriction. Factorization existence is proved using
gcds with primorials at arbitrary thresholds. No prime-count restriction
is imposed on `q` or `b`. Unit factors are allowed.

## Exact elimination from the profile

Write the signed divisor profile as

```math
R_L(m)=\sum_{d\mid m}\mu(d)\max(0,L-\log d).
```

For squarefree `b*c`, if every prime of `b` has logarithm at least `L`,
then Lean proves exactly `R_L(b*c)=R_L(c)`. Each prime insertion is a
cutoff difference; its translated profile is zero at a nonpositive length.
This holds for the entire extreme factor, with any number of primes.

For a saturated core `log c<=L`, the remaining profile is `L` when `c=1`,
`log c` when `c` is prime, and zero when `c` is a composite nonunit.
The original coefficient still deletes prime integer labels. For `L>0`
this gives both its exact nonpositive sign and

```math
\left|C_L(bc)\right|\leq\log(bc).
```

The physical version includes every early order because `L_N>0` is
already proved. **Only the profile loses the extreme factor.** The factor
remains in `log(bc)` and in the original kernel's magnitude, complex phase
and factorial moments. A nonpositive coefficient does not give a sign
for the real part of the filtered sum.

## The complete signed boundary window

For a composite smooth core `a`, the original coefficient becomes

```math
C_{L_N}(bqa)=-\frac{\log(bqa)}{L_N}
\sum_{\substack{d\mid q\\ X_N<da,\ d<X_N}}
\mu(d)R_{L_N-\log d}(a).
```

This identity keeps the common physical length, exact integer floor,
complete Möbius signs and total integer. Divisors with `d>=X_N` have
nonpositive shifted length. Divisors with `da<=X_N` leave a saturated
composite profile. Both classes vanish exactly, including equality at
either edge. No norm or divisor-count replacement is used inside the
surviving window `X_N/a<d<X_N`.

For one intermediate prime `p`, the profile is exactly
`-R_(L_N-log p)(a)`. A nonzero contribution requires
`X_N<p*a` and `p<X_N`, regardless of the number of extreme primes.
For arbitrary intermediate `q`, Lean proves that a nonzero coefficient
forces an actual divisor in the displayed window with nonzero shifted
core profile. The terminal support theorem constructs that witness together
with all three complete prime layers.

## The remaining arithmetic task

| Controlled information | Still required |
| --- | --- |
| All earlier independently paid classes and their exact scale intervals | Retain their complete deletion error |
| Saturated extreme composite cores contribute zero | Control the surviving unit and prime cores with their phases |
| Saturated extreme-core amplitude is at most `log n` | Obtain a bound for the actual filtered sum |
| Composite smooth cores have an exact signed divisor window | Control its joint Möbius and prime-factor correlations |

The three-layer support statements hold for the defined residual at every
parameter. Its independent deletion error still has the stated interval;
these identities do not enlarge it. The all-scale adaptive fallback,
exact negative-multiplicity source and independent signed Euler-window
bridge remain unchanged.

The required bound is a cofinal real floor `>=-c`, for some `c<1`, for the
**whole** adaptive carrier. The compiled RH implication assumes that floor.
These exact identities and coefficient bounds do not prove it. No new
zero-free region, numerical starting order or historical novelty is claimed.
See the [family index](theorem-families/arithmetic.md),
[compiled status](proof-status.json) and
[RH explorer audit](rh-proof-explorer/audit.json). Ordinary CI does not run
the optional exhaustive numerical certificate.
