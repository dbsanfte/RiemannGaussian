# Actual zero exclusion from the complete Stechkin budget

The later [half-logarithm completion theorem](zeta-half-log-zero-free.md)
strengthens this exclusion to width `1/(24*log(abs(gamma)+22))`, exactly
`8/3` times the width below. It applies the smaller completion allowance
to the same classical square. The earlier theorem and its downstream
Euler-boundary bounds remain valid.

The compiled theorem `nontrivialZetaZero_mem_stechkin_strip` in
[ZetaStechkinZeroFree.lean](../RiemannGaussian/ZetaStechkinZeroFree.lean)
proves that every actual nontrivial zeta zero `rho=beta+i*gamma` with
`abs(gamma)>=1` satisfies

```
1/(64*log(abs(gamma)+22)) < beta < 1 - 1/(64*log(abs(gamma)+22)).
```

`riemannZeta_ne_zero_of_stechkin_margin` states the corresponding
nonvanishing theorem for the literal zeta function throughout the
closed right-edge region. Every arithmetic and analytic premise is
discharged. This is a concrete stronger zero bound in the repository.
It is not an RH proof or a claim of a new best published zero-free region.

## The signed contradiction

The general [Stechkin phase budget](zeta-stechkin-phase-budget.md) applies
to arbitrary admissible families. Here the classical exact coefficients
`(3,4,1)` provide an actual contradiction near the edge:

```
K(t)=3+4*cos(t)+cos(2*t)=2*(1+cos(t))^2 >= 0.
```

There is no coefficient search. Positivity of each actual Stechkin
prime-power amplitude gives nonnegative complete arithmetic work `W`.
The selected genuine right-half reflection pair retains its full
analytic multiplicity `m>=1`.

Put `d=1-beta`, `sigma=1+6*d`, and let `c` be the canonical Stechkin
coefficient. The compiled theorem
`zetaThreePhase_stechkin_source_add_primeWork_le` is

```
4*m/7 - 1/2 + d*W <= d*(1-c)*H + 30*d^2/gamma^2,
H=3*(1+log(sigma))+5*(1+log(sigma+abs(gamma)))+log(2).
```

The global comparison gives `c>=1/sqrt(5)>=4/9`, proved uniformly on
every sampling line `sigma>=1`. Suppose a zero violated the asserted
right margin. With `L=log(abs(gamma)+22)>3`, this would imply

```
d*L <= 1/64,
d <= 1/192,
sigma <= 33/32,
H <= (257/32)*L.
```

The exact nonreal pole allowance is retained through its estimate,
using `gamma^2>=1`. Together these give

```
d*(1-c)*H <= (1285/288)*d*L,
30*d^2/gamma^2 <= (5/96)*d*L,
right side <= 325/4608 < 1/14 <= 4*m/7 - 1/2 + d*W.
```

Thus the entire proved allowance is strictly below the source. The
genuine critical reflection supplies the identical left-edge margin.
No zeros, multiplicities, or omitted reflected pairs are assumed to
have an unproved sign.

## Comparison and propagation

The former full phase-contact margin was
`1/(15600*L+21200)`, with a simpler corollary `1/(23000*L)`.
`phaseContactZeroMargin_lt_stechkin` proves that the new margin is
strictly larger than the full former one for every height.

The stronger actual strip also improves the constants in the
[Euler-boundary estimates](zeta-stechkin-euler-boundary.md). On
`1<=sigma<=3` and `abs(t)>=5`, the complete Poisson mass is now bounded
by `325*log(abs(t)+26)`, replacing 115005, and the absolute real part of
the pole-removed logarithmic derivative by `326*log(abs(t)+26)`,
replacing 115006. The full signed boundary identities and their
infinite-family limits are retained.

## Remaining RH gap

The exclusion has the form `d > constant/log(abs(gamma)+22)`. It still
allows zeros throughout most of the critical strip, and its edge width
decreases with height. It does not force `beta=1/2`.

For hypothetical zeros farther from the edges, the same nonnegative
prime-work estimate does not beat the Gamma allowance. The active goal
still needs an independent signed arithmetic estimate that closes that
remaining region, or the full balanced Suzuki/weighted reflection bound.
The new theorem is an actual partial exclusion toward that goal; it
does not redefine the goal as merely improving an edge constant.
