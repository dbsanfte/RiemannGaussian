# Gaussian multiplicity bounds and boundary simplicity

[ZetaGaussianMultiplicityDepth](../RiemannGaussian/ZetaGaussianMultiplicityDepth.lean)
retains a factor that the current universal Gaussian region bounds below
by one: the selected zero's actual multiplicity. The resulting theorem
restricts multiple zeros more strongly and discharges simplicity in a
larger boundary layer. It does not enlarge the region known to contain no
zeros of any multiplicity, and it does not close the signed prime-tail bound.

## The actual all-height theorem

For an actual nontrivial zero `rho=beta+i*t` of multiplicity `m>=1`, put

```math
L(t)=\log(|t|+2),\qquad
d(t)=\min\left\{\frac1{450000},\frac{32}{45L(t)}\right\},\qquad
g(m)=\max\left\{1,\frac72-\frac{8}{3m}\right\}.
```

`exact_strip_min` proves

```math
|t|\ge 10^6\quad\Longrightarrow\quad
g(m)d(t)\lt\beta\lt1-g(m)d(t).
```

The lower height is explicit; there is no upper height ceiling. The
coefficient family and every analytic and arithmetic premise are supplied
by the same complete Gaussian proof used for the universal region.

`multiplicityFactor_one`, `multiplicityFactor_two` and
`multiplicityFactor_mono` prove that `g(1)=1`, `g(2)=13/6`, and `g` is
nondecreasing at positive integer orders. Consequently `simple_of_near_edge`
proves

```math
|t|\ge10^6,\qquad
\min\{\beta,1-\beta\}\le\frac{13}{6}d(t)
\quad\Longrightarrow\quad m=1.
```

The general theorem `multiplicity_lt_of_near_edge` allows any positive
integer threshold `k`: a zero within `g(k)*d(t)` of either edge has
multiplicity strictly less than `k`. This is a bound on every actual
zero satisfying the displayed location condition, not a numerical count
certificate or a claim that such a zero exists.

## Where the gain comes from

The Gaussian scale, center and width are unchanged:

```math
w_q=\frac1{450000q},\qquad x_q=w_q/1000,\qquad B_q=4w_q^2,
\qquad q\ge1.
```

For the genuine half-Gaussian Laplace integral `H_B`,
`scaled_tangent_lower` proves, for every real `z`,

```math
H_{B_q}(w_qz)\ge q(199350-56250z).
```

Suppose the zero were within
`(7/2-8/(3*m))*w_q` of the right edge. Substituting its damping into that
inequality, then multiplying by its actual multiplicity, gives

```math
m H_{B_q}(1+x_q-\beta)
\ge q\left(150000+\frac{9675}{4}m\right).
```

The cotangent correction is at most one per copy of the zero. Its full
Poisson reserve remains nonnegative. After the first phase coefficient is
included, `selected_source_lower` proves that the complete source is at
least `48000*q`, whereas the independently proved full cost is at most
`47500*q`. This contradicts the actual signed source-budget theorem.

Taking the maximum with the previous width retains its stronger estimate
at multiplicity one. The argument applies first to every eligible phase
family with the existing coefficient enclosures; `scaled_margin` then
instantiates the repository's mathematically defined exact contact family.

## Earlier bounds and the arithmetic chain

The repository already had a simplicity layer of width
`1/(6000*log(abs(t)+22))`. The new theorem
`old_simplicity_width_lt` proves that the Gaussian simplicity layer is
strictly wider whenever `log(abs(t)+2)>=100`. No superiority is claimed
at smaller heights. The older theorem also supplies nearby-zero separation;
that additional separation conclusion is not asserted for this whole
simplicity layer. The subsequent [finite-group refinement](zeta-gaussian-zero-separation.md)
proves a Gaussian rectangle count at depth `2*d(t)` and isolation at depth
`(3/2)*d(t)`, with vertical radius `d(t)/2`.

`eta_current_eq_head` feeds the newly discharged multiplicity-one fact into
the existing exact signed eta-current theorem. It retains the complete
head and inverse-moment sum, both reflected factors and their complex
interaction. Thus a larger part of the unresolved strip now admits that
simplified representation with no assumed simplicity premise.

This does not bound the remaining signed inverse sum or prime carrier.
Possible simple zeros in this larger layer, and zeros deeper in the strip,
still require the independent arithmetic estimate. The general absolute
[error-envelope obstruction](zeta-prime-envelope-rate.md) remains applicable.

## Research decision and validation

The preceding two-scale exploration checked whether known short-interval
results supplied the required correlation bound. Matomäki and Radziwiłł's
[author survey](https://maksym-radziwill.github.io/icm.pdf), especially
Theorems 2--4 and equations (5)--(10), distinguishes RH-dependent variance
bounds from unconditional averaged cancellation and short-versus-long
interval comparisons. Those estimates do not directly provide the
fixed-frequency, source-normalized lower bound required here. No such
estimate was imported or assumed. Retaining multiplicity instead produced
the concrete location restriction proved above.

The module is root-imported. Local verification includes strict direct
elaboration, focused and full builds, whole-project declaration lint,
standard-only terminal axiom audits and regenerated proof/family metadata.
The explorer's multiplicity endpoint links the location theorem,
comparison and signed eta-current consequence; its default remains the
universal zero-free curve. Work remains local under the commit hold.
