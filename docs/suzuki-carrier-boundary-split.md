# Separated Suzuki integrals with the real poles retained

The modules [SuzukiCarrierPrincipalValue.lean](../RiemannGaussian/SuzukiCarrierPrincipalValue.lean)
and [SuzukiCarrierBoundarySplit.lean](../RiemannGaussian/SuzukiCarrierBoundarySplit.lean)
close the real-axis separation step following the
[local residue calculation](suzuki-carrier-local-cancellation.md).
Every actual mixed carrier Gram now has a split into two ordinary,
absolutely integrable channel integrals. The exceptional repeated real
nodes have proved symmetric principal values. This is an unconditional
analytic interface, not an independent global bound or a new zero exclusion.

## Real-node subtraction and principal values

Write `C=i*A/(A+i*A')` off its denominator divisor, retaining the original
totalized carrier everywhere. Put `C_sharp(z)=conj(C(conj(z)))`. For a
genuine real spectral xi node `a` of analytic multiplicity `m`, define

```text
c_a(x) = 1/[m*(x-a)*(1+(x-a)^2)],
F_a(x) = C(x)/(x-a)^2 - c_a(x).
```

The prior local theorem supplies
`C(z)/(z-a)^2=1/[m*(z-a)]+p(z)` with `p` analytic near `a`.
Consequently `F_a` is bounded near the center, including its literal
assigned value there. The already proved carrier bound `|C(x)|<=1`
controls its tail by a constant times `1/(x-a)^2`. An explicit compact
plus Cauchy majorant proves `F_a` absolutely integrable on the full real
axis. No simplicity or RH assumption is used.

`integrable_suzukiXiRealNodeRegularizedChannel` proves this statement.
Conjugation gives the other integrable channel with exactly the same
counterterm, by `integrable_suzukiXiRealNodeRegularizedSharpChannel`.

For every `epsilon>0`, both the original carrier quotient and the
counterterm are integrable on `|x-a|>=epsilon`. Reflection about `a`
negates `c_a`, so its integral over that set is exactly zero. Thus

```text
integral_(|x-a|>=epsilon) C(x)/(x-a)^2 dx
  = integral_(|x-a|>=epsilon) F_a(x) dx.
```

Dominated convergence for the integrable remainder proves

```text
PV integral C(x)/(x-a)^2 dx = integral F_a(x) dx,
PV integral C_sharp(x)/(x-a)^2 dx = conj(integral F_a(x) dx).
```

The limits use all positive real cutoffs tending to zero, not merely
a selected sequence. The compiled entry points are
`suzukiXiRealNode_exterior_integral_eq_regularized`,
`tendsto_suzukiXiRealNode_principalValue`, and
`tendsto_suzukiXiRealNode_sharp_principalValue`.
The full real line outside the gap is integrated at every stage; there
is no unproved outer-tail limit in these statements.

## Mixed entries and the complete matrix

For distinct genuine nodes `a,b`, a safe Cauchy factor gives the exact
almost-everywhere identity

```text
C(x)/[(x-a)*(x-b)]
  = ((a-i)*C(x)/[(x-a)*(x-i)]
     -(b-i)*C(x)/[(x-b)*(x-i)])/(a-b).
```

Each term on the right is an `L2` zero function times an `L2` nonreal
Cauchy kernel. Their integrability is therefore unconditional even when
both original nodes are real. For a repeated nonreal node, the same
`L2` product argument applies directly. The only remaining case is the
repeated real node handled above. The reflected channel is treated with
both node reflections kept.

In the actual Gram convention, set

```text
D_(rho,sigma)(x) = (x-conj(alpha_rho))*(x-alpha_sigma),
c_(rho,sigma)(x) = c_(alpha_sigma)(x)
  if conj(alpha_rho)=alpha_sigma and Im(alpha_sigma)=0, and 0 otherwise,
F_(rho,sigma) = C/D_(rho,sigma) - c_(rho,sigma),
G_(rho,sigma) = C_sharp/D_(rho,sigma) - c_(rho,sigma).
```

`integrable_suzukiXiRegularizedGramChannel` and
`integrable_suzukiXiRegularizedGramSharpChannel` prove integrability
for every genuine pair. `suzukiXiRegularizedGramChannel_sub_sharp`
retains the exact pointwise identity with the original continuation:

```text
(F_(rho,sigma)-G_(rho,sigma))/(2*i) = K_(rho,sigma).
```

The terminal theorem
`suzukiXiBoundaryCarrierGramKernel_eq_regularized_split` proves

```text
H_(rho,sigma) = [integral F_(rho,sigma) - integral G_(rho,sigma)]/(2*i)
```

for every pair, without an orthogonality premise. This matrix statement
retains all mixed entries; it is not restricted to one coefficient family.

## Poles still needed in a global argument

The subtraction is useful on the real line, but its meromorphic extension
also has known poles away from that line. Lean proves the exact identity

```text
1/[m*(z-a)*(1+(z-a)^2)]
  = 1/[m*(z-a)] - 1/[2*m*(z-a-i)] - 1/[2*m*(z-a+i)]
```

away from its three named poles, in
`suzukiXiRealNodeCounterterm_complex_partialFractions`. A contour
calculation of either regularized channel must retain these extra terms
at `a+i` and `a-i`. They cancel in the complete signed integrand, but
that does not justify omitting them when closing channels on different
sides of the axis.

The subsequent [global xi expansion and carrier bounds](xi-global-expansion-carrier-bounds.md)
now exclude zeros of `A+i*A'` for `Im z >= 1/2` and zeros of `A-i*A'`
for `Im z <= -1/2`. Both corresponding outer horizontal integrals vanish
with bound `8/T`. Possible carrier poles in the remaining upper and lower
half-strips still need their residues retained. The vertical sides are
also open. No half-circle indentation formula or complete contour closure
is asserted by the real principal-value theorem.

The next global step must compare the actual arithmetic signal with the
screw kernel while controlling these oriented pole and boundary terms.
The resulting signed estimate must reach the existing subexponential
compensator, or the independent balanced-cutoff bound must be proved
directly. Positivity of the actual boundary Gram alone still does not
provide either estimate. These local analytic arguments are classical;
no historical novelty claim is made for them.
