# Exact vertical moments and the signed Euler zeta bound

The terminal theorem
[`ZetaSechEulerBound.window_bound`](../RiemannGaussian/ZetaSechEulerBound.lean)
is a bound on the **original signed zeta logarithm**, with every finite
zero singularity included. For `k>=1`, `t!=0`, `a!=0` and `l<=r`, put

```text
sigma = line_k,  H = abs(t)+2,
w(u) = 1/(2*cosh(u)^2),
Q_k(t) = log(8192)+alpha_k*log(H)+log(log(H)),
D_k(t,a) = (alpha_k+1/log(H))*abs(a)/H,
c_k(y) = log(1+4*sigma/((1-sigma)^2+y^2))/2,
M_minus = integral_l^r w(u)*log^+(1/norm(zeta(sigma+i*(t+a*u)))) du.
```

Lean proves

```text
integral_l^r w(u)*log(norm(zeta(sigma+i*(t+a*u)))) du
  <= Q_k(t)+log(2)*D_k(t,a)+8/t^2
       +2*c_k(0)*exp(-abs(t)/abs(a))-M_minus.
```

The positive logarithmic part and pole correction are genuinely integrable
on the whole real line. The signed logarithm and negative part are proved
integrable on every finite window. **No global integrability of the negative
part is assumed or asserted.**

This develops the classical vertical detector used in
[Yang, section 4](https://arxiv.org/html/2301.03165v2). It does not reproduce
the paper's complete zero-free theorem or its optimized constants, and no
historical novelty is claimed.

## Keep the original kernel when integrating

[SechVerticalMoments](../RiemannGaussian/SechVerticalMoments.lean) proves
the exact logistic representation and survival derivative:

```text
w(u) = 2*exp(-2*u)/(1+exp(-2*u))^2,
S(u) = exp(-2*u)/(1+exp(-2*u)),
S'(u) = -w(u).
```

The ordinary fundamental theorem of calculus, with the limiting endpoints
proved, gives

```text
integral_R^infinity w(u) du = S(R),
integral_Real w(u) du = 1,
integral_Real abs(u)*w(u) du = log(2),
integral_(abs(u)>R) w(u) du = 2*S(R) <= 2*exp(-2*R)  (R>=0).
```

The first-moment primitive is
`-u*S(u)-log(1+exp(-2*u))/2`. Its limit is zero at positive infinity.
The old Laplace envelope still establishes integrability, but its mass
two is no longer substituted for the actual mass one. Thus a complete
affine allowance integrates to `A+log(2)*B`, instead of `2*A+2*B`.

[ZetaSechExactMass](../RiemannGaussian/ZetaSechExactMass.lean) transports
this improvement directly to the preceding actual zeta window estimate,
retaining the entire negative logarithmic mass.

## Undo pole clearing without a global width penalty

The [direct Euler growth proof](zeta-direct-euler-truncation.md) controls
`g(s)=(s-1)*zeta(s)/(s+1)`, continued through the pole, by `exp(Q_k(Im(s)))`
on the complete line. The new theorem retains exactly

```text
c_k(Im(s)) = log(norm((s+1)/(s-1))).
```

Consequently `log^+ norm(zeta(s)) <= Q_k(Im(s))+c_k(Im(s))`, also at
zeros. The correction is continuous and nonnegative, is largest at
ordinate zero, and is at most `2/y^2` for `y!=0`.

On the central window `abs(u)<=abs(t)/(2*abs(a))`, the actual ordinate
`t+a*u` stays at distance at least `abs(t)/2` from zero. The correction
there costs at most `8/t^2`. The complementary window has exact logistic
mass at most `2*exp(-abs(t)/abs(a))`; only that tail pays `c_k(0)`.
This proves the full-line pole estimate before it is used in the signed
window bound. No tail estimate is left as an antecedent.

## Relation to the existing zero bound

The [Euler angular family theorem](../RiemannGaussian/ZetaEulerAngularPhaseFamily.lean)
already improves the existing actual zero-source budget by the exact amount

```text
2*W*log(4/delta_k)/(pi*delta_k),
```

for every eligible finite or countable family, keeping multiplicity and
the radial correction. That is a completed propagation through the
existing circular detector.

The sharper vertical bound above is a **separate input to the strip route**.
Its factor-two saving is not a proved factor-two enlargement of the current
zero-free region. The [complete right-boundary theorem](zeta-sech-phase-boundary.md)
now retains the common prime phases for every eligible summable family:
its negative nonconstant integral costs only the constant channel's
averaged mass. The [actual finite strip divisor](zeta-strip-cotangent-source.md)
and selected cotangent source limit are now proved, including the rational
pole correction and all zero multiplicities. Its signed boundary integrand
has a uniform upper envelope. The subsequent
[actual boundary-limit inequality](zeta-strip-boundary-constraint.md)
now connects the selected cotangent source to the two complete vertical
integrals, retaining arbitrary left negative depth and the full right
sign. The [complete strip family budget](zeta-strip-phase-budget.md) now
applies the sharp arithmetic estimates and rational normalization
correction, preserving the constant-channel right prime cost. It proves
an elementary bound and actual finite-height exclusion from a strict surplus.

The [displayed region](zeta-log-log-zero-free.md) is unchanged, with
coefficient-dependent thresholds that have not been numerically evaluated.
No world-best result is established. The independent cofinal ordinary-prime
lower bound above `-1` by a fixed positive gap remains open, and RH remains
unproved.

## Previous Euler-detector checkpoint

The strict full build passes 10,299 jobs. All 27 affected modules pass direct
elaboration with warnings treated as errors. The root verbose declaration
lint and whole-project linter pass. All 172 public theorems in the affected
modules have explicit axiom audits using only `propext`, `Classical.choice`
and `Quot.sound`.

The focused detector and arithmetic build passes 4,971 jobs. The compiled
inventory contains 1,452 project modules, 30,728 declarations and 26,947
theorems, with no project axioms or placeholder dependencies; `rhImplied`
remains false. The generated artifacts reproduce exactly.

These counts record the preceding Euler-detector checkpoint. The
subsequent [coupled boundary slice](zeta-sech-phase-boundary.md) adds the
actual right-boundary comparison.
