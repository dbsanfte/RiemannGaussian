# Half-logarithm completion cost and a wider actual zero-free strip

Lean now proves that every genuine nontrivial zero `rho=beta+i*gamma`
with `abs(gamma)>=1` satisfies

```text
1/(24*log(abs(gamma)+22)) < beta < 1 - 1/(24*log(abs(gamma)+22)).
```

The terminal theorem is `nontrivialZetaZero_mem_half_log_strip` in
[ZetaHalfLogZeroFree.lean](../RiemannGaussian/ZetaHalfLogZeroFree.lean).
The same module proves nonvanishing of the literal zeta function on the
closed right-edge region and an exact `8/3` increase over the preceding
excluded width. Every arithmetic and analytic antecedent is discharged.

The [centered Euler eta argument](eta-centered-euler-zero-free.md) now
proves `gamma^2>3` for every genuine nontrivial zero. Thus the height
premise here is automatically satisfied. The stronger terminal theorem
`nontrivialZetaZero_mem_half_log_strip_all_heights` in
[ZetaCenteredEulerZeroFree.lean](../RiemannGaussian/ZetaCenteredEulerZeroFree.lean)
gives the same strip with no ordinate restriction.

The underlying improvement applies to all admissible phase families.
The familiar three-height square is used only to obtain an actual
contradiction and zero exclusion. No coefficient search occurs. This
improves the repository's formalized bound; no best published zero-free
region is claimed. The global RH objective remains open.

## The information recovered before the digamma bound

Write the actual regular completion as

```text
R(s) = 1/s - log(pi)/2 + digamma(s/2)/2
     = digamma(s/2+1)/2 - log(pi)/2.
```

The second equality is the already checked exact complex Gamma
recurrence. The shifted trigamma theorem proves that `Re(R(sigma+i*t))`
increases with `sigma` on the entire positive half-plane. The earlier
Euler-digamma estimate is

```text
Re(digamma(z)) <= log(normSq(z)/Re(z)).
```

Using this directly at a fixed real part puts two powers of the
ordinate inside the logarithm. Instead, first compare horizontally to
`tau=sigma+abs(t)`, retaining the exact signed monotonicity. At
`z=(tau+i*t)/2+1`, direct algebra gives

```text
normSq(z)/Re(z) <= (sigma+2+2*abs(t))/2.
```

Consequently, for every `sigma>0`,

```text
Re(R(sigma+i*t))
  <= (log((sigma+2+2*abs(t))/2)-log(pi))/2.
```

On the entire closed Euler half-plane `sigma>=1`, this implies

```text
Re(R(sigma+i*t)) <= log(sigma+abs(t))/2.
```

These are `re_zetaGlobalRegularCorrection_le_shifted_half_log` and
`re_zetaGlobalRegularCorrection_le_half_log` in
[ZetaCompletionHalfLogBound.lean](../RiemannGaussian/ZetaCompletionHalfLogBound.lean).
The former allowance was `1+log(sigma+abs(t))`. The improvement keeps
the full signed completion identity upstream; it changes neither the
zeta function nor the genuine zero divisor.

## All-family signed budget

For the same Stechkin coefficient `c` and auxiliary abscissa as before,
horizontal monotonicity gives

```text
Re(R(sigma+i*t)) - c*Re(R(auxiliary+i*t))
  <= (1-c)*log(sigma+abs(t))/2.
```

The exact prime work, pole family, and full nonnegative reflected zero
mass therefore satisfy this smaller allowance for every nonnegative
summable coefficient family of real frequencies, with the stated
logarithmic height moment. The theorem
`zetaPhase_stechkin_primeWork_add_zeroMass_le_half_log` retains all zeros
and their analytic multiplicities before selecting a source.

For integer frequencies, let `a0` and `a1` be the first two coefficients,
`A` the remaining-frequency mass, and `B` the logarithmic frequency
moment. For every `kappa>0`, put `d=1-beta`, `sigma=1+kappa*d`.
The complete normalized budget is

```text
a1*m/(kappa+1) - a0/kappa + d*primeWork
  <= d*(1-c)*(a0*log(sigma)+A*log(sigma+abs(gamma))+B)/2
     + kappa*A*d^2/gamma^2.
```

This is `phase_shifted_source_add_primeWork_le_stechkin_half_log`.
It applies to every admissible family. The exact signed arithmetic work
and full multiplicity source remain present; no arithmetic floor is
assumed in that theorem.

## The independent edge contradiction

Use the existing exact square

```text
3+4*cos(theta)+cos(2*theta) = 2*(1+cos(theta))^2 >= 0.
```

Every actual Stechkin prime-power amplitude is nonnegative, so the
complete prime work `W` is nonnegative. At `kappa=6`, the new source
theorem specializes to

```text
4*m/7 - 1/2 + d*W <= d*(1-c)*H + 30*d^2/gamma^2,
H=(3*log(sigma)+5*log(sigma+abs(gamma))+log(2))/2.
```

Suppose `d<=1/(24*L)`, where `L=log(abs(gamma)+22)>3`.
Then `d*L<=1/24`, `d<=1/72`, and `log(sigma)<=1/12`.
The already proved `c>=4/9` and `gamma^2>=1` give

```text
H <= (65/24)*L,
d*(1-c)*H <= (325/216)*d*L,
30*d^2/gamma^2 <= (5/36)*d*L,
right side <= 355/5184 < 1/14 <= 4*m/7 - 1/2 + d*W.
```

Thus an independent arithmetic floor and the complete proved allowance
contradict the full selected-zero source in this region. Actual critical
reflection supplies the same exclusion from the left edge. The proof
includes every analytic multiplicity and all omitted zero and prime
terms have independently proved signs.

## The remaining goal

The excluded edge width is still reciprocal-logarithmic and shrinks
with height. Most of the right half of the critical strip remains
allowed. The half-logarithm estimate reduces the required arithmetic
floor for all families, but does not prove the stronger floor needed
throughout that interior region.

On the Suzuki route, the [compact source bound](suzuki-compact-source-decay.md)
still leaves the full positive source at the reflected node. This
slice neither bounds that local source below itself nor changes its
proved positive radial profile. The active objective remains one
independent source-beating signed inequality for every hypothetical
right-half zero, rather than only the wider edge region proved here.
