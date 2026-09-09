# An independent bound for proper-prime-power work

`SuzukiProperPrimePowerWork.lean` bounds the complete contribution from
proper prime powers to the unchanged Suzuki work. **The signed correlation
at ordinary primes is still open. No zero exclusion or RH proof follows
from this estimate alone.**

For cell `j`, put `n=j+3`, `a_j=Lambda(n)/sqrt(n)` and let `r_j` be the
original canonical center of the full prefix ending at `n-1`. The work is
`I_j=a_j*(log(n)-r_j)`. Split its prefix by the new atom's support:

```text
W(N) = W_prime(N) + W_power(N),
```

where `N=count+2`, `W_prime` selects ordinary primes, and `W_power` selects
proper powers `p^k` with `k>=2`. Integers that are neither primes nor prime
powers have zero von-Mangoldt weight. Both terms retain every preceding
prime power in the old prefix mass and keep the same canonical centers.
This is not a replacement of `psi` by `theta` inside the nonlinear work.

The independent arithmetic input is an explicit Chebyshev estimate:

```text
psi(x)-theta(x) <= 18*sqrt(x)                  (x>=1).
```

Lean derives it from the existing comparison with `psi(x^(1/2))`,
`psi(x^(1/3))`, `psi(x^(1/5))` and the unconditional bound `psi(y)<=6*y`.
Finite Abel summation, including its endpoint, then proves

```text
P(b) = sum_{p^k<=b, k>=2} log(p)/sqrt(p^k)
     = b^(-1/2)*(psi(b)-theta(b))
       + (1/2)*integral_1^b x^(-3/2)*(psi(x)-theta(x)) dx
     <= 18+9*log(b).
```

The proved canonical-center localization gives `|I_j|<=5*a_j`.
Consequently, before any cancellation among proper prime powers,

```text
sum_{j<count, j+3 a proper prime power} |I_j| <= 90+45*log(N),
|W_power(N)| <= 90+45*log(N).
```

The finite mass-log work `L_j` from the
[summable replacement](suzuki-mass-log-work.md) satisfies `|L_j|<=6*a_j`,
giving the parallel bound `108+54*log(N)` on its absolute contribution.
The constants are exact checked bounds, not numerical fits.

Both the full absolute proper-prime-power work and its signed sum, divided
by `N^epsilon`, tend to zero for every fixed `epsilon>0`. The main checked
declarations are:

- `suzukiProperPrimePowerMass_eq_abel`
- `suzukiProperPrimePowerMass_le_log`
- `sum_abs_suzuki_proper_prime_power_linearWork_le_log`
- `sum_abs_suzuki_proper_prime_power_massLogWork_le_log`
- `suzuki_signed_work_eq_ordinary_add_proper`
- `suzuki_proper_prime_power_absoluteWork_div_rpow_tendsto_zero`
- `suzukiProperPrimePowerWork_div_rpow_tendsto_zero`

There is a threshold issue in using this split with the earlier
[RH criterion](suzuki-bounded-work.md), which accepts a finite constant floor
for the full work. A finite floor `W_prime(N)>=-B` gives only

```text
W(N) >= -(B+90+45*log(N)).
```

`suzuki_signed_work_lower_of_ordinary_lower` records exactly this allowance.
It does not invoke the constant-floor RH theorem. The separate
[logarithmic-allowance theorem](suzuki-logarithmic-work.md) now absorbs this
loss by proving the active-cell transfer to an affine time floor and applying
positive Laplace continuation after a genuinely integrable compensation.
An eventual logarithmic lower bound for ordinary-prime work therefore
suffices for RH, with this entire proper-prime-power allowance included.
That ordinary-prime bound remains open. No positive-power source from the
earlier eta carrier is transferred to this different Suzuki work.

The module is imported by the root library. Validation remains local under
the user's instruction to hold commits.
