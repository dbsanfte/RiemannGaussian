# Whole-ideal cancellation and literal determinant phases

2026-10-19. This checkpoint freezes two specific shortcuts and records a
third paper-level source obstruction. It proves no new RH inequality or
zero-free region. The imported strict `Re(s)>7/8` endpoint is unchanged.
The [validation record](arithmetic-operator-joined-dual-valuation-gates.json)
distinguishes checked finite arithmetic from conditional analytic estimates.

## The whole Möbius–Ramanujan join

[QuasiRHJoinedRamanujanAudit.lean](../scripts/QuasiRHJoinedRamanujanAudit.lean)
proves, using the actual primitive trace, quotient units and ideal CRT,

```
mu(I) * sum_(v in (O/I)^units) psi_I(nv)
  = product_(P|I) (if P|n then 1-NP else 1).
```

Here I is an actual admissible squarefree Eisenstein ideal. Every
numerator, including zero, nonunits and proper powers, is retained. On
paper this is `mu(gcd(I,(n)))*phi(gcd(I,(n)))`. The theorem uses the
literal unit sum, not a divisor surrogate defined to satisfy the identity.

The checked consequence is particularly sharp: when `(n)` is prime and
`Nn>NI`, the complete coefficient equals **one**. Thus if the numerator
is beyond the entire ideal annulus, the whole signed ideal sum is exactly
the corresponding sum with numerator one. External cusp/ray phases,
the moving profile and the same-weight Patterson correction remain.
This does not assert positivity of that weighted sum.

For fixed n and a fixed genuine unitary Hecke character eta, the Euler
series of the unmodeled coefficient is, on its absolute domain,

```
L_E(s,eta)/L_E(2s,eta^2)
 * product_(P|n,P outside E)
     (1-(NP-1)eta(P)(NP)^(-s))/(1+eta(P)(NP)^(-s)).
```

E is the fixed excluded-prime set. In the principal sector the density
factor is `delta_E(n)=product_(P|n,P outside E)1/(NP+1)`.
For a pure norm phase the pole is shifted; absorb that phase into the
smooth profile rather than deleting it. General arbitrary masks or the
nonmultiplicative Patterson factor are not Hecke characters.

The density is inexpensive: for every epsilon>0 its squared sum up to
K is `O(K^epsilon)`, by its absolutely convergent prime-power Euler
product. Conditional on the previously specified full theta energy and
native analytic bridge, the density contribution costs

```
Q^(-1/12)Y^(-1/3) = Z^(-11/48+d/2).
```

That is a useful bound for this particular density term. It is not a
bound for the full covariance or for the first pole of the preceding
Voronoi formula. The analytic input remains a research-preprint input,
not a new Lean import; see the [theta-twist audit](arithmetic-operator-theta-twist-frontier.md).

## Why the moving cutoff still matters

The exact finite divisor expansion is

```
A_n(S;u) = sum_(D|rad_E(n), ND<=C*S) mu(D) ND
             * sum_(J squarefree,(J,DE)=1) W_u(ND*NJ/S).
```

The complete density product requires all divisors of rad(n). For a
prime numerator larger than the cutoff, the actual sum contains only
D=1, while the missing D=(n) density contribution has size S. This is
why a fixed-n residue formula is not a uniformly saving approximation
when n moves. At the native lengths

```
S=Z^(7/6-d), Q=Z^(5/6-2d), Y=Z^(23/48-d),
K=S^2/Q=Z^(3/2), K/S=Z^(1/3+d),   0<=d<=1/6,
```

the problematic range is present. For a nonnegative fixed annular
profile the discrepancy is order S along prime numerators beyond the
cutoff. For the literal complex profile, no lower bound is inferred.
Its dependence `W_u(t)=t^(-11/6)W(t)Htilde(u/t^2)` stays exact.

Joining all divisors before norms gives the valid elementary allowance
`|A_n-density_n| << S*(Nn)^epsilon`. Pairing it with the full theta
energy costs

```
Q^(1/3)Y^(-1/3)S^(-5/6)K^(11/12)
  = Z^(25/48+d/2).
```

Compared with the old theta budget `Z^(3/16-d/2)`, the deficit is
`Z^(1/3+d)`. This is a scoped failure of density replacement and its
available discrepancy bound, not a lower bound for the final signed
sum. The next necessary input is a bound on the **actual theta-weighted
cutoff discrepancy**, keeping both variables and their moving profile.
The first Voronoi pole, marks, cube rows, fixed exclusions and source
transfer remain separate obligations.

## Divisibility does not split a phased prime-power observation

[ArithmeticOperatorQDetValuationPhaseAudit.lean](../scripts/ArithmeticOperatorQDetValuationPhaseAudit.lean)
keeps the same actual higher-q determinant. If its valuation at p is
`3a+c`, define `G_v(z)=sum_(r=1..v)z^r`. The checked identity is

```
G_(3a+c)(z) = (1+z^a+z^(2a))*G_a(z)+z^(3a)*G_c(z).
```

The quotient's depths start after the extracted cube. Replacing this
by `3G_a+G_c` would reset their physical phases and change the statistic.
At cutoff depth L the exact finite partition instead uses

```
sum_(j=0..2) z^(ja) G_(min(a,max(0,L-ja)))(z)
 + z^(3a) G_(min(c,max(0,L-3a)))(z).
```

The finite cutoff formula is verified in exact regressions; the
untruncated identity and the following actual example are Lean checked.
Direct kernel computation gives

```
D_3(2)=-1465731801504914208720,
Phi_3(2)=7, v_7(|D_3(2)|)=3,
v_7(|D_3(2)|/7^3)=0.
```

At `z=exp(2*pi*i/3)`, the full seven-fiber is zero while the extracted
depth-one fiber is nonzero. This is a literal real-height prime phase,
not an arbitrary prime-system model. It disproves a positive fiberwise
transfer from extracted divisibility. It does not claim that the whole
determinant packet vanishes, or that this height is a zeta-zero ordinate.

For the full integer-base packet through row N, the ordinary norm bound
`|D_n(b)|<5b^(8n^2)` gives total phased mass `O_b(N^3)` uniformly in the
physical cutoff and height. The complete-support envelope has
`log X=Theta_b(N^2)`, so this schedule has no nonzero X^beta response.
X is an envelope, not the largest actual prime-power factor. Smaller
polynomial physical windows remain open: the row-average estimate only
forces source-smallness when `X=N^kappa` and `kappa*beta>2`.

## Root-of-unity height reduction does not rescue the extracted channel

Evaluating the same determinant at a primitive M-th root lowers every
conjugate height to `11*2^(5n)`. But the extracted norm satisfies the
exact cyclotomic resultant formula. Including index one as an auxiliary
envelope, its cube product is

```
E_M=product_(1<=n<M)|Norm Phi_n(zeta_M)|^3
   =product_(p|M)p^(3 phi(M)/(p-1)).
```

The complete phased prime-power packet of E_M, divided by phi(M), is
at most `3 log(X)(1+log(X))`, uniformly even when M and y vary. It is
therefore `o(X^beta)` for every beta>0. No prime-power depth is reset in
this bound. The extracted guaranteed factors of actual once-counted
rows form a divisor of E_M and inherit the bound.

There is also a nonvanishing trap: the product of all actual rows
`D_2(zeta_M),...,D_(M-1)(zeta_M)` is zero for every M>=4. Thus this
auxiliary extracted norm is not a nonzero full determinant norm.
The quotient remains unestimated. The full proof, primary resultant
source and precise scope are in
[the root-of-unity audit](arithmetic-operator-root-unity-source.md).

These results preserve the useful lesson from the Siegel proof: the
same nonzero integer object must retain a source and have divisibility
exceeding its matched Archimedean cost. Extra factors, a different
physical cutoff, or a smaller conjugate height do not establish that
surplus on their own.

The two new strict leaves contain 52 local declarations and 39 theorem
declarations including generated helpers; each passed 15 namespace
linters and an all-local standard-axiom audit. General Euler/rate,
resultant and infinite source arguments above are paper-level. All
119 previous checkpoint pins matched before shared notes changed, and
33 additional agent pins were independently checked. Research stays
local; no root registration, broad CI, commit or push is part of this slice.
