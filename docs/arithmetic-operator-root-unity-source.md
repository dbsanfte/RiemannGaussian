# Root-of-unity height reduction: the extracted norm loses the power source

2026-10-19. Paper-level proof and exact finite regressions, not a Lean
resultant theorem. This is a scoped test of the same higher-q determinant;
it does not close the q-determinant family or estimate its quotient.

## 1. The same integral determinant, at smaller Archimedean height

Retain exactly

```
D_n(q) = [5n choose n]_q [4 choose 2]_(q^(n*n))
         - [4n choose 2n]_q [5 choose 1]_(q^(n*n)), n>=2.
```

The preceding higher-q audit proves `Phi_n(q)^3 | D_n(q)` over the
integers (order four at n=2, order three at all n>2). Let M>n and let
zeta_M be primitive. Because Gaussian binomial coefficients have
nonnegative integral coefficients, every conjugate satisfies

```
|D_n(zeta_M^a)| <= 6 binom(5n,n)+5 binom(4n,2n)
                <= 11*2^(5n),               (a,M)=1.
```

This genuinely lowers the available per-embedding logarithmic height
from O(n^2) at integer base b>=2 to O(n). It does not by itself establish
a useful lower bound from divisibility, nor nonvanishing.

Nonvanishing must be retained separately: M>n DOES NOT imply
`D_n(zeta_M) != 0`. Exact regressions find, for example, D_2 vanishing at
M=5,6,10 and D_3 at M=4,5,6,7,12,15. Whenever the value is nonzero, its
ordinary integer norm is divisible by
`|Norm Phi_n(zeta_M)|^3`; a zero value cannot be used as a nonzero integer
in a height/divisibility contradiction. No regularization is supplied.

In fact the product of ALL actual rows 2<=n<M is zero for every M>=4.
For M>=5 take n=M-1. The cyclotomic orders in the two large Gaussian
binomials are respectively `4-0-3=1` and `3-1-1=1`, by the factorial
floor formula for their Phi_M valuations. Both terms of D_(M-1) vanish.
For M=4 the second large binomial and the first term's
`[4 choose 2]_(q^9)` vanish at zeta_4. This is an additional exact
nonvanishing obstruction, not a numerical inference.

## 2. Exact extracted norm and its prime-power valuations

Write phi for Euler's totient. The cyclotomic resultant formula gives,
for 1<=n<M,

```
|Norm_(Q(zeta_M)/Q) Phi_n(zeta_M)|
  = p^(phi(n)), if M/n=p^a for a prime p and a>=1;
  = 1, otherwise.
```

For n>1 this is Theorem 9 and equation (9) of Bzdega,
Herrera-Poyatos and Moree, *Cyclotomic polynomials at roots of unity*,
[arXiv:1611.06783v2](https://arxiv.org/abs/1611.06783v2),
Acta Arith. 184 (2018), 215--230. Their proof is included in the pinned
local PDF. For n=1, use `Phi_M(1)=p` for prime powers M and 1 otherwise;
the absolute norm makes the sign immaterial.

Introduce an auxiliary extraction ENVELOPE

```
E_M = product_(1<=n<M) |Norm Phi_n(zeta_M)|^3.
```

The actual determinant rows begin at n=2: D_1 is identically zero.
Including n=1 therefore enlarges the extracted divisor; it is not
presented as an additional actual determinant row. Any subset of the
actual once-counted rows n=2,...,M-1 has its guaranteed extracted norm
dividing E_M. The fourth copy at n=2 may remain in the quotient.

If p^v exactly divides M, write M=p^v A with p not dividing A. Then

```
sum_(a=1..v) phi(M/p^a)
  = phi(A) sum_(b=0..v-1) phi(p^b)
  = phi(A)*p^(v-1)
  = phi(M)/(p-1).
```

The first equality is coprime multiplicativity, the second includes
`phi(1)=1` and telescopes the prime-power totients. Consequently

```
E_M = product_(p|M) p^(3 phi(M)/(p-1)).
```

For the full actual extraction n=2,...,M-1, remove the Phi_1 factor:
divide E_M by p^3 when M is a prime power p^v, and leave it unchanged
otherwise. All resulting exponents are nonnegative. No physical prime
index is identified with the row index n or with M.

## 3. Full phased prime powers, with no exponent reset

For X>=2 and real y define the literal finite prime-power observation

```
T_M(X,y) = sum_(p prime, r>=1, p^r<=X, p^r|E_M)
             log(p) * exp(-i*y*log(p^r)).
```

Every depth r occurs once, with its own phase. Using the exact valuation
above and only the unit modulus of that phase,

```
|T_M(X,y)|/phi(M)
 <= sum_(p|M,p<=X) log(p)*min(v_p(E_M),floor(log(X)/log(p)))/phi(M)
 <= 3 sum_(p<=X) log(p)/(p-1)
 <= 3 log(X) sum_(h=1..floor(X)-1) 1/h
 <= 3 log(X)*(1+log(X)).
```

The same inequality holds for every integer divisor of E_M, so also
for every guaranteed extracted divisor from any once-counted subset of
nonzero actual determinant rows. It is uniform in M and y. In particular,
for any beta>0 and any schedules M(X)>=2 and y(X),

```
X^(-beta) T_(M(X))(X,y(X))/phi(M(X)) -> 0.
```

This is an actual upper bound for the extracted observation, not a
claim that its continuous-density model has the same response. It
shows that this degree-normalized extracted channel cannot supply a
nonzero source of size X^beta. The estimate includes physical prime
powers beyond the row scale whenever they are <=X; it never resets
their depth to one. No PNT, RH, or prime-factor equidistribution is used.

The field-degree normalization is the same one needed when comparing
the total norm with the per-embedding Archimedean height. Multiplying
both sides by phi(M) does not create a surplus. A different growing
row multiplicity or source renormalization requires a new matched
height/source audit; it is not excluded by this calculation.

## 4. Scope and next obligation

The available height upper bound for a product of rows n<=N is
`phi(M) * O(N^2)`. This is an upper bound, not a lower bound or a proof
of the optimal height. The extracted cube valuation alone does not
outgrow it, and the corresponding normalized prime-power observation
has just been shown source-small.

The quotient `D_n/Phi_n^3` is still an actual integral polynomial. Its
norm and every extra valuation remain outside the estimate in section3.
They must not be erased or given the extracted factor's bound. Therefore
the result freezes the proposed **root-of-unity extracted-factor
shortcut**, not all root-of-unity determinant arguments, not the
integer-base polynomial physical windows, and not the full interpolation
strategy in the Siegel paper.

This gate also explains why ordinary log-norm control cannot be promoted
to an additive split of phased fibers. For a product with valuation
`v=3a+c`, the correct phase ledger is
`G_v(z)=(1+z^a+z^(2a))*G_a(z)+z^(3a)*G_c(z)`,
not `3G_a+G_c`. The separate native qdet audit checks that identity.

## 5. Validation

The files `probe.py` and `probe.json` in
`.lake/arithmetic-operator-root-unity-determinant-gate/` contain 3,891 exact checks: 780 actual
cyclotomic resultants, 2,126 prime-power totient towers, 39 all-proper
extraction products, 917 cutoff valuation comparisons, and 29 nonzero
actual determinant norm divisibilities. Thirteen zero norms are recorded
and excluded from the nonzero tests. These finite regressions do not
prove the general theorem; sections1--3 give its paper derivation.

An independent agent checked the resultant formula, the n=1 envelope
correction, growing-M uniformity, every prime-power phase, and the
nonvanishing caveat. No Lean leaf, root import, public theorem explorer,
broad build, CI run or source-preserving RH estimate is claimed here.
