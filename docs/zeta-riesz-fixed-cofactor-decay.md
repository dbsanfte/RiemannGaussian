# Fixed cofactor decay in the original Riesz band

[Explore the component bounds and exact remaining terms](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=fixed-cofactor-decay).

Lean now proves an independent decay estimate for an entire arithmetic class:
integers `n = p*a`, with `p` prime and `a` any fixed squarefree nonunit
composite. The theorem uses the original band, common moving logarithmic
cutoff, source normalization and full polynomial factorial filter. It has
no hypothetical-zero assumption. RH and the joint signed floor remain open.

| Module | Checked endpoints |
| --- | --- |
| [ZetaRieszFixedCofactor](../RiemannGaussian/ZetaRieszFixedCofactor.lean) | `norm_sum_filter_square_cutoff_le`, `tendsto_actual_clipped_prime_band`, `tendsto_actual_composite_cofactor_band`, `coefficient_prime_pair_above_cutoff` |
| [ZetaRieszPrimeClasses](../RiemannGaussian/ZetaRieszPrimeClasses.lean) | `actual_band_eq_two_prime_classes`, `one_large_prime_factorization`, `prime_divisor_small_product`, `tendsto_small_composite_cofactor_band` |
| [ZetaRieszFilteredCompletion](../RiemannGaussian/ZetaRieszFilteredCompletion.lean) | `actual_band_eq_filtered_completion`, `integrable_filtered_completion` |
| [ZetaPrimeNonlinearHalfplane](../RiemannGaussian/ZetaPrimeNonlinearHalfplane.lean) | `integral_norm_nonlinearFactor_le_halfplane_tail`, `exists_uniform_halfplane_nonlinear_tail_lt` |

## The arithmetic estimate

Retain the quantities in the [original carrier audit](zeta-riesz-signed-fourier-tail.md):

```text
0 < u < 1,
D_N = floor(u^(-N)/(N+1)),       L_N = log((D_N+2)^2),
R_L(n) = sum_(d|n) mu(d) * max(0,L-log d),
C_L(n) = -log(n)*R_L(n)/L        on squarefree nonprime n,
K_(P,N,y)(n) = n^(-3/2-i*y)
              * sum_j P_j*(log n)^(N+j)/(N+j)!.
```

The actual hypothetical-zero parameters have `u = 3/2-Re(rho)` and the
specific fixed polynomial `zetaRightHalfPoleJetFilter rho hrho`. The new
bound holds for every fixed polynomial `P` and every real height `y`.

For a fixed nonunit cofactor define the finite nonnegative cost

```text
B(a) = sum_(d|a) |mu(d)| * log d.
```

The complete signed divisor mass is zero. Subtracting the common value
`max(0,L)` before taking absolute values gives

```text
|R_L(a)| <= B(a),
R_L(p*a) = R_L(a) - R_(L-log p)(a),
|R_L(p*a)| <= 2*B(a)                      if p does not divide a.
```

This cancels the large prime's logarithmic cost before the norm is taken.
On the clipped range `n <= a*(D_N+2)^2`, the common length obeys
`L_N >= log 4 > 0` and `log n <= L_N+log a`. Consequently the actual
coefficient has the fixed bound

```text
|C_(L_N)(n)| <= C(a),
C(a) = 2*B(a)*(1+log(a)/log(4)).
```

Unit exponential tilt bounds every factorial shift simultaneously:

```text
|K_(P,N,y)(n)| <= n^(-1/2)*S(P),
S(P) = sum_j |P_j|.
```

The elementary bound `sum_(1<=n<=X) n^(-1/2) <= 2*sqrt(X)` now pays the
entire clipped class. More generally, for any finite support `T_N` below
`K*(D_N+2)^2` and any coefficient bounded there by `C >= 0`, Lean proves

```text
|u^(N+1) * sum_(n in T_N) f_N(n)*K_(P,N,y)(n)|
 <= 2*C*S(P)*sqrt(K) * [u/(N+1) + 2*u^(N+1)]
 -> 0.
```

This is an explicit bound after the original full factorial filter.
It requires a fixed coefficient bound and fixed enlargement `K`; it does
not bound the full unrestricted coefficient by such a constant.

## Why composite cofactors disappear and prime cofactors survive

For squarefree nonunit composite `a`, both complete divisor mass and
logarithmic moment vanish. Thus `R_L(a)=0` for `L>=log a`. If also
`log p>=L`, the translated profile has nonpositive cutoff and is zero.
Hence `C_L(p*a)=0` above that boundary. Since `L_N` tends to infinity,
the entire fixed composite-cofactor band eventually equals its clipped
part and has the preceding decay.

For prime `a`, the saturated profile equals `log a`. Lean instead proves
the exact surviving formula

```text
C_L(p*a) = -log(p*a)*log(a)/L,
                     log(a) <= L <= log(p), p != a.
```

The visible `1/L` is not by itself a bound on this growing, factorially
filtered prime sum. Its oscillation and its correlation with the other
arithmetic classes remain relevant.

## Component ledger

The threshold 16 comes from the proved nonlinear prime-factor estimates;
the six smaller primes are `{2,3,5,7,11,13}`, whose product is 30030.

| Original arithmetic component | What is proved | What is still unpaid |
| --- | --- | --- |
| All prime factors below 16 | Absent from the original band for `N>=60` | Nothing in this class |
| Exactly one prime factor at least 16, with composite small cofactor | Exact factorization `n=p*a`, `a>1` dividing 30030; the full insertion band for each fixed composite cofactor tends to zero | Nothing in this class: the complete finite deletion and reduced source are now proved in `ZetaRieszReducedCofactorSource` |
| Exactly one large prime, with prime small cofactor | The only small cofactors are the six listed primes; their coefficient above the cutoff is exactly the displayed semiprime formula | Their signed filtered tail and its correlations with the multiple-large-prime class |
| At least two prime factors at least 16 | Exact support and original signed coefficients retained | A joint source-scale estimate strong enough for the fixed cofinal floor |

The classification has a finite cofactor space, not a claim of a percentage
of RH proved. The source limit is still the original negative multiplicity.
The [growing-cofactor continuation](zeta-riesz-growing-cofactor-decay.md)
now assembles that finite deletion and proves a stronger unbounded-range
deletion with the source retained. The sufficient target remains a fixed real floor
strictly above minus one along a cofinal sequence of the combined carrier.

## Auxiliary analytic operations

These operations describe representations of the same arithmetic carrier;
they are not additional disjoint classes in the preceding table.

* The isolated multiplier `exp(E)-1` has a vanishing integrated square-log
  allowance, now uniform on each entire closed half-plane
  `Re(s)>=sigma>1/2`. The factor `exp(A)` multiplying it is unpaid.
* Every original factorial moment passes exactly through the completed
  response minus its signed off-band boundary. Both frequencies remain
  paired in one genuinely integrable quotient. This identity does not
  bound the completed response or the boundary separately.
* The default RH explorer continues to end at
  `ZetaRieszCriticalProfile.exists_original_band_critical_profile`.
  The new component bounds are supporting endpoints and do not replace
  the furthest checked bound on the entire carrier.

All statements use only the permitted standard Lean axioms. The generated
[proof audit](rh-proof-explorer/audit.json) and [family index](theorem-families/README.md)
link the ordinary-root declarations. No historical novelty claim, new
zero-free width, or improvement to the numerical certificate is made.
