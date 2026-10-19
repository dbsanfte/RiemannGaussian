# Sextic support and the small physical determinant window

2026-10-19. This follows the [joined dual and valuation audit](arithmetic-operator-joined-dual-valuation.md). One new isolated Lean leaf closes the small-window divisibility question. Two primary-source audits resolve applicability questions about the theta coefficients. None supplies a new independent signed estimate or changes the imported strict `Re(s)>7/8` endpoint. The [validation record](arithmetic-operator-theta-support-small-window-gates.json) separates formal results, exact finite regressions and paper-level arguments.

## The actual small-window product has exactly the Chebyshev support

For integer `b>=2`, let

```
C_N(b) = product_(2<=n<=N) Phi_n(b).
```

Every index occurs once. [ArithmeticOperatorQDetSmallWindowAudit.lean](../scripts/ArithmeticOperatorQDetSmallWindowAudit.lean) proves, for every prime p, positive r and `p^r<=N`,

```
p^r divides C_N(b)  iff  p does not divide b.
```

The factors are actual positive cyclotomic values, not prescribed prime weights. The proof includes 2 and omits index one exactly as the original construction does. It uses the divisor product for the geometric sum: when `p|b-1`, successive p-index blocks provide the required powers; otherwise Fermat–Euler and coprimality of `b-1` provide them. No primitive-prime distribution theorem is needed.

Consequently the literal once-counted prime-power packet, through every `X<=N`, is exactly

```
sum_(p^r<=X, p does not divide b) log(p) * (p^r)^(-iy).
```

This packet identity is a paper-level finite consequence of the checked support theorem. Cubing `C_N` does not triple the packet: all eligible depths below the cutoff are already present. Nor can product packets be replaced by a sum of row packets. For example, both `Phi_2(2)` and `Phi_6(2)` contribute a factor 3, but their product contains the depth-one prime power 3 only once at `X=6`.

For the original higher-q determinants, set `P_N(b)=product_(2<=n<=N)|D_n(b)|`. The previous paper proof gives `C_N(b)^3|P_N(b)` and nonzero determinants. In addition `D_n(0)=0`, so `b^(N-1)|P_N(b)`. Since `p^r<=N` implies `r<=N-1`, this restores every omitted base-prime depth. Thus, on paper,

```
lcm(1,...,N) divides P_N(b),
packet(P_N(b); X,y) = sum_(n<=X) Lambda(n)*n^(-iy),  X<=N.
```

The general determinant extraction and this full-product strengthening are not claimed as new Lean results. They use the previously documented determinant proof.

The hypothetical zero source survives along the growing family `N>=X`; no fixed finite product has a zeta pole. For the resulting cyclotomic packet its Dirichlet series is

```
-zeta'(s)/zeta(s) - sum_(p|b) log(p)/(p^s-1).
```

The finite base correction is holomorphic on `Re(s)>0`, so it cannot remove a nontrivial zero pole. At the matched height, the cumulative Mellin transform retains residue `-m/beta`. Removing smooth density cancels the pole at one while retaining this source. These analytic statements are paper-level, independent of numerical probes.

But the same exact support identity is a collapse obstruction: for any weights on the actual prime powers, the packet is the original weighted von Mangoldt sum. The integer product provides no additional signed relation in this window. Its available logarithmic heights, `O_b(N^2)` for `C_N` and `O_b(N^3)` for `P_N`, do not estimate that sum at zero-source scale.

**Decision:** freeze this once-counted product observation for `X<=N`. Do not extend the conclusion to individual row sums, unsaturated windows `X>N`, quotient correlations or the whole q-Pascal family. For instance `C_2(2)=3` misses 5 above its proved window. The [full paper audit](../.lake/arithmetic-operator-qdet-small-window-gate/preflight.md) includes the valuation classification, source proof and primary references.

## The needed physical theta coefficient is sextic

The imported `sourceResidualFourierCoefficient` and squarefree-times-cube support theorem describe a **cubic** theta residue. The physical residue in the candidate full-Gauss estimate is **sextic**, with normalization

```
t(n) = (Nn)^(1/12) * rho(n).
```

The classical sextic Hecke relations pair prime exponents 0 with 4 and 1 with 3, give a self-relation at exponent 2, and kill exponent 5 modulo 6. They do not determine prime coefficients. The simple cubic support formula cannot be substituted for this residue. The native API search found no existing imported bridge that makes that substitution valid.

This matters to the preceding large-prime discrepancy witness. Its arithmetic statement remains exact, but a nonzero value of the actual sextic coefficient on that prime sector has not been proved. Conversely, the known sextic support relations do not remove the eligible prime sector. Known fourth/sixth-power frequencies are not substitutes: their norm may exceed the spectral cutoff while their radical prime still divides a spectral ideal. The Ramanujan factor then remains `1-Np`, not 1.

The primary-source checks also prevent two tempting transfers:

* Friedberg–Ginzburg compute coefficients of a descent representation; identifying it with the requisite sextic theta representation is conjectural. Their torus entry `diag(p,p^-1)` corresponds to a **square** numerator in classical indexing, not a prime numerator.
* A sufficient bad-place period of 72 does not imply sixth-power invariance. In the actual Eisenstein ring, the primary unit `a=1+18*omega`, of norm 307, has `a^6=37 mod72`. A genuine character of order dividing six is invariant; that factorization must be established for the assembled native section. This is not a counterexample to that actual section.

See the [native support audit](../.lake/arithmetic-operator-native-theta-support-gate/preflight.md) for exact APIs and the finite quotient calculations, and [Bröker–Hoffstein](https://arxiv.org/abs/1312.0568) and [Friedberg–Ginzburg](https://doi.org/10.4171/JEMS/803) for the primary literature.

## The aligned prime/cube pair does not cancel exactly

There is a concrete Hecke pairing worth testing before a larger development. The two incidences

```
(I,n)=(J,kp), (pJ,kp^3)
```

have the same transformed-kernel argument `Nn*Q/(NI)^2`. In a fixed scalar section, with its puncture and normalization bridges supplied, the local relation is

```
rho(kp) = q^(1/6)*u_p(k)*rho(kp^3),  |u_p(k)|=1, q=Np.
```

Keeping the actual annular profile gives the joined factor

```
W(t) - v_p(k)*(q-1)/q^2 * W(qt),  |v_p(k)|=1.
```

The factor is `q^-2`, including the precise spectral weight and raw-residue normalization. The two profiles are on different annuli. Even granting a common profile, the remaining multiplier has modulus at least

```
1 - 1/q + 1/q^2 >= 43/49,  q>=7.
```

This rejects exact cancellation by this particular pair; it is not a lower bound for the complete signed covariance. The unit depends on the remaining numerator. Actual cusp vectors, the nonmultiplicative model correction, ray data and masks remain explicit obligations. A putative product of these local bounds has only logarithmic attenuation at polynomial prime range, but no complete native product identity is asserted.

The known theta-density residue cancels in the second transform. That does not cancel the first Voronoi pole and does not bound the moving-cutoff discrepancy. The [Hecke audit](../.lake/arithmetic-operator-theta-hecke-gate/preflight.md) gives the full formulas, conjugation and section qualifications, and primary-source page checks.

## What remains worth testing

The useful lesson from the [Siegel interpolation argument](siegel-interpolation-review.md) remains the same: the *same* nonzero arithmetic object must retain the zero source and have divisibility or signed control exceeding its matched Archimedean cost.

The product at `X<=N` passes the source test but adds no constraint. The proposed local Hecke pairing retains a factor rather than cancelling it. The next theta task therefore requires an actual fixed-section/cusp bridge and a joint estimate of the sextic residue against the moving Ramanujan cutoff, with the prescribed model, phases and all physical powers. Cubic support, fixed-n density, and scalar prime/cube pairing alone do not provide it. Other unsaturated determinant interactions remain open and require their own source test.

Validation: the new Lean leaf passes warnings-as-errors, 15 namespace linters and an all-local standard-axiom audit: 27 declarations, 24 theorem declarations including generated helpers. Independently rerun exact regressions passed 31,408 small-window checks, 105 native quotient checks (plus the full ray-unit enumeration), and 1,829 Hecke algebra checks. These finite checks do not certify the analytic statements. All 157 previous pins and 48 agent pins matched before shared notes changed. Local work only; no root registration, broad CI, commit or push. Goal active: eight Tier-1 families visited, none exhausted.
