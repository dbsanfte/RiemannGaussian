# Actual all-square amplitude and physical integral bound

2026-10-19. Local research checkpoint following the
[residue/cubic gates](arithmetic-operator-residue-cubic-gates.md).
The old conditional Gauss bridge is now discharged. This checkpoint proves
an unconditional bound on the **original square-numerator amplitude and
its Mellin integral**, with every physical modulus retained. It does not
bound the complementary odd-core population or prove a new zero-free region.

## Checked arithmetic endpoint

Let `L_sigma(m) = lowRayAmplitude (calibrationForSet S) W Y sigma m v`.
The original profile is compactly supported in `[a,z]`, with `a>0` and
`norm(W)<=B`. For independent scales `A,Z>=1`, `Y>0`, `z*Y<=Z`, and any
actual Eisenstein unit `zeta`, Lean proves, for every `eps,eta>0`,

```text
sum_(x != 0, Nx <= A) |L_sigma(zeta*x^2)|^2
  <= K_eps,eta * (B*a^(-1/2))^2 * A^eta * (A*Z)^eps * (Z/Y)^2
       * [A^(1/3) + A^(4/3)/Z].
```

The constant is uniform in the canonical calibration set, ray and real
Mellin height. Roots need not be squarefree, supported or coprime to the
modulus. Physical columns retain the original calibration, profiles,
exclusions and phases. With fixed profile and `Z=max(1,z)*Y`, this has the
usual small-power shape `(AY)^eps[A^(1/3)+A^(4/3)/Y]` for `Y>=1`.

The terminal theorem is
[`lowRayAmplitude_all_square_energy`](../scripts/QuasiRHAllSquareAmplitudeBridgeAudit.lean).
It has **no** assumed Gauss identity, free phase, baseline norm or energy
bound. It applies the imported actual cubic large sieve after proving the
literal finite Gauss decomposition.

## Why the finite arithmetic works

Every nonzero square column has the canonical factorization

```text
c = H^6*b*d^3*e^5,       T = H^3*d*e^2,       x = T*u,
G(c,-zeta*T^2*u^2)
  = G(c,-zeta*T^2) * conjugate(cubicRow(b,u))
                      * cubicRow(e,u) * 1_coprime(u,d).
```

Here `b,d,e` are squarefree and disjoint; `H` may overlap all three. There
is **no** coprimality condition between `u` and the principal-only primes
of `H`. Their sixth-power Gauss terms remain constant for nonunit `u`.
CRT is used across distinct primes, never across overlapping factors.

The actual normalized baseline satisfies `norm(G_C(-zeta*T^2))<=NT`
for **every** ideal divisor `T|C`, not only canonical blocks. For the
transport identity, however, canonical partitioning is essential.
The final proof groups actual columns by `T`, proves `b6` injective on
each fiber and pushes those exact coefficients into the cubic column
range. Only then is the coefficient extended by zero. It never applies
the canonical ratio to a noncanonical enlarged column.

The surviving row factor has norm at most one. The actual divisor count
pays the number of active `T|x`; the remaining ideal sums have exponents
`-7/3` and `-4/3`, both summable. This is genuine arithmetic input from
the actual cubic matrix, not a norm axiom for arbitrary pair masks.

## The original physical integral

[`QuasiRHSquareSectorTransfer`](../scripts/QuasiRHSquareSectorTransfer.lean)
proves the exact square/complement split and the six-unit energy cover.
[`QuasiRHSquareSectorIntegral`](../scripts/QuasiRHSquareSectorIntegral.lean)
then proves that both sectors are genuinely integrable, retains their
exact integral sum, and applies the unconditional amplitude bound.

For `A=sqrt(2*bCut*Q)`, the result is the square root of the displayed
energy bound, times a fixed Mellin-profile constant and the original
`lowInverseMass`. That companion still contains its selected prime marks,
cube powers, phases and overlap masks. It is **unnormalized** here:
the original `Q^(-1/2)/(2*pi)` factor and the native companion estimate
are kept separate.

The reviewed **paper application** to the native central Gaussian dyads
gives the two costs

```text
q_C^(1/12) * Zsource^(5/72)  * L^(-1/6),
q_C^(1/3)  * Zsource^(11/288)* L^(-1/6),
```

before the explicit arbitrarily small energy/companion/Gaussian losses.
The first dominates eventually because `q_C` is fixed and their exponent
gap is `1/32`. The required unselected tuple mass is the already-checked
`theta=-1/6` specialization, giving exponent `-5/3`; the old `theta=-1/2`
bound is not silently reused. The full central Gaussian/source wrapper
is not newly claimed as compiled by this checkpoint.

The original remote Gaussian bound is for the whole family, so it must
remain joined. The legitimate global ledger is

```text
Probe - F_all
  = centralSquare + (centralOdd - F_all) + remoteAll.
```

The source belongs to this whole expression. No source is allocated to
the square subset. The imported strict `Re(s)>7/8` result and the previous
full-central `1/250000` saving are unchanged.

## Next obstruction: the joined odd core

The untreated numerators have a nontrivial squarefree odd core:
`(m)=r*x^2`, with `r` allowed to overlap `x`. At a prime of `r`, the
principal sixth-power Gauss term now has a negative boundary. For norm7,
physical modulus `p^6`, the normalized values at numerators `-p^5` and
`-p^7` are respectively `-49` and `294`. The square-sector constant rule
cannot be reused there.

A new **paper-only** fixed-core audit retains this boundary/interior
split. It recovers a cubic bound for fixed `r`, but summing cores of norm
`R` separately costs

```text
Q^(1/12)*R^(5/12) + Q^(1/3)*R^(1/6)*Y^(-1/2).
```

At `R` comparable to `Q`, this costs `sqrt(Q)` and supplies no useful
whole-population payment. The varying core contributes an actual sextic
phase coupled to the cubic square-part phase; it cannot be absorbed into
one common cubic column vector. The next estimate must retain that joint
arithmetic and the original companion. This rejects only the separate
fixed-core summation route, not all odd-core mechanisms.

## Evidence and scope

Eight strict isolated leaves: 178 explicit theorem declarations,
438 module-local declarations and 364 theorem declarations including
generated helpers. Every leaf passed all 15 namespace linters, file and
CLI warning-as-error checks, and an all-local module-provenance audit
allowing only `propext`, `Classical.choice`, and `Quot.sound`.
Independent read-only reviews passed for the unconditional amplitude and
integral endpoints. The canonical-factorization, budget and odd-core
probes add 62,394 exact checks; they are regressions, not substitutes for
the Lean proofs.

The companion JSON records hashes, producer exits, bootstrap provenance
and the paper/compiled distinction. Historical manifests are preserved;
shared-note changes have explicit before/after hashes. No wider build,
root registration, publication, commit or push is part of this slice.
The roadmap remains active: eight Tier-1 families visited, none exhausted.
