# Finite stationary-phase contraction attempt — 2026-10-22

Scratch derivation for the ORIGINAL prepared scalar gamma, q=gamma^(m²). No frozen files changed; no new evaluator is claimed.

## Exact stationary lift identity and its surviving digit

Fix a unit tag j modulo m, its native a=a_j with aj²=N mod m, and an inverse J of j modulo m². For x_k=j+mk, an inverse modulo m² is J−mkJ². Consequently

 a x_k+N x_k^(-1) = aj+NJ+mk(a−NJ²) mod m².

Since a−NJ²=0 mod m, all m lifts have the same phase modulo m². This is the usual finite stationary cancellation input and does not require m prime. For an additive primitive m²-root, phases are literally identical on this stationary fibre; nonstationary fibres can cancel by geometric character orthogonality.

For gamma, keep the INTEGER representatives instead. Writing a−NJ²=m d, the unreduced linear inverse lift gives

 gamma^[a(j+mk)+N(J−mkJ²)] = gamma^(aj+NJ) q^(k d).

If the inverse is reduced to its canonical residue modulo m², its correction adds another integer multiple of m² and hence another q-power. Likewise the native E_j is congruent to N+a−aj−NJ modulo m², but its chosen centered carry is an actual q-power. Thus stationary phase supplies a common LOW DIGIT and an explicit, generally nonconsecutive q-shift fibre; it does not supply a common original scalar target. Its public d can have polynomial magnitude in m,N; replacing it by a residue without retaining the quotient changes the original query.

This is a source-specific arithmetic distinction, not a lower bound on possible compensated transforms. An effective construction would need to exploit these exact carries, not merely invoke stationary phase over roots of unity.

## A finite lift-product compensation that can actually be proved

Let H_L(X)=product_(0<=i<L)(X−q^i). For every integer k>=0,

 H_L(q^k X) product_(t=1)^k(X−q^(L−t))
   =q^(kL) H_L(X) product_(t=1)^k(X−q^(-t)).                 (1)

This is an identity of Laurent polynomials in q, obtained by matching labeled factors; no cross difference is divided. It is valid at zero divisors. For k>L, overlap cancels symbolically before specialization, so no invalid pointwise inverse is needed.

Even granting the especially favorable consecutive fibre k=0,...,m−1, multiplying (1) gives

 [product_(k=0)^(m−1) H_L(q^k X)]
 [product_(t=1)^(m−1)(X−q^(L−t))^(m−t)]
 =q^[L m(m−1)/2] H_L(X)^m
 [product_(t=1)^(m−1)(X−q^(-t))^(m−t)].                    (2)

It follows that a stationary-lift product is NOT eliminated by its finite endpoint compensation: the compensation retains precisely H_L(X)^m. At original scalar inputs, H_L(X)^m has exactly the desired local zero support, but acquiring it is still the collision query. Taking an m-th root of a value is unnecessary for zero detection and does not acquire that value.

This identity is a constructive finite correction, not an invocation of an invalid invertible cyclic primitive. It also records where apparent theta simplifications put the missing source. The weighted boundary factors have only m−1 distinct roots, but total multiplicity m(m−1)/2. A soft-m descriptor does not itself pay their evaluation on J~m unrelated targets. Some unweighted endpoint products are paid by shared polynomial/MPE trees; the weighted triangular product must be separately acquired or contracted. Most importantly, even a free boundary evaluation would leave H_L(X)^m on the right.

The less ambitious ratio H_L(q^m X)/H_L(X) has only O(m) boundary factors, with the same cleared form (1). It transports a supplied startup value but does not determine it. At a collision, division by H_L(X) would erase exactly the desired source; only the cleared identity is admissible.

## Regularization retains the unpaid source coefficient

A completely finite regularization is H_L(X(1+epsilon)) in R[epsilon], R=Z/N. Its constant coefficient is H_L(X); if a local hit is simple, the first nonzero coefficient gives the other-factor product times X. Same-side seed differences are units under the prepared q-order promise, so this local description is legal. However the coefficient that distinguishes the local hit is still the original product or its punctured companion. A stationary sum of regularized values is not automatically a zero detector: summands from other lifts need not vanish on the same local leaf and can cancel. A product over all regularized lifts retains OR support but again has the initial product in (2). No cheap coefficient acquisition follows just from writing the regularization.

A cyclic regularization is more problematic: the existing frozen audit proves full-orbit product zero on the old actual prime-order source and excludes an invertible cyclic primitive there. In the stronger general odd-order prepared source, one must also check membership in the q subgroup before quoting that particular cyclic argument. Neither argument rules out a new noncyclic regularized algorithm; neither supplies one.

## Paid/unpaid ledger and precise next bridge

Paid now: native j,a,b,E and their modulo-m² phases/carries; O(m) target powers; short q-powers; exact division-free identities (1),(2); shared unweighted endpoint products. The stationary congruence does not require any hidden P and is exact for every native row.

Unpaid: an exact whole-family contraction combining the row-dependent integer q-carry fibres with H_L startup values, in soft O(m) BIT cost, preserving at least one original bounded scalar leaf. No such contraction emerges from the finite identity above. A meaningful positive bridge would prove a carry-weighted product/transform identity whose remaining factor is both acquired and a UNIT on the retained family, rather than H_L(X)^m or an uncomputed weighted boundary product. An additive stationary-phase estimate, a formal Taylor error, a full m²-class completion, or a supplied Kloosterman scalar does not establish that bridge.

This pass therefore proves the exact finite compensation and identifies its surviving source power, but does not achieve near-linear collision acquisition or the sixth-rate factorizer. No claim of general impossibility follows.

Prior authoritative scope read: `docs/research-evidence/semiprime-input-dependent-20261015/reports/cyclic-reciprocity-audit.md` (finite carry/reversal identities, singular cyclic primitive), and `.../semiprime-spectral-source-20261016/reports/opposite-tag-reflection.md` (cleared finite theta endpoints). No new external theorem is used in this algebraic derivation.
