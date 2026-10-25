# Nonlinear residual quartic characters: a paid whole palette

22 October 2026. No soft-O(J+sqrt L) collision aggregate or factor locator was obtained. The actual aggregate computed here is the complete unit gauge for a public nonlinear twist palette, with all its parameter values charged. The zero-mask aggregate remains uncomputed; it is not claimed that an equivalent character count solves acquisition.

## Input and the new nonlinear points

Read the paid Cayley companion report and its structured-twist companion. Retain their precise setup: N=P Q odd distinct primes; x_j, u and q all belong to the same prepared odd-order scalar subgroup G of (Z/NZ)*. The seeds are y_i=u q^i, 0<=i<L. Assume J,L and the palette size ν are polynomially bounded in N, as in the native J~m,L~m²,ν~m regime; hence every exponent descriptor below has O(log N) bits. In particular x_j/a and y_i/a have odd local orders whenever a belongs to G.

For every public a in G form Gaussian units

    α_a(t)=t+a*i,
    W_a(t)=α_a(t)/barα_a(t)=(t+a*i)/(t−a*i).

This is nonlinear in the original scalar point. Its denominators are universally safe on the full prepared family: if t²+a² vanished modulo either hidden prime, (t/a)²=−1 would force an element of order4 inside an odd-order group. Hence Norm α_a(t)=t²+a² is a unit. This uses no character guess or hidden sign selection.

The transformed W_a(t) is norm one but need not have odd order. Thus its lift character can be nontrivial even after the *original scalar* odd-order preparation. That is the specific way the nonlinear argument retains a phase which a homomorphic colour of G itself cannot retain.

## Exact residual phase and zero ledger

Let S_N denote the actual Gaussian quartic Jacobi symbol with rational denominator N, let τ(W_a(t))=S_N(α_a(t)), and set j2=Jacobi(2,N). Explicitly extend S_N(h)=0 whenever Norm(h) is a nonunit modulo the squarefree N, retaining the multiplicative quartic convention on Gaussian units. Direct subtraction gives

    W_a(x)−W_a(y)
       =−2a*i*(x−y)/[(x−a*i)(y−a*i)].               (1)

Every denominator is a checked/promised unit. A rational unit has Gaussian quartic symbol1, S_N(i)=j2, and conjugation inverts S_N. Therefore, including zero values,

    S_N(W_a(x)−W_a(y))
       =j2*S_N(α_a(x))*S_N(α_a(y))
             *1_(gcd(x−y,N)=1).                    (2)

This is a nonprincipal quartic residual character with an exact row/column gauge. Local Gaussian split/inert conventions are those proved in cross-twist-symbols.md. Nonunit differences in (1) have exactly the original local collision mask; no new zeros from the denominator are introduced. The original exponent ledger therefore still discharges every localized leaf.

For the full phase on arbitrary Gaussian norm-one chords, take unit lifts w=α/barα and z=β/barβ. The numerator of w−z is

    η=α*barβ−β*barα,

which is conjugation-anti-fixed and therefore η=r*i for a rational residue r. On a unit chord, η is a unit, hence r is a rational unit. Its quartic symbol is exactly S_N(η)=S_N(i)=j2. Dividing by barα*barβ consequently gives the full identity S_N(w−z)=j2*τ(w)*τ(z), not merely its square. The shorter bar(w−z) identity alone must not be used to guess a quartic root. If w,z themselves have odd order, τ(w)=τ(z)=1 and the residual character is simply j2 times the unit mask. Removing oscillation here does not compute the mask sum.

## A whole public palette, acquired in the target budget

Choose a_k=u q^k for 0<=k<ν, with ν=O~(J+sqrt L), e.g. ν~m when J~m,L~m². Define actual Gaussian unit products

    A_k=product_j(x_j+a_k*i),
    B_k=product_(0<=h<L)(y_h+a_k*i).

All A_k can be acquired together by forming the degree-J polynomial A(Y)=product_j(x_j+iY) and monic multipoint evaluation at the ν public scalar points a_k. This costs soft O(J+ν) Gaussian-ring operations. The coefficient ring is Z/N[i] of fixed rank2; no unknown field or point-difference inverse is used.

For B_0, compute product_(0<=h<L)(q^h+i) and multiply by u^L. A scalar degree-one q-factorial is evaluated in soft O(sqrt L) Gaussian-ring operations: choose b~sqrt L, form the length-b block polynomial, evaluate it at the L/b geometric block starts with monic product/remainder trees, and multiply the blocks plus exact tail.

For all later k, use the literal unit-safe boundary recurrence

    B_(k+1)=q^L*B_k*(q^(−k−1)+i)/(q^(L−1−k)+i).     (3)

The two Gaussian factors have unit norms because q has odd local order. Their powers are updated geometrically. Each division is implemented using conjugation and a checked norm inverse. Thus all ν seed products cost soft O(sqrt L+ν), not ν*sqrt L or L.

Consequently the *entire* Gaussian unit companions

    C_k = (−2a_k*i)^(JL)/(barA_k^L*barB_k^J)         (4)

are acquired in soft O(J+sqrt L+ν) bit work, with logarithmic modular arithmetic factors. They satisfy the unconditional product identity

    product_(j,i)[W_(a_k)(x_j)−W_(a_k)(y_i)]
       =C_k*product_(j,i)(x_j−y_i),                 (5)

even when the rightmost product is a nonunit. No division by that product occurs.

The full character gauge for each k is also acquired at that cost:

    j2^(JL)*S_N(A_k)^L*S_N(B_k)^J.                  (6)

Computing the O(ν) quartic symbols uses conservative O((log N)^3) per symbol, hence only logarithmic overhead. Each actual parameter, product and descriptor has O(log N) bits. The polynomial parameter bounds ensure log L, log J, log ν and log(JL)=O(log N), so all modular exponentiation and quartic-symbol costs are included in the stated logarithmic overhead. This is a public, full-input nonlinear palette acquisition and aggregate calculation for its gauges; it is not a supplied-palette assumption.

## What this calculation does and does not evaluate

Equation(2) diagonal-gauges every palette member to the SAME unit/nonunit matrix. Equations(4)--(6) acquire all its gauge products, but do not acquire its masked row sums, sum of all normalized characters, or a useful original product. In particular, a promised original collision makes the product of all character entries zero for every k; knowing that zero does not locate a proper gcd or a saturated nonzero leaf. The finite searches cannot be skipped during localization merely because the root-level promise is known.

The nonlinear phase information is real: W_a(t) may have even order and τ(W_a(t)) is not forced to1. In this common-twist palette, however, it enters exactly as the explicit diagonal gauges above. I found no additional additive reciprocity or finite Jacobi-sum identity computing the remaining incomplete geometric-window aggregate at soft O(J+sqrt L).

A complete-field identity cannot be used as an algorithm on this input by supplying the hidden field, its complete period or an incomplete-window selector for free. The inspected primary complete Jacobi-sum algorithms accept those fields/characters as data; they do not give an N-only evaluator for this normalized residual matrix. This is a scoped applicability statement, not an impossibility theorem for other nonlinear twists.

## Validation and inherited sources

check_palette.py verifies405 Gaussian residual phase/zero-ledger cases and12 literal seed-product updates on three odd-subgroup composite-ring inputs. These test algebraic signs and division safety, not success rates or the asymptotic factoring claim.

The Gaussian symbol conventions and implemented descent are pinned in:

- /tmp/semiprime-character-acquisition-20261022/algebraic_symbols/cross-twist-symbols.md
- /tmp/semiprime-character-acquisition-20261022/algebraic_symbols/corrected-cross-order-root.md

Primary Gaussian reciprocity: Bach--Sandlund, arXiv:1807.07719v1, Section7; https://arxiv.org/html/1807.07719v1 . PDF SHA256 2f8942dde3c54580a39e442e51781d688dee1169d7e0722bd7077e5768d3c3cb.

The scalar block q-factorial construction is the degree-one case of Bostan--Yurkevich, arXiv:2012.08656v1, with direct monic-ring implementation as described above; https://arxiv.org/html/2012.08656v1 . Its degree-J theorem is not invoked with J silently treated as constant. PDF SHA256 f3d617af2e9c899b41d5f4d9120412c78857ebc19009b69fe99e74d97f0d9b09.

The already read paid scalar Cayley report is /tmp/semiprime-character-acquisition-20261022/character_counts/cayley-paid-companion.md. The recent complete-sum source audit is in that directory's report.md; it does not supply the missing native incomplete query.

Only /tmp/semiprime-cayley-acquisition-20261022/residual_characters/ was written this round. No repository edits, builds, commits, or subagents.
