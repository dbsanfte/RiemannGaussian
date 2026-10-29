# Residue-preserving cancellations and a retuned hybrid target

26 October 2026. **No further acquisition-rate improvement is established in this pass.** The previous covered parity mask remains available. This packet executes collective and moving-root cancellations, obtains one jointly acquired symmetric-function operator action, and proves a conditional hybrid consumer at a different row/clock scale. The completed uniform query bound remains soft K^(5/4); the all-semiprime sixth-rate goal remains open.

These are independently reviewed paper arguments under the existing preparation contracts. They are not Lean theorems or a completed factoring implementation.

## A different scale for the missing evaluator

For sufficiently large K, keep the original preparation parameter K but build the complete parity family at K'=K/m, where m is the largest power of 3 with m³<=K/1024. If no such m exists, use the original-family fallback. The original stronger order, unit-gap and mixed-relation recovery contracts are retained. The new family has

    J=O(K^(2/3)), h=O(K²).

The old pure-conductor support argument still selects exactly one good collision. Its arithmetic part does not require N<=(K')^6; the numerical horizon and alias bounds are charged at the original K scale instead. Rooting the scaled rows is explicit division of their integer labels, not unknown-order root extraction.

Mark the selected rows by distinct integers 1,...,J. A supplied normalized residue or weak first-jet pair identifying the hit row can be validated with coordinate tests and O(J) gcd work. Then the existing geometric-product engine searches JUST that row in soft sqrt(h)=soft K and localizes an actual labelled leaf. This avoids using a smaller-conductor residue tag with an uncharged recovery cost.

Consequently an initialized selector costing

    soft(J^(3/2)+sqrt(h))

would meet the soft-K acquisition and recovery budget on this family. That selector has **not** been constructed. The distinction matters: its J^(3/2) term would be too expensive on the original J~K family. This is a concrete hybrid opportunity to investigate, not an achieved new bound.

| Covered family | Rows J | Clock h | Existing soft sqrt(Jh) term | Hypothetical separated term |
|---|---:|---:|---:|---:|
| Original parity family | K | K^(3/2) | K^(5/4) | K^(3/2) |
| Retuned unique family | K^(2/3) | K² | K^(4/3) | K |

The [coverage and consumer proof](content-cover.md), especially §§5–5.2, and its [independent review](review-content-cover.md) give the guards and distinguish the unique row-index interface from a more general product/localization interface. Merely retuning the family makes the existing evaluator worse; the paired change of evaluator is essential.

## A collective cancellation that retains a marked residue

With x_(j,i)=T_j*q^(-i), a=1+delta, the finite product

    K_delta(t)=product_(j,i) (a-t*x_(j,i))/(a-x_(j,i))

at t=q cancels across every row and leaves only two endpoints per row. Those endpoints are actually gated, so the boundary value kappa and its inverse cost soft K. Marking the numerator by t_i=q+epsilon*(-1)^(i-1) retains

    Res_delta partial_epsilon K_delta = -kappa*q^-1*(-1)^I

at the unique good collision. A row mark instead returns that row's tag. This realizes earlier paid-endpoint and marked-product machinery in one finite Cauchy specialization; it is not first credit for unit normalization.

The [collective calculation](collective-character.md) also acquires a whole-row Macdonald operator action S_X from short polynomial evaluations:

    S_X + [h]_q*D(q^h)/D(q^(h-1)) = [J+h]_q,
    [n]_q=(q^n-1)/(q-1).

All denominators are screened. The required marked derivative remains unpaid: differentiating the cancelled value follows a different direction, and its extra clock contribution cancels the desired residue. The finite operator's differentiated form likewise retains selected leave-one-out factors. The [review](review-collective-character.md) checks these identities directly, including a partial-fraction proof of the jointly acquired action. No infinite partition sum is evaluated at native units.

## Moving roots and the remaining finite boundary information

The [moving-root decomposition](deformed-telescoping.md) uses D_t(X)=t^J D(X/t). The signed logarithmic derivative of the even/odd product ratio has residue exactly (-1)^I. Its q-shift collapses to two degree-J endpoint polynomials, giving a residue recurrence a_(k+1)+a_k=e_k. The endpoints are acquired; their bounded orbit positions relative to the requested clock are not. The [review](review-deformed-telescoping.md) checks the finite endpoints, chain-rule factor, amended horizon and wrong-bin gates.

Two imposed-content coverage constructions were also executed. Their exact phase supports are smaller than their stationary colour domains; the resulting row savings do not improve the existing evaluator. The full-cylinder construction is exactly conductor retuning after explicit powering is removed. These scoped calculations motivate the hybrid above; they do not establish a general acquisition lower bound.

## Validation and next acquisition target

The [structural diagnostic](check_content_structure.py) passed 1,134 cylinder-criterion checks and 1,266 periodic-root checks, and its replay matches the [recorded output](content-structure-results.json) exactly. Those checks validate finite arithmetic identities, not coverage or a scaling rate. Uniform statements are paper proofs with independent reviews. Prior files and concurrent work were preserved; no commit or push was made.

The next concrete target is an initialized selected-residue or row-index algorithm with separated dependence on J and h, especially at J~K^(2/3), h~K². A full dense matrix or full resolvent is still unnecessary. The missing operation is acquisition of the marked response itself.

Prior contracts: [covered parity mask](../semiprime-clock-phase-20261026/README.md), [unique weighted cover](../semiprime-unique-weighted-20261026/README.md), and [earlier packed-residue contractions](../semiprime-packed-residue-20261026/README.md).
