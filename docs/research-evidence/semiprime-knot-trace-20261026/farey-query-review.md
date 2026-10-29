# Independent review: same-colour phase and weighted Gauss cover

26 October2026. Read `farey-query.md` against the authoritative scalar catalogue/swap and current native setup. No numerical tests or repository edits. **The new same-colour linear phase and the signed-window Gauss coverage construction are valid for every prepared semiprime.** They acquire soft-k rows at the old horizon scale; no fast branch predicate or query exponent gain follows. Two small formula/scope corrections and a signed-window qualification are recorded below.

## 1. Same-colour arithmetic: proof and minor sign correction

For j a unit modulo k choose any unit lift modulo H=k² and acquire j^-1 modH. In Lambda_j, aj²−bN is divisible by k. Therefore

    (aj+bN j^-1)²−4abN=(aj−bN j^-1)²

is divisible by H. The canonical lambda_j=−aj−bN j^-1 modH is an ACTUAL native root, including axis cases. If j'=j+kt, then j'^-1=j^-1−kt j^-2 modH and

    L_(j')−L_j=−kt j^-2(aj²−bN) modH.

The report omits the MINUS sign in its prose first-order change. Its divisibility conclusion is unaffected. All lifts of the same colour give the same canonical lambda_j.

At the true colour j=P modk, this permits using the lift P moduloH. Since N P^-1=Q modH, lambda_j=−aP−bQ modH. Thus its stationary I is an integer. The canonical carry law for v+w is exactly lambda_sum=lambda_v+lambda_w−Hh, h in{0,1}, and I_sum=I_v+I_w−h. The character X_v=beta^(E_v−H tau_v)=U_j^a V_j^b is linear in the lattice vector. Equation(7) expands exactly, without division. The transformed physical exponent I−tau has additive carry-free closure because tau_sum=tau_v+tau_w−h.

This closure is valid at the common prime P for the correct colour. The same-lambda swapped row supplies the Q-side witness at the same I, but need not itself lie in Lambda_j. Its character must not blindly be assigned the same j-linear formula. The report's actual coverage argument uses the original swapped exponent and is sound. Any proposed traversal must additionally check that its child stays in the admitted row band; lattice closure alone does not impose |ab|<k.

## 2. Weighted Gauss cover: uniform proof and exact constants

The displayed basis (1,theta),(0,k), theta=j² N^-1 modk, has determinant k and describes Lambda_j exactly. Theta is a unit, so the primitive horizontal and vertical axis vectors are precisely (+/-k,0),(0,+/-k). A shortest axis vector has those primitive lengths; an arbitrary nonprimitive axis multiple should not be chosen instead.

The weight map (a,b)->(ap0,bN/p0) has determinant N, so its transformed lattice covolume is kN. Exact two-dimensional shortest-vector/Gauss reduction gives

    ||v||_0² <=(2/sqrt3)kN,
    |ab|N<=||v||_0²/2,

hence |ab|<=k/sqrt3<k. Nonaxis integer coordinates therefore have |a|,|b|<k. No signed cancellation or positivity assumption is used here; the lattice is the actual signed product lattice. Rational weights are computationally harmless: clear the common p0 denominator and reduce the integer basis ((ap0²),(bN)), whose entries have O(logN) bits.

Choose a public dyadic p0 within factor2 of the unknown smaller P. Both actual weighted coordinates are at most twice their guessed counterparts; therefore

    |aP+bQ|<=sqrt2 ||v||_(P,Q)
                <=(4/3^(1/4))*sqrt(kN)<4sqrt(kN).

The derived bound on |I| is correct. A fully integer public implementation can use Dceil=ceil sqrt(kN) and M'=ceil(4Dceil/H)+2, matching the authoritative original horizon. This avoids any floating-point square root. Then M'<=4k^(3/2)+4 on N<=k^6, and 2M'<16H holds throughout k>16, not merely eventually. The original M has this same safe form, so its existing signed-window ledger already covers these representatives when that contract is retained.

There are phi(k)=O(k) colours and O(logN) public dyadic scales. Every reduction, inverse/lift and row power costs polylogN, giving soft-k total bits including swapped partners, labels and duplicate metadata. The construction does not enumerate H colours or all roots per row. One supplied root per selected vector suffices because the true colour proves it is the correct stationary root. This is a genuine uniform coverage acquisition theorem under the prepared setup.

## 3. Deletion, special rows and signed queries

The original and swapped true rows have the nonzero Fermat gaps (P−1)(bQ−a) and (Q−1)(aP−b). The inequalities P,Q>16H>k exclude their vanishing, including the axis cases. If a row is globally E=Ht in the searched signed window, its local hit and |I−t|<=2M'<ord(q) force I=t, contradicting that nonzero integer gap. Hence both members of the correct pair survive public whole-row deletion. This is valid independently of whether the two rows happen to coincide on a diagonal.

Previously unit-certified central, diagonal or lambda=0 rows can be removed: a correct collision there would contradict that certificate or already have factored N. If their old certificate used a smaller horizon, it must be renewed for M'. The existing full diagonal and four lambda=0-axis prepasses fit soft k at this horizon. These four rows are NOT all axis rows; arbitrary nonzero-lambda axes must remain unless separately queried/certified. The new cover correctly includes them when Gauss returns an axis.

The proved family covers the SIGNED interval. A deterministic Gauss sign choice does not ensure I<0. If the final interface requires only negative physical indices, include both opposite representatives with their canonical phases (constant-factor acquisition), then use the inherited center/endpoint and opposite-carry proof. The signed proof as written is complete; negative-only use must make this extra closure explicit rather than infer a favourable sign.

## 4. Earlier Farey triple and modular-alias scope

For the explicit determinant-one triple the 3-adic valuations of abN are2,2,0, with unit parts1mod3 under the chosen epsilon. At k>910 the phase counts are12,12,4, respectively, not four for every row. The current report explicitly avoids the incorrect four-lift claim, and root existence is all that argument needs.

Its determinant-one phase calculation proves H does NOT divide Delta=lambda_3−lambda_v−lambda_w. Since |Delta|<2H, beta^Delta−1 is a certified unit. But H not dividing Delta only excludes the LITERAL exponent shift Delta/H. It does not prove beta^Delta differs from q^n for every integer n modulo hidden local orders; after H-roughening q spans the same group as beta. The Section3/outcome phrase “cannot be an integer q-shift” should therefore say “does not supply a literal acquired short shift Delta/H.” This correction does not affect the repaired same-colour law, whose explicit carry h is genuinely acquired.

## Outcome

The new constructive content passes: same-colour phases are lift-independent, weighted Gauss vectors are admitted, one true colour/scale produces a surviving same-index two-prime pair, and all acquisition fits soft k. Its row count and signed horizon still give the old soft k^(5/4) complete evaluator. Equation(7) propagates known-parent collisions forward but supplies no reverse subtree selector. No all-semiprime branch-selection or whole-query gain is established.

Integration note: the lift sign, literal-versus-modular shift distinction, opposite/swap metadata, and exact integer horizon have been incorporated into the report; the corrections above describe the reviewed draft.
