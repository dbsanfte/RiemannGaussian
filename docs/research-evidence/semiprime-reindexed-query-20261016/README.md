# Row starts and denominator redesigns: exact arithmetic constraints on acquisition

2026-10-16. **New arithmetic results constrain two concrete acquisition shortcuts.** Arbitrary long-scale row reindexing preserves a nearly quadratic carrier tradeoff. Choosing denominators so every leading coefficient equals one retains guaranteed collisions but produces an exact global Sidon target set. A denominator-m redesign really produces one geometric carrier, whose aggregate instead becomes a cubic-length stream. Centered carries can be removed cheaply on an explicit unit branch.

Three authorized Sol 6.1 agents investigated in parallel. The redesigned-family proofs have two independent final-byte reviews; the other reports have targeted independent reviews. These are classical results. The whole-family softly O(m) collision query remains open, and the general softly O(m^(3/2)) acquisition bound is unchanged. No new Lean declaration, build or factoring-exponent claim is made.

## Reindexing every row does not remove the arithmetic obstruction

The [raw-energy theorem](reports/raw-energy-rowwise-carriers.md) strengthens the [previous high-digit result](../semiprime-high-digit-query-20261016/README.md). Raw modular energy counts ALL tag quadruples satisfying equal offset sums modulo m^2, including multiplicities. For fixed nonzero low digit n, the exact source lift still gives

    sum_h Eraw(n,h) <= 4m^3.

On all but at most 4m^2/lambda coprime input residues, Eraw<=lambda*m^2. Thus EVERY integer rowwise lift epsilon_j=delta_j-m^2*s_j has energy at most lambda*m^2, simultaneously over all input-dependent or privately advised integer starts. Deduplication still leaves more than m/2 offsets. Any arithmetic-progression cover of their integer set obeys

    k^2 T > m^2/(32lambda).

The same bound holds for geometric covers in the global unit group when twice the lifted span is smaller than the global element order. The actual qualified supply has D>cM^4.062; this covers every prescribed start RANGE at most m^2 polylog(M), even with a huge common translation. This long-scale transfer is global, not automatically fieldwise. Unbounded relative advice can collapse all geometric targets to one point; the report gives that counterexample rather than dropping the span condition.

The varying-menu selector count bounds the new bad prime pairs by O(K_*M^6/lambda) against the SAME original qualified supply. Taking lambda=K_*log^4 M preserves a majority-size family. For polylogarithmic candidate menus, the cover bound is therefore k^2T=soft Omega(m^2), uniformly over all allowed reindexings. This sharpens the tradeoff for schedules compatible with the desired query clock. Polynomial menus retain their explicit lambda charge.

## A constant-leading redesign gives an exact Sidon obstruction

The [constant-leading family](reports/constant-leading-sidon.md) chooses

    t_j=(N^(-1)j^2 mod m),  a_j=1,
    delta_j=1+mb_j-2j,  E_j=N*t_j+delta_j.

It uses public data and softly O(m) setup. Its own-factor index is an integer in the canonical length 2m^2+2, with

    E_j-m^2*i_P=(P-1)(t_j*Q-1)  at j=P mod m.

Thus this redesigned family has actual collision coverage, not just geometric conjectures. Nevertheless its GLOBAL targets are an exact multiplicative Sidon set: equal pair products occur only for the same unordered pair of tags.

The key is the global reduction N=P+Q-1 modulo the order of gamma. The effective phase is t_j*(P+Q-1)+delta_j. The inherited global order makes pair-sum congruences exact integer equalities. Since P+Q-1 dominates the delta span, equal phase sums force equal denominator sums, then equal tag sums and tag-square sums modulo m. Odd characteristic forces identical unordered pairs. The m-1 targets are distinct and their energy is EXACTLY 2(m-1)^2-(m-1), with no new deletion or high-digit averaging.

Consequently every advised geometric cover satisfies k^2T>=(m-1)^2/4; any containing carrier has a quadratic productset. This also excludes nearlinear progression boxes of fixed or o(log m) rank. The theorem is global only; passing to a hidden-field quotient can destroy the Sidon property. It bounds carrier representations, not operations, scalar norm algorithms, shared computation or factor-selective queries.

## One progression can still leave a long scalar query

The [denominator-m redesign](reports/denominator-m-redesign.md) uses t=m, a=0 and b_j=centered(-N/j mod m). The b_j permute all nonzero centered residues. It has one geometric target carrier with one missing point and a guaranteed own-factor index (Q+b_j)/m in the same canonical long window. This uses the general row constructor, beyond the existing list's t<m range.

Adding the missing b=0 point gives an enlarged query with the exact tiling

    product_b product_(i<L)(1-g^(-N-b+mi))
       = P_(mL)(g^(-N-(m-1)/2);g),  g=gamma^m.

The stream length is Theta(m^3). The established division-free evaluator costs softly O(m^(3/2)); a geometric carrier alone has not paid the desired query. Added or saturated global-zero leaves recover P+Q on the stated large-order branch. Neither removing the extra class by an invalid division nor assuming long Gaussian denominators are units is used. A faster evaluator remains possible; no operation lower bound is inferred.

## Paid normalization isolates the remaining scalar target

The [normalization algorithm](reports/constant-carry-normalization.md) writes delta_j=r_j+m^2*kappa_j with 0<=r_j<m^2 and -3<=kappa_j<=1. Exact finite-product identities remove kappa_j with at most six endpoint factors per tag and softly O(m) work. On the full canonical majority branch, the existing endpoint-unit theorem licenses the unit normalizers. For restricted intervals the reduction is conditional on their own endpoint-unit branch or separately paid saturation handling; canonical endpoint units do not grant arbitrary interior units.

The remaining target is a norm on the ACTUAL two-digit residue graph r_j, not merely its low quadratic digit. Acquiring that norm, the quotient forcing, a channel remainder, a collision locator or another restriction-stable sufficient factor query in softly O(m) is still required. Complete bit-complexity and Lean composition remain after that. All twelve predecessor packets and exact journal entries are unchanged.
