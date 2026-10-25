# Native multiplier closure: exact tag maps and carried point identity

22 October 2026. Focused symbolic investigation; no implementation, selected examples, repository edits or new evaluator claim. Write M=m^3, Q=gamma^M, e_j=N+a_j+v_j and y_j=gamma^e_j. Retain all integer carries. The auxiliary prime m is odd and coprime to N; v_j^2=4a_jN modulo M and v_j=-2a_jj modulo m.

## Exact reuse criterion for the dyadic query states

After h steps of the direct multiplier-two recurrence, the base is q^(2^h) and the targets originating from j are

    gamma^(e_j-Mt), 0<=t<2^h.

For LITERAL INTEGER-EXPONENT identification with an actual canonical target k for that powered source, up to an integral power of its common stride Q^(2^h), necessarily

    e_j=2^h e_k+M(t+2^h u)                    (1)

for an integer u. Its exact public test is e_j=2^h e_k modulo M together with the required carry class modulo 2^h. No equality modulo m alone licenses reuse.

Modulo m the native exponent is e_j=N(j^-1-1)^2. Hence (1) requires

    (j^-1-1)^2=2^h(k^-1-1)^2 modulo m.        (2)

If 2^h is nonsquare modulo m, the only possible pair is j=k=1. If 2^h is square and c²=2^h modulo m, the only candidate tags obey

    k^-1=1 +/- c^-1(j^-1-1).

Candidates with inverse zero are absent from the actual tag set. These are genuine public Mobius maps; there are at most two candidates per tag. They generalize the previously known inverse-reflection fiber, but supply only a low-digit necessary condition. Full (1) is checked by the actual cubic carries. In particular literal dyadic native-target closure at odd depths cannot hold when Legendre(2,m)=-1, apart from the fixed tag. This is a statement about canonical-tag reuse, not arbitrary compressed query representations or operation lower bounds.

A common multiplicative rescaling of all targets changes the low-digit condition by one fixed additive exponent. It must be retained explicitly. It does not follow from (2) that every resulting conic has supplied canonical tags and full-M carries. No general rescaled closure is proved here.

## A different exact native map when multiplier reduction has no carry

There IS a concrete conic-root map with bounded integer carry. Let c be a fixed positive integer coprime to m, choose a tag j for which c² a_j<m, and put k=j/c modulo m. Then

    a_k=c² a_j EXACTLY as integers,
    v_k=c v_j+M s

for an explicitly acquired integer s=O_c(1). The root congruence holds since c²v_j²=4c²a_jN modulo M, and the chosen sign is correct because v_k=-2a_k k=c v_j modulo m. Hensel uniqueness for a simple root then proves equality modulo M; the native O(M) representative bounds give the stated carry bound.

Therefore the actual scalar points satisfy

    y_k=gamma^[(1-c)N+(c²-c)a_j] y_j^c Q^s.    (3)

Every factor in (3), including the row-dependent geometric a_j factor and bounded Q carry, is acquired in soft O(m) whole-family metadata work. This is an exact source-preserving native point identity. It is not a free evaluation of H at a powered or row-scaled point. Its no-carry domain is only a portion of the actual a coset; repeated multiplication exits that domain and (3) is not a universal recursion.

When multiplier reduction wraps, write a_k=c²a_j-mw and v_k=c v_j+mT. The full correction is constrained by

    4wN+2c v_j T+mT²=0 modulo m².             (4)

This quadratic determines the relevant Hensel correction after its root sign is fixed, but T is a row-dependent residue modulo m². It is not a bounded common Q shift: the extra scalar phase is gamma^(mT). The value can be computed for each row within the already affordable metadata budget; an operator acquiring all associated H evaluations is additional work. Dropping (4) would replace the actual native points by their uncarried residues.

## Acquisition endpoint

The Mobius candidates (2) and exact bounded-carry native identity (3) are acquired in soft O(m). They are stronger point descriptions than arbitrary target advice. Neither supplies the missing whole-family evaluator: dyadic states require the full cubic condition (1), while general multiplier wrapping introduces the additional row-dependent phase (4), and the no-wrap domain does not cover all tags under iteration. Prepaying gamma=gamma0^(2^D) makes the chosen root directions coherent and preserves recovery, but does not itself merge these target origins.

No sublinear whole-input target-orbit representation or soft-O(m) acquisition algorithm was established in this pass. The remaining constructive requirement is an operator acting simultaneously on the actual powered points and carried phases in (3)-(4), or a different carrier whose state compression is proved and whose original scalar zero mask is retained.

## Amendment after independent review

The reuse criterion (1) is necessary only for the stated literal integer-exponent/stride identification. Scalar equality locally or globally can additionally occur when the exponent difference is a multiple of an unknown local or global order. No such accidental coincidence is excluded or decided by the cubic test. See `review-native-multiplier.md`. This clarification preserves the original investigation and does not claim that shifted recursion origins are compressed.
