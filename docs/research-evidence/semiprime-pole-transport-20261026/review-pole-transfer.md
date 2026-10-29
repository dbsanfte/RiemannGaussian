# Review of the finite pole transport

26 October 2026. Independent root review of `pole-transfer.md`, after the
moving-modulus clarification. Verdict: **PASS within the stated scope**.
This is a paper check, not a Lean proof or an acquisition benchmark.

The barycentric weight recurrence follows by cancelling the two finite
products in adjacent derivatives of W. Multiplying its d consecutive
ratios gives omega_i K_d(q^i)=omega_(i+d). The last d nodes are killed by
an actual numerator zero, whereas every denominator uses a positive gap
at most h+d-1. Thus the displayed finite identity includes exactly the
first d nodes, with no endpoint residue lost.

For the monic normalization of F(q^d X)+delta, multiplying B_d over its
roots gives q^(-Jd(d-1)/2) times the original prefix product. This verifies
both the exponent and the direction of the prefix gate. Reduction of
A_d p(q^d X)/B_d modulo the shifted denominator changes the rational
source by a term with denominator B_d only. That difference is regular
in delta at every clock node. Interpolation at the separated shifted row
roots therefore suffices at delta=0 for the simple delta residue; fixed
higher jets require the stated derivative units and lifts.

The native singleton assumption is essential to dropping K_d. It preserves
a weak ratio because there is only one good hit and both numerators share
the new unit amplitude. It does not preserve the original packed additive
coefficient C on a family with multiple hits. Shortening the clock gives
the exact suffix. Keeping the clock instead needs the stated native
integer provenance and original-order margin; generic row polynomials do
not have that property. Wrong-bin rejection remains part of the consumer.

The moving quotient clarification is correct: D_d(q^e X)=D_(d+e)(X), so
substitution transports an acquired numerator lawfully. At doubling, the
second K_d factor is required at a different modulus and its denominator
tests the next original strip. The earlier fixed-modulus quotient-carry
argument would not apply to this substitution and is not used here.

The actual short and shared-product implementations cost soft(J+d) and
soft(J+sqrt(Jd)), respectively, with the stated recovery overhead. At
J=O(K^(2/3)), a length K^(4/3) prefix fits soft K. No theorem puts every
native hit in that prefix, and the geometrically shrinking full search
still costs soft(J+sqrt(Jh)). These conclusions describe the executed
algorithms and impose no general lower bound on a direct selected residue.

Primary-source scope was checked directly in Du--Huang--Li, Section 2,
Lemma 1 and Corollary 1. Their characteristic-zero/non-root-of-unity
setting is not imported into the native finite-order algebra. The finite
identity and all unit guards above are established separately.
