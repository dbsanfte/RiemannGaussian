# Paid selected-shift overlap screen

22 October 2026. Independent review for the canonical source; scratch only. This supplies a concrete selected-shift algorithm, including equal-degree local gcds. It does not acquire a universally useful shift or improve the all-input factoring bound.

Let d=m², z_j=gamma^(-N-delta_j), q=gamma^d, |delta_j|≤3d. Deduplicate equal integer offsets. Assume the prepared gamma has local orders r_P,r_Q>16d, coprime, so its order modulo N is r_P r_Q>256d². The actual canonical range is narrower, [-3d,d]; the symmetric bound suffices below.

## Selected shift: all local overlaps in soft O(J)

For any supplied integer a with (|a|+6)d<256d², set y_j=q^a z_j. Build H(X)=product_j(X-z_j), and evaluate H at all y_j by monic product/remainder trees over Z/N. This costs soft O(J) ring operations, with the usual residue bit cost and O(log|a|) modular powering. No field inverse or hidden prime is needed: all polynomial divisors in this evaluation are monic.

Compute gcd(H(y_j),N) at every leaf. A proper gcd is a factor. A unit means no overlap in either field. If the gcd is N, route y_j down the root product tree for H. At each visited node evaluate the two child polynomials at the active y_j and take integer gcds with N. A proper gcd is a factor. Otherwise each active y_j routes through precisely one child: the H roots are distinct in each field, since any nonzero delta difference has absolute value below both local orders. If the two fields route into different children, that child evaluation has proper gcd and factors N.

Perform these evaluations in batches at each node, not one dense polynomial evaluation per point. At a fixed depth, the sum of polynomial degrees is O(J), and, until a factor is returned, the active point sets have total size at most J. Monic multipoint evaluation therefore costs soft O(J) per depth. There are O(log J) depths. This proves the claimed total soft O(J) localization, including when the local gcd polynomials have equal degrees or even identical sets of source indices.

If routing reaches the same partner z_k in both fields, then

    gamma^(a*d+delta_k-delta_j)=1 modulo N.

The displayed exponent has absolute value less than the known global order. It must therefore be the integer zero. Such an overlap is exactly the publicly checkable metadata relation delta_j-delta_k=a*d. Conversely this relation gives a genuine shared overlap. Consequently this algorithm either factors N or certifies that EVERY local overlap for this shift is an exact integer metadata overlap. Computing gcd(H(X),q^(-aJ)H(q^a X)) first is optional, not necessary.

One may skip points with a publicly matching partner from the start: distinctness of H roots in each field means these points cannot have an additional hidden partner. For |a|≤9 all overlaps are already metadata-only, since (|a|+6)d<16d. This is a guardrail on a small-shift strategy, not a prohibition on useful larger shifts or on accidental factors during other computations.

## What recursive squaring actually computes

Simultaneously powering the anchors and the stride by 2^k preserves every overlap relation exactly: both local orders are odd, hence multiplying an exponent by 2^k is invertible modulo either local order. Thus the powered-root polynomial product_j(X-z_j^(2^k)) and powered q do not discover an overlap absent from the original selected-shift query. Its coefficients can be computed in soft O(kJ) by successive root powering plus product trees; this is paid but supplies no new shift information.

The positive-support expansion U_B(X)=product_(0≤t<B) H(q^t X), after monic normalization, has degree JB before root coincidences are removed. Its doubling identity multiplies U_B(X) and U_B(q^B X). Retaining explicit coefficients or a root product tree costs soft O(JB). Retaining just U_B modulo H does not support the next doubling: in general the omitted multiple of H becomes a nonzero multiple of H(q^B X) after the substitution. An additional valid remainder acquisition algorithm would be needed; it is not furnished by the doubling identity.

If overlaps are discovered during this construction, the selected-shift screen above can resolve them and factor whenever they are not metadata overlaps. If no factor has been found, only exact integer overlaps remain within the stated exponent range. The canonical source has at most two tags in any fixed low-digit fiber (the already reviewed weighted-descent result), and every exact q-shift preserves that fiber. Hence arbitrary powers of q do not turn its metadata into long chains; this statement concerns the actual canonical source, not arbitrary Gauss rows.

Products of roots across pairs have up to J² roots. A gcd applied after acquiring those products must charge that degree; a compact expression alone does not provide the monic coefficients or remainder queries at soft O(J).

## Noncommensurate twists and the unresolved constructive step

Multiplying anchors by gamma^b tests exponents b+delta_k-delta_j. Powering one anchor family by c and comparing with another tests exponents involving (c-1)N+c delta_j-delta_k. Each explicitly supplied constant-degree twist is screenable by the same monic evaluation/localization method, with its degree and exponent lengths charged. An actual nontrivial local relation in the certified global-order range yields a factor, regardless of equal local gcd degrees.

Coprimality of the two local orders makes a shared nonzero edge impossible in that range; it does not by itself supply an edge for a selected finite twist set. No identity of the actual canonical offsets was found that forces one among soft O(1) such screens to contain a nonmetadata local edge. The inherited true-factor event is an anchor-versus-seed relation; subtracting two anchor exponents eliminates N and does not automatically retain that event.

The positive interface left open is precise: construct, from N and its canonical offsets, a soft O(J)-size total-degree collection of shifts/twists for which at least one nonmetadata local edge is guaranteed, or acquire a comparably cheap implicit batch of the selected-shift tests. A supplied useful shift is fully consumable in soft O(J); its acquisition remains missing. No new general obstruction, success-example campaign, or universal acquisition result is claimed.

## Prior-source boundary

The known chain/fiber fact and the lift-freedom caveat are recorded in `/tmp/semiprime-character-acquisition-20261022/discriminant_sieve/actual-anchor-overlap.md`, referring to `docs/research-evidence/semiprime-descent-query-20261016/reports/weighted-descent.md` section 2. The repository journal's 2026-10-16 channel-acquisition entry already records unsuccessful compact-circuit GCD/Graeffe searches. This note's concrete audit contribution is the division-free selected-shift screen and its matched-partner localization charge, not a new uncharged gcd oracle.
