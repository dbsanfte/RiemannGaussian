# Public residue controllers, both-prime phase faithfulness, and the missing supplier

26 October2026. Paper derivation, no tests, code, Lean or repository edits. Read the archived axis-controller and phase/multisection interfaces. **Positive:** public integer-AP controllers can repair the auxiliary phase-faithfulness premise at BOTH primes within soft k; a weaker certificate for q alone even costs soft sqrtk. They can also certify an independently chosen auxiliary modulus. The attempted phase-projector readout is fully initialized below but retains the long product cost; no useful residue is supplied at soft k and no forced-continuation claim is made.

## 1. Clean controller with a BOTH-prime implication

Use the hard branch N=P Q, distinct odd P<Q, B=floor(sqrtN), N<=k^6, H=k², k=2*3^e, P,Q>16H. Let a public modulus M be a unit modulo N. For an acquired residue r modM, evaluate the INTEGER product of all2<=n<=B with n=r modM. Normalize by the unit M to a scalar factorial progression. Initialization, length clipping and its evaluation cost

    soft O(1+sqrt(B/M+1)).                         (1)

Every leaf is a positive integer<Q. Thus a nonunit product gives the PROPER factor P directly, never a saturated N gcd. The literal n=1 is not needed; no zero leaf is present. These are old integer-AP/factorial operations, not a new factoring algorithm.

Test TWO residues1 and N modM. If P=1 modM, the first contains P. If Q=1 modM, PQ=N forces P=N modM, so the second contains P. Therefore UNIT results for both tests certify

    neither P nor Q is1 modM.                      (2)

Test -1 and -N as well to exclude -1 for BOTH primes. Duplicate residue classes are harmless and may be merged. This is stronger than applying only the old P=+/-1 controllers; it uses the product relation to turn larger-prime ramification into a supplied smaller-prime residue.

The cap matters: a controller through c*k²*M with c<2 need not reach B when M=k/2. Failure below P implies no exclusion at P. In the full-cap algorithm(1), B<=k³ and M=k/2 give length at most2k²+1, hence soft k cost per residue. Equivalently c>=2 at that maximal axis modulus pays the full smaller-factor range. No factorization branch is presumed to continue; every nonunit test returns its verified factor.

## 2. Exactly which order conclusion is certified?

Take M=3^a. From(2), v3(p-1)<a for BOTH p=P,Q. Since q=beta^(4*3^(2e)), ord_p(beta)|p-1 gives

    v3(ord_p(q))=max(v3(ord_p(beta))-2e,0).

Hence a<=2e+1 certifies ord_p(q) coprime to3 at BOTH primes. This requires no roughness premise. Two useful fully paid choices are:

* **Phase-faithfulness only:** M=3^(2e+1)=3H/4. The two full-cap AP tests cost soft sqrt(B/M+1)=soft sqrtk. On continuation v3(p-1)<=2e, so q is3-coprime. The stronger root clocks below need not have the same order under this weaker certificate.
* **Existing native root clocks:** M=3^(e+1)=3k/2 (or the older M=k/2, at the same soft-k rate). The tests cost soft k and certify v3(p-1)<=e (respectively<e). Then rho=beta^k and q have EXACTLY the same local orders, all odd and3-coprime. More generally beta^(H/d), for every divisor d|k, has that same order: the remaining3-adic exponent is at least e and the original beta orders are odd.

The optional minus residues certify the analogous v3(p+1) bound for future norm-one torus groups, but do not import a torus point or its collision theorem into this scalar query. These are factor-or-certificate prepasses. They do not prove the low-ramification branch occurs for every input or force continuation on any previously constructed family.

The original root observation is therefore valid at the SMALLER prime only when the chosen cap covers P. The paired N-residue test is what makes its implication genuinely BOTH-prime. Conversely a failed plus-only smaller-prime menu says nothing about v3(Q-1).

## 3. Execute the repaired auxiliary phase filter

For d|k, after the q-only certificate, adjoin a primitive dth root zeta in S=R[Z]/Phi_d(Z). Hidden characteristics exceed d and gcd(d,N)=1; each local primitive component has exact order d. The actual kernel query has acquired C=ceil(N/(2k)), V=O(sqrtk), W=O(sqrt(N/k)+sqrtk). For a supplied rho modulo d define

    A_rho=product_(|b|<=V,|h|<=W,h!=Cb)
             (1-q^(Cb-h)*zeta^(h-rho)).             (3)

Both local q-orders are now coprime to d (2-primary tameness is inherited from their odd orders). Consequently a factor is zero locally iff q^(Cb-h)=1 AND h=rho mod d. Thus its norm has the faithful original residue predicate at BOTH primes. The earlier conditional phase statement can be repaired by this PAID prepass on the universal-kernel family, whose Fermat coverage remains valid for the unchanged base.

Literal h=Cb is omitted before constructing(3) in every channel. No norm zero of a zero exponent is assigned an annihilator. In a direct implementation, each b contributes a geometric string of ratio zeta/q, with direct literal splitting; the extension rank is phi(d). The previous monic backend computes its actual coefficient vector at rank-dependent cost, followed by a paid norm/localization. The conservative division-free completion remains soft O(phi(d)*N^(1/4)+phi(d)^4+T_ext), not rank-independent. This is an acquired algorithm, not a root-of-unity symbol counted as a scalar value.

Direct AP evaluation is better: for a given rho it costs soft O(V+sqrt(V*(W/d+1))+T_ext). Residue refinement beginning modulo2 and then multiplying by3 really supplies a useful h modk (or a factor), but its first coarse tests cost soft sqrt(VW)=soft N^(1/4). Summing the geometric refinement costs does not remove that first payment. These are the strongest already initialized readouts in this attempt, and neither is soft k.

Taking the cyclotomic norm of one FIXED rho channel retains that channel's filter; it does not select a useful rho. With prime auxiliary d, the local factor norms are(1-x)^(d-1) for h=rho mod d and Phi_d(x) otherwise, x=q^(Cb-h); on the repaired coprime branch the latter are units. Combining ALL rho channels instead gives product_(rho mod d)(1-x*zeta^(h-rho))=1-x^d, whose zero predicate is the whole original query under the coprime-order gate. These are faithful finite filters and their combined predicate, not a supplier of the unknown nonunit channel.

## 4. Acquired root clocks/projectors do not supply the axis phase

Under the stronger certificate, rho=beta^k is an acquired k-th root of q with the SAME local order. For d|k the root beta^(H/d) is likewise acquired and order-preserving. One can acquire finite interpolation projectors on small supplied root-clock point lists in soft k, using their certified short differences. This does not acquire the long unknown q-orbit value or the nonunit channel in(3).

There is an exact caution: when the local q order r is coprime to d, an exponent-residue homomorphism q^h->h modd cannot be well-defined, because q^(h+r)=q^h but r is nonzero modd. The improved phase-faithfulness certificate therefore does NOT make h modd an intrinsic character of the q-group. The auxiliary zeta records the EXTERNAL integer clock label. This statement rules out only that quotient-character interpretation; it is not an impossibility theorem for interval-promised arithmetic algorithms or a new modular-discrete-log lower bound.

The old axis-to-kernel transport remains exact: an ODD-phase axis hit with e=t+1-kI gives h=e/2!=0 and h=(t+1)/2 modm for odd m|k. But neither equal root-clock orders nor projectors compute t modm. The additive AP certificates exclude a few public ramification residues and return factors when their hypotheses hold; after unit continuation they do not identify the useful axis phase among the remaining values. The original phase may still be an accidental alias rather than -P modm, so no factor-residue decoder is invoked on it without provenance.

## 5. Multi-modulus variant, executed and charged

The same BOTH-prime certificate works for any public prime ell: test residues1,N mod ell through B. On unit continuation ell divides neither p-1, so ell is coprime to both local q orders, independently of whether ell divides H. Choosing a public ell in[k,2k] by ordinary sieving costs soft k; its two AP tests also cost soft k. A residue h mod ell is sufficient for the universal-kernel consumer, since V*(W/ell+1)=O(k²). The faithful phase filter can therefore use ell instead of a3-power.

This changes the auxiliary conductor and supplies its order-coprimality honestly; it does NOT acquire the residue. The rank of R[zeta_ell] is ell-1=Theta(k), and a direct phase readout still costs with that rank. Testing every ell residue directly costs soft k². A polylogarithmic collection of such moduli retains the preparation budget, but separate useful residues need not belong to the SAME collision, so a CRT reconstruction cannot combine them without a matching-hit theorem. No small covering palette follows from conductor freedom.

For a fixed finite smooth set of primes one may instead remove their order parts by a factored powering exponent and rerun the actual short-order screen, using the old rough preparation and annihilator branches. That is prior credit. It likewise supplies automorphisms/injectivity, not an acquired coarse hit phase. No cost of a new base, changed screen, or auxiliary algebra is omitted here.

## Outcome and sources

The exact repair is constructive: paired public AP residues certify3-coprimality at BOTH primes (soft sqrtk for q alone, soft k for the stronger native root clocks) or return a factor. Multi-modulus phase faithfulness is similarly paid. The best actual residue supplier tested after it remains soft N^(1/4), and the old native soft-k^(5/4) route remains better. Thus this pass repairs a premise but does not count that lemma as supplying the original missing residue.

Inputs/old methods: [axis controller](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-string-projective-20261026/axis-controller.md), [multisection](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-knot-string-supplier-20261026/multisection.md), and [kernel coverage/consumer](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-hybrid-audit-20261026/coverage-selector.md). The AP factorial engine, old roughening and T_ext=soft N^(31/192) are credited there. All new order conclusions above follow by exact Fermat and valuation arithmetic; no primary literature theorem about quantum characters is imported, no actual-factor counterfamily is inferred from formal congruences, and no sixth-exponent solution is claimed.

## Addendum: the sharper correct-factor-residue consumer

The new independently audited Harvey–Hittmeir specialization is taken here as an INPUT theorem: for S supplied candidates for the CORRECT smaller-factor residue modulo n|k, the complete bound is

    soft O(S*r+sqrtN/(n*r)^(3/2)),

with beta^(n²) retaining the required local-order bound because n|k. Choosing r=ceil(16k/S) fits soft k when n is at least a suitable constant times S*k^(1/3). Thus one correct residue modulo order k^(1/3), or S=O(k^(2/3)) candidates at n=k, is sufficient. This is genuinely a weaker supplier specification than the older coarse-factor decoder; it is not itself an acquired residue. The exact finite constants and the complete HH algorithm remain the companion audit's responsibility.

### Distinguish the three clocks and outputs

* The full axis query with an explicitly supplied smaller-factor cap B has cost soft sqrtB after its phase interval tiles. A supplied useful axis phase modulo m reduces this to soft sqrt(B/m), plus recovery. In a gamma subfamily B=Theta(k^(2+gamma)), its unsupplied full axis query is k^(1+gamma/2), not automatically N^(1/4).
* The FULL universal-kernel query has V starts and clock W, costing soft sqrt(VW)=soft N^(1/4) in the hard scale. The axis-to-kernel bridge may enter a shorter b=0 extension; it does not assign the whole universal W clock that shorter cost.
* The NEW HH consumer requires a correct FACTOR residue P modn (or a palette containing it). An arbitrary useful axis alias phase t need not equal -P modn, and the BOTH-prime phase-faithfulness certificate does not establish that equality. Therefore it cannot be fed to this stronger arithmetic consumer without a provenance/transport theorem.

### What the gate can now exclude, and what it does not select

Granting the new bounded consumer, one can test the constant public candidate set{+1,-1,+N,-N} at any3-power n|k with n of order at least k^(1/3). If it returns no factor, completeness excludes these smaller-factor residues; by PQ=N this excludes +/-1 modulo n at BOTH factors. This can strengthen the earlier ramification certificate to v3(p+/-1)<log_3(n), without a new assumption on the q order. It remains a factor-or-exclusion operation, not a recognized branch that must continue.

This supplies no small retained palette by itself. Let n0 be the smallest tested3-power of order k^(1/3). Each of its four excluded unit residue classes has k/(2n0) odd-unit lifts modulo k. Therefore at most2k/n0=O(k^(2/3)) of the phi(k)=k/3 possible colours are excluded; Theta(k) remain. Running the same +/-1,+/-N tests at all higher nested3-powers supplies no independent density gain: their excluded classes project into those same four classes modulo n0. At n=k the new consumer allows only O(k^(2/3)) RETAINED candidates, whereas these tests leave Theta(k). At n0 it permits a constant retained palette, whereas a growing number of residues remain. These are exact counts for the tested congruence exclusions, not a claim that all remaining classes are realized by prime divisors of one N.

Starting a ternary search at modulus3 does have a complete candidate menu, since P is a unit. But for constant S the displayed HH bound at such a small n retains the above-budget sqrtN/(n*k)^(3/2) term. The new threshold does not supply its first cheap branch. Conversely testing a complete menu S=Theta(n) at once gives, after writing m=n*r, the bound soft(m+sqrtN/m^(3/2)), optimized at soft N^(1/5). This is the already known general HH-scale completion, not a new supplier or a sixth-exponent gain. Deleting only constantly many classes leaves that asymptotic menu size unchanged.

The weaker threshold DOES make a smaller future selection theorem useful: an actual constant palette of correct residues modulo n~k^(1/3), or an order-k^(1/3) reduction in the full-k candidate count, would now close the arithmetic consumer. The phase gate repairs the filter premise but has not computed such a palette. A phase-provenance theorem could also be valuable, but faithfulness of an external integer phase channel is not that theorem. No general obstruction to a stronger global arithmetic selector or a new joint HH acquisition is claimed.
