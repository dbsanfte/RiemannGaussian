# Actual full-N high-digit folding probes miss every local collision on a retained majority

2026-10-15. New classical actual-family counting argument. No Lean theorem, general scalar lower bound or acquisition algorithm is claimed.

## Statement, including arbitrary bounded offset selection

Use the same original ordered balanced prime-pair supply N=P Q, scale X=M^3, and first-K candidate-prime menu as the verified endpoint/catalog reports. Its size is Omega(M^6/log^2 M). Here the original supply means the inherited prime-order supply satisfying the listed local-order/menu premises, before the further frozen observation deletions; the new count does not assign those order premises to inputs discarded while constructing that supply. Let K_*=O(M^.020) dominate the menu, and prescribe any nonnegative integer shift envelope S=S(M)<=M^.004.

For every candidate m, every integer offset delta in [-3m^2,m^2], and every integer shift |s|<=S, define the ACTUAL full-input-dependent probe

E=N+delta,
i_delta(N,m)=floor(E/m^2) mod m^2, in {0,...,m^2-1},
A_(delta,s)=gamma^E-gamma^(m^2*(i_delta+s)).

Here gamma is the actual public projected base at that m. Delete an original input if ANY such probe is zero in EITHER hidden prime field at ANY permitted m. The deletion count is

O(K_* V(S+1) M^5), V=O(M^.969),

hence O(M^5.993) when S<=M^.004. For polylogarithmic S it is soft O(M^5.989). Both are below the frozen soft O(M^5.994) deletion and below the supply exponent six. Thus the same original supply, after all frozen deletions and this new direct union, retains Omega(M^6/log^2 M) inputs on which EVERY probe above is a unit modulo N.

The actual canonical first-current targets have delta=delta_j in this band, so this theorem simultaneously defeats ALL tags and every allowed shift around their folded digit index. It even allows the offset and shift to be chosen using full N, prior observations or arbitrary advice, as long as they stay in these envelopes: the theorem grants every offset and shift simultaneously, not merely one prescribed catalog. It does not grant different digit-folding formulas or arbitrary index choices outside the envelope.

For polylogarithmic S, probing actual canonical tags at these indices costs soft O(m) per candidate modulus with standard powering and gcds. Enumerating every possible offset, polynomial S, or the polynomial prime menu is granted for coverage only; no nearlinear clock is assigned to those expanded observations.

## Verified historical premises

The two historical archive originals and journal menu hypotheses were independently verified in coverage/endpoint-independent-review.md and catalog-independent-review.md from the prior follow-up directory. Exact source pins are recorded beside this report. We use only:

1. P,Q=Theta(M^3), in a fixed ratio-at-most-3/2 bin, with original pair supply Omega(M^6/log^2 M).
2. Every retained candidate m has m=Theta(M), and gamma has exact local prime order R_P>P^.677 in the P field, and similarly for Q. Write P-1=v_P R_P with 1<=v_P<=V=O(M^.969). These are proof-side supply facts, not algorithmic order inputs.
3. With G_m=m-p_(-K_*)(m), the necessary candidate-selector envelope is (m-G_m)^6<N<=m^6. Its frozen telescope is sum_m(G_m+1)=O(K_*M), and G_m=o(m).
4. Actual first-current offsets obey -3m^2<=delta_j<=m^2.

The new proof needs no tag congruence, false-tag Hensel uniqueness, stationary phase estimate or additional prime-distribution theorem.

## Exact digit decomposition; no boundary exceptions

Euclidean division gives, exactly,

E=m^4 t+m^2 i_delta+r,
t=floor(E/m^4), 0<=r<m^2.

Hence

E-m^2(i_delta+s)=m^4 t+r-m^2s=:n_(m,t,r,s).              (1)

No assertion that t=floor(N/m^4) is needed. Offsets can cross a high-digit boundary without invalidating the proof.

For any N in the candidate-selector envelope and any permitted delta,

(m-G_m)^6-3m^2<E<=m^6+m^2.

Consequently t belongs to a common m-only integer interval T_m with

|T_m|=O(mG_m+1).

Indeed its length is at most ((m^6-(m-G_m)^6+4m^2)/m^4)+2, and the sixth-power difference is O(m^5 G_m). Also t=Theta(m^2), uniformly, since G_m=o(m). For |s|<=M^.004, equation (1) is a positive integer of size Theta(M^6). In particular n is never zero, so the divisor count below has no exceptional zero integer.

## Count large prime divisors before the hidden prime P

Fix m,t in T_m,r in {0,...,m^2-1}, and shift |s|<=S. If the probe is zero in the P field, then its exact local order R_P divides the positive integer n_(m,t,r,s).

This integer has only O(1) prime divisors exceeding c M^2.031: if h distinct such primes divided it, their product would be at least (c M^2.031)^h, while n=O(M^6). This is a uniform constant bound. We enumerate ALL these large prime divisors for counting only; the algorithm is not given them or asked to factor n.

For each such possible R, the hidden prime must be P=1+vR with 1<=v<=V. There are at most O(V) possibilities for P, even before imposing that P is prime, lies in the source bin and has the correct actual projected order. Every restriction can only decrease the count.

Fix one resulting actual P. If this state (t,r,s) arises from ANY offset delta in the band for some partner Q, then t=floor((P Q+delta)/m^4), which forces

m^4 t-m^2 <= P Q < m^4(t+1)+3m^2.

The corresponding Q interval has width

(m^4+4m^2)/P=O(M)=O(m),

because P=Theta(M^3) and m=Theta(M). Therefore it contains only O(m) integer partners Q TOTAL. This bound already grants all tags, offsets, residues r consistent with the state, and all source qualifications. There is no additional factor m for the tag list, and no need to prove a unique Q per tag. Counting prime Q can only reduce this bound.

Thus each fixed (m,t,r,s) gives O(V m) bad input pairs in the P orientation.

## Whole-menu and joint count

Multiply the preceding bound by |T_m|=O(mG_m+1), m^2 choices of r and 2S+1 shifts. Summing m gives

O(V(S+1) sum_m (mG_m+1)m^3)
 <=O(V(S+1) M^4 sum_m(G_m+1))
 =O(K_* V(S+1) M^5).                                  (2)

The inequality uses m=Theta(M), with fixed uniform constants. Reversing P,Q costs only a factor two; no order relation between the two primes was required by the count. We count on the ORIGINAL supply and then unite all frozen deletions, rather than intersecting unrelated sparse families. At S<=M^.004, exponent .020+.969+.004+5=5.993 is strictly below 5.994. Fixed powers of logarithms do not alter the strict gap to exponent six.

## Interpretation and exact scope

For actual first-current delta_j, i_delta is exactly floor((N+delta_j)/m^2) mod m^2, so these observations depend on the full input's high digits and are outside the earlier fixed m,j-only catalog theorem. Their failure is proved directly here.

All numerator residuals on the surviving family are units. Products and inverses formed solely from these residuals remain units, so no multiplicative boundary expression built from this observed support has nontrivial gcd. The full canonical seed rectangle nevertheless retains its already compiled forced collision and proper recovery. The theorem does not preclude arbitrary additions, new residual constructions, different adaptive index formulas or the still-unpaid implicit long-query evaluator.

A stronger counting feature is that delta can vary over the ENTIRE bounded source band without an extra factor in (2). The digit decomposition grants all low residual digits r, and the narrow Q interval then absorbs all source tags/offsets. This is why an N-dependent choice inside the stated envelope is allowed here, unlike a post-hoc N-dependent choice in the prescribed-catalog theorem.

## Corollary: one prescribed public fold modulus, including the actual search length

Fix in advance ONE public m-only positive integer family W_m with

c m^2<=W_m<=C m^2

for fixed positive constants c,C. Replace the index rule by

i_delta=floor((N+delta)/m^2) mod W_m,

and keep all other hypotheses, offset/shift envelopes and observations unchanged. The same deletion bound (2) and simultaneous-unit conclusion hold, with constants allowed to depend on c,C. This applies in particular to W_m=2m^2+2 and to the CURRENT native padded search length W_m=SemiprimeSeedSumAcquisition.seedLength(m). Its already compiled seedLength_bounds theorem states 2m^2+2<=seedLength(m)<=4m^2 for m>=4. The exact native source hash is recorded in high-digit-source-pins.json.

Proof. Put A_m=m^2 W_m=Theta(m^4). Exact Euclidean division now gives

E=A_m t+m^2 i_delta+r,
t=floor(E/A_m), 0<=r<m^2,
E-m^2(i_delta+s)=A_m t+r-m^2s.

The selector and offset envelope put t in a common m-only interval of length

O((m^6-(m-G_m)^6+4m^2)/A_m+1)=O(mG_m+1).

Uniformly, t=Theta(m^2) and A_m t+r-m^2s=Theta(M^6)>0. The same O(1) large-prime-divisor count therefore applies. For each possible P=1+vR, the existence of an offset in the band forces

A_m t-m^2<=P Q<A_m(t+1)+3m^2.

This partner interval has width (A_m+4m^2)/P=O(m), still absorbing all tags and offsets without any additional multiplicity. The choices of r and s and the menu telescope are unchanged, proving exactly the same asymptotic bound.

This is ONE prescribed W_m family at a time. There is no free simultaneous union over every possible W_m, and W_m may not be chosen using N at fixed m unless an independently bounded prescribed family is counted separately. Uniform proof constants alone do not grant that union. Choosing W_m to be the fixed native padded length is permitted because it depends only on m. A polylogarithmic prescribed menu can be united with its actual logarithmic cost; no such menu is needed for this corollary.
