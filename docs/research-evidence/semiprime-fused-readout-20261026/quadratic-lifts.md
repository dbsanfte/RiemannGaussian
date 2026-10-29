# Fixed weighted coefficient blocks are exact quasi-periodic chirps

26 October 2026. Paper-only arithmetic derivation and finite contraction test; no repository edits, code, tests or numerical campaign.

**Positive executed contraction:** fixed weighted coefficient blocks have quadratic phases on parity-adjusted colour lifts. Section 4 proves a coverage-safe soft-K completion, pays canonical-carry endpoint gates, and contracts each complete chirp into O(log g) GP strings by exact square strata. All normalized starts and additive residue weights are acquired. The whole-bank cost remains the existing soft-K^(5/4) rate. Sections 1–3 record the original actual-mask derivation and baseline test; §4 supersedes its need to preserve that mask for coverage.

## 1. Correct parity and quadratic phase

Let pure K=2*3^e, H=K², a=gA,b=gB, g=gcd(a,K)=gcd(b,K), and g²<=K. Put n=K/g. Dividing the stationary congruence gives

    A j²=BN mod n.

A and B are units modulo n. Unit square roots modulo n have at most two branches (the 2-part has exponent at most one). Fix a branch j0; if n is odd, choose its odd representative modulo 2n. Define epsilon=1 when n is even, epsilon=2 when n is odd. All its odd unit lifts modulo K are

    j=j0+epsilon*n*t, 0<=t<g/epsilon.

Here epsilon divides g. An actual Gauss row table may retain only a subset of these lifts, and may have duplicates. That subset/multiplicity remains part of the acquired input; do not silently complete it.

Choose v=j0^{-1} modulo H and the supplied integer

    d=(BN*v²-A)/n.

The numerator is divisible by n by the branch equation. Expanding the inverse of j0+epsilon*n*t modulo H gives

    ell(j)-ell(j0)
       = (H/g)*[epsilon*d*t-epsilon²*BN*v³*t²] mod H.   (1)

Indeed the linear term is g*epsilon*n*t*(BNv²-A), and the quadratic term is -g*BN*epsilon²*n²*v³*t². Every cubic or higher term vanishes modulo H. For the cubic term the required quotient is epsilon³*K/g², an integer: if g is odd, its 3-adic divisibility follows from g²<=K; if g is even, epsilon=2 supplies the missing 2-power. Higher terms multiply this by another integer epsilon*n. This parity point is necessary; g²<=K alone does not literally imply g² divides K when g is even.

Take Q(t) to be the centered residue modulo g of the quadratic in brackets. With the actual centered phases define

    k_t=[ell(j)-ell(j0)-(H/g)Q(t)]/H.

Then k_t is an acquired integer in {-1,0,1}, since the phase difference has absolute value less than H and the centered correction has absolute value at most H/2. With q_g=pi^(H/g), the actual roots satisfy globally

    y_j=y_0*q_g^{Q(t)}*q^{k_t}.                        (2)

The fixed barpi exponent a+bN cancels exactly. All identities are arithmetic modulo H followed by their explicit integer lift; no unknown group order is used. Computing branch labels, Q and carries for all retained rows costs soft J after reading the actual row table.

## 2. Execute a finite chirp recursion

For a complete interval of t with NO carry mask, define the finite scalar product

    P_m(z;r,s)=product_(t=0)^(m-1)(1-z*r^t*s^{t²}).

For m=3l, direct reindexing t=3u+a gives

    P_(3l)(z;r,s)
      =product_(a=0)^2 P_l(z*r^a*s^{a²}; r³*s^{6a}, s^9). (3)

Remainders m mod3 are explicit final factors. This is a finite cleared identity over the actual ring and does not require an auxiliary root of unity or an invertible rejected factor. The corresponding clock product keeps a second index i and factors 1-z*r^t*s^{t²}q^{-i}; (3) remains valid with the SAME finite i-window in each child.

This executes a genuine ternary transfer, but it gives three child parameter triples, not a single parent scalar whose boundary is known. After depth log_3 m it has m initialized chirp factors. The clock length has not shrunk. If the clock is also split modulo three, there are nine finite children with the appropriate starts; their total row-clock mass is unchanged. This is a cost statement for (3), not a general exclusion of a better chirp norm identity.

For the actual input (2), keep three explicit masks according to k_t. Q(t) can instead be left uncentered and its larger integer carries retained. Neither representation permits division by a masked-out factor: a rejected row may be an accidental nonunit. The recursive algorithm must pass each actual subset/multiplicity mask to its children. Its total input support is J, and this can be read and propagated in soft J; it does not become a complete Gaussian sum merely by forgetting that support.

A fully initialized safe scalar completion is to acquire the actual roots from (2), and run the old division-free shared geometric-product engine over the unchanged finite clock. It costs soft(J+sqrt(Jh)), with the existing labelled decoder. Executing separate fixed-(a,b) blocks gives a sum of their such costs and need not improve the joint engine. Equation (3) alone gives no smaller bill.

## 3. Why the usual finite Gauss evaluation does not apply to this exact block

Here q_g^g=q, and q is a supplied high-order rough element; q_g is not a g-th root of unity. Thus Q(t) modulo g changes a scalar factor by q, exactly the carries in (2). The usual finite Weil/Gauss orthogonality at an auxiliary primitive g-th root does not evaluate this product or remove those factors. Auxiliary Fourier encoding is possible only with all its coefficients, its representation extension and the carry/mask multiplication charged; no such initialized compressed norm was obtained from (3).

At this stage of the original actual-mask test, the input is a parity-adjusted quadratic chirp with explicit carries and retained support. A standard root-of-unity Gauss sum does not evaluate it. Section 4 now supersedes that limitation by proving a lawful soft-K completion to a larger coverage family and an exact GP-stratum contraction; the original mask is no longer required for coverage after that paid completion. The exponent conclusion remains unchanged.

## 4. Positive completion and square-stratum collapse (updated execution)

The earlier masked-recursion execution is not the strongest available operation. There is a lawful completion whose TOTAL size stays soft K, followed by an exact non-root-of-unity chirp collapse.

Complete each DISTINCT acquired nonaxis pair (a,b) to every unit colour satisfying a j²=bN modulo K. These extra rows retain the SAME weighted coefficient bound and the canonical stationary phase, so in the correct factor-size bin the inherited exact-integer argument applies to them too. This is an overcover, not equality with the old Gauss multiset. Duplicated input copies may be discarded before completion for the factor/residue task; original covered witnesses remain. Added multiplicity cannot be omitted from the new residue count.

For content g, the number of signed nonzero pairs with |ab|<=K is O((K/g²)log K), by writing a=gA,b=gB and using the elementary hyperbola count. Each pair adds at most 2g unit colours (in fact 2g/epsilon). Thus the completed table has

    O(K log K * sum_(g|K) 1/g)=soft K

rows for pure K=2*3^e. The sum is bounded by (1+1/2)sum_{r>=0}3^{-r}. Acquiring all phases, numeric roots and tags is paid by this bound. A public total-count check below 16H makes every good hit count less than R; the proven soft-K bound ensures this for all sufficiently large K, and bounded remaining inputs can use the existing finite controller. This is not an assertion that an arbitrary conductor has polylogarithmically many divisors.

Keep the two square-root branches separately, with their tag j0 modulo n=K/g. Every added good-field hit on a branch has this same tag. Consequently the later fusion can retain the sector's HH pair; it does not require recovering which lift t hit.

### Normalize the signed clock and recompute canonical carries

Write the actual inherited physical interval as i=-M0,...,-M0+h-1. Define T_j=q^M0*y_j and Z0=q^M0*y0, so its normalized factors are 1-T_j*q^{-t}, 0<=t<h. This normalization is required even though it is an acquired unit scaling.

Before endpoint gates, rebase DIRECTLY to the FINAL canonical phase e in [0,m), where m=3^{v3(g)} as below:

    ell(j)-ell(j0)=(H/m)*e+H*k'_j,
    T_j=Z0*qhat^e*q^{k'_j}.

Here k'_j is recomputed from the actual integer phases, not inherited from the centered-Q representation. Since the phase difference lies strictly between -H and H and the canonical correction lies in [0,H), k'_j is -1 or 0. Thus centered-to-canonical conversion never silently loses a further q carry. The more conservative four normalized endpoint indices t=-1,0,h-1,h cover every change of finite interval. Screen those endpoints for every completed row before removing the shifts. A proper norm/coordinate gcd factors; a saturated point equality has the known scalar beta annihilator 2E, where

    E=ell+a+bN-H*(t-M0).

The physical endpoint index is i=t-M0, not the normalized t. Here b!=0 and |bN| dominates |ell|+|a|+H|t-M0| under N>256H² and the actual signed short weighted clock bound. Hence E!=0, including a physical endpoint i=0, so the licensed saturated extractor applies. All original axes are handled separately with their existing provenance, not smuggled into this dominance argument. The endpoint bank costs soft K, with any terminating extractor once only.

If every endpoint is a unit, replacing each carried root by its uncarried root changes neither hit membership nor its per-row residue count/tag. It need not preserve the scalar norm value: the two products differ by a known-endpoint UNIT. Thus it is legitimate for the zero/nonunit and additive-residue targets, not an equality obtained by cancelling a possibly zero factor.

### Exact square strata, including even content

Put m=3^{v3(g)}. If g is odd, m=g and the phase variable is Q(t) modulo m. If g is even, epsilon=2, Q(t) is even, the lift interval has length m=g/2, and use Q(t)/2 modulo m. In both cases write

    qhat=pi^(H/m), qhat^m=q,
    phase(t)=c+A0*(t+t0)² mod m,

where A0 is a 3-unit and t runs through ALL residues modulo m. Completing the square uses only the known inverse of 2A0 modulo m; this is public integer arithmetic. It does not invert a native collision factor.

For m=3^a, the nonzero square valuation 2r<a gives exactly the residues 3^{2r}(1+3v), 0<=v<3^{a-2r-1}, each with multiplicity mu_r=2*3^r. After the affine transformation by c,A0, this is still one canonical AP

    e=e0+Dv, D=3^{2r+1}, L=m/D, 0<=v<L,

with e0 the appropriate residue modulo D. The zero-square stratum is the singleton e=c modulo m, with multiplicity mu_zero=3^{floor(a/2)}. All phases, AP starts and multiplicities are explicitly computed. At a=0 there is only the singleton, multiplicity one. This covers every parity-adjusted lift exactly with its multiplicity.

For one such AP, the uncarried finite product is EXACTLY

    product_(v=0)^(L-1) product_(t=0)^(h-1)
         (1-Z0*qhat^{e0+Dv}*q^{-t})
      =product_(u=-L(h-1))^(L-1)
         (1-Z0*qhat^e0*(qhat^D)^u).                 (4)

The bijection is u=v-Lt, with t the normalized clock index. Thus it is ONE consecutive GP string of length Lh, raised to the known multiplicity mu_r. No auxiliary root of unity is used; qhat^m=q is precisely what makes the finite boxes concatenate. The singleton stratum is the same formula with L=1 and base q. Actual group exponents and all integer endpoints are supplied.

The existing native window bound h<=8K^{3/2}+9, together with g²<=K/sqrt(3), bounds these string lengths by less than 16H for K>16 (using the actual Gauss product bound). Their bases are powers of pi by 2,3-smooth integers, so the prepared roughness gives the same local order as q. Therefore per-string zero counts have the same one-hit guard. Even without that last simplification the finite product identity (4) remains exact, but a mask-only count would then require multiplicity care.

### All string starts and batched cost

For each (g,r), all AP strings have the SAME acquired base qhat^D and the SAME length Lh; their starts Z0*qhat^{e0-DL(h-1)} are explicit and acquired in soft K overall. Let J_{g,r} be their number. There are at most two branches per completed pair, so

    J_{g,r}=O((K/g²)log K).

A shared division-free geometric query on this bank costs

    soft O(J_{g,r}+sqrt(J_{g,r}*Lh)).

Known positive multiplicities are attached to the first-residue count and branch-tag weight; their value never exceeds the completed row count. The multiplicity does not require that many identical root starts. For a completely initialized residue completion, acquire ALL GP-string values in the bank, not merely their aggregate product. Norm/coordinate classification either factors or makes each value globally zero or globally unit on a no-factor continuation. The inherited one-hit clock guard then makes its 0/1 flag the exact string residue count. Summing mu times the flags and mu times their branch tags gives the sector pair. This costs the same shared-engine bound and needs no Hasse jets. A single aggregate zero bit alone is not asserted to provide that weighted pair.

Summing over the O(log K) contents and valuation strata is geometric up to logarithms: since L<=g/3^{2r+1}, the square-root term is at most soft(sqrt(Kh)/(sqrt g*3^r)). The zero stratum has square-root cost at most soft(sqrt(Kh)/g). Thus the whole initialized bank retains

    soft O(K+sqrt(Kh))=soft O(K^{5/4})

for the weighted horizon. Within the NONAXIS content sum, the g=1 sector retains the old K-by-h scale. The separately retained axis bank can also retain the old query scale; this contraction does not solve its acquisition. Thus this execution does not improve the uniform exponent or reduce every remaining input solely to primitive nonaxis rows. This is a method cost, not a lower bound or proof that g=1 cannot admit another contraction.

**Updated outcome:** completion plus parity reduction and square strata DO give a genuine finite quasi-periodic chirp contraction to O(log g) GP strings per coefficient branch. Endpoint screens and additive tag provenance are paid. It supersedes the earlier generic ternary-recursion-only execution, while preserving the report's conclusion that no faster whole-family scalar/first-jet readout has yet been acquired.
