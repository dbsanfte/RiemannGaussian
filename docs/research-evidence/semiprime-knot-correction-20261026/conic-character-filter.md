# Paid collective quadratic-character filter

26 October 2026. This pass derives one executable sieve, including its modulus, residue masks, AP expansion and product cost. On the *nonaxis complete native catalogue* it gives a rigorous subpower saving over soft(k^(5/4)), without changing that exponent. It does not solve the full prefix: the remaining axis rows have identically square conics and retain the old worst-case cost. That exception is explicit below, rather than silently charged to the nonaxis estimate.

The sieve is an elementary finite quadratic-character operation, not an analytic Gauss-sum evaluation or a square oracle. No experiments are needed. The earlier AM–GM and event-count arguments are not repeated.

## 1. Exact native conic and safe residues

For a native label (a,b,lambda), H=k² and lambda²=4abN mod H, a physical clock index I has sum T=HI-lambda. Define the acquired integer polynomial

    f_j(I)=H I²-2lambda I+(lambda²-4abN)/H.              (1)

If I is the actual factor witness, then f_j(I)=[(aP-bQ)/k]², an integer square. Thus retaining only I for which f_j(I) is a quadratic residue or zero modulo every selected auxiliary prime preserves that witness. Swapped rows use the same a*b and lambda, hence exactly the same mask and the same physical index. Their common-index/global-zero endpoint survives. Opposite rows transport the mask by their known I->1-I or I->-I rule; alternatively keep original signed row windows and masks, which avoids needing any inverse-closure assumption.

The original nonzero-exponent deletion and consumer still apply. A false positive of the square sieve is harmless: every retained group leaf remains an original scalar collision leaf with its known nonzero integer exponent. No cancellation or inverse of that leaf is introduced.

## 2. One common modulus, not row-dependent bases

Let K denote the scale k. For sufficiently large K choose t auxiliary odd primes, all greater than 3, from an interval [B,2B] where B=C log K and C is a fixed sufficiently large constant. The prime number theorem, or explicit elementary prime-interval estimates with a finite fallback, provides t of order log K/loglog K. Enumerating and sieving all integers through 2B costs polynomial(log K). Gcd each auxiliary prime with N; a nontrivial result already factors N. Otherwise every prime is a unit modulo N. Let

    L=product_(ell selected) ell.

Use this SAME L for all rows, even when an ell divides a*b. This is crucial: row-dependent moduli would create many different arithmetic bases q^L and invalidate the single batched-cost estimate below.

For each row and prime, explicitly scan I modulo ell and retain the set

    R_(j,ell)={I mod ell: f_j(I) is square or zero mod ell}.

Tables of quadratic residues are constructed by squaring 0,...,ell-1; no character oracle is needed. All rows/prime scans cost soft(k), since B,t are polylogarithmic and J=soft(k). Combine the sets by ordinary CRT, acquiring the complete allowed residue list R_j modulo L, of cardinality A_j. Its incremental expansion costs soft(A_j) per row: each partial list has no more entries than the final list.

## 3. Exact character counts, including degenerate primes

For ell not dividing a*b*N, (1) has square nonzero leading coefficient H and nonzero discriminant 16abN modulo ell. Its quadratic character sum is -1 and its number of roots is 1+chi_ell(abN). Therefore

    |R_(j,ell)|=(ell+chi_ell(abN))/2 <=(ell+1)/2.        (2)

For completeness, the character-sum identity follows by completing the square and counting pairs satisfying u²-v²=D!=0: the change to (u-v,u+v) gives exactly ell-1 pairs. No cancellation estimate over unknown primes of N is used.

If ell divides a*b, the discriminant is zero and the leading coefficient is still a square unit. Then f_j is a square polynomial modulo ell and every residue is retained. This costs density 1 rather than 1/2, as it must. In particular axes a*b=0 get NO saving from this sieve.

Writing rho_j=A_j/L gives the uniform bound

    rho_j <= 2^-t product_(ell|L)(1+1/ell)
                         *2^omega(gcd(|ab|,L)).         (3)

## 4. Collective density bound on the actual nonaxis catalogue

The divisor/root count of the authoritative full native catalogue supplies, for squarefree D coprime to 6,

    number of nonaxis phase rows with D|ab
          <=soft(k)*tau(D)/D.                          (4)

Here is the needed specialization, so it is not treated as a random-row assumption. Write |ab|=u*v, u supported on 2,3 and gcd(v,6)=1. Its modular phase-root count is at most 32sqrt(u). Ordered divisor labels contribute O(tau(u)tau(v)). If D|v, set v=Dw and use tau(Dw)<=tau(D)tau(w). Summing w<=k/(uD) gives O(k*tau(D)log k/D) times the convergent sum over u of tau(u)/sqrt(u). Signs change only constants. This proves (4).

Because 2^omega(gcd(n,L))=sum_(D|gcd(n,L))1, summing (3) and using (4) gives

    sum_(nonaxis j) rho_j
      <=soft(k)*2^-t product_(ell|L)(1+1/ell)(1+2/ell)
      =soft(k)*2^-t.                                 (5)

The last product is exp(O(t/B))=exp(O(1/loglog k)), since the selected primes all have size Theta(log k). This is a deterministic complete-catalogue average, not independent character randomness. Any native subfamily chosen without duplicating rows satisfies the same upper bound. It is deliberately NOT asserted for an arbitrarily repeated Euclidean descriptor list; use the actual complete native catalogue, whose original coverage is already proved.

Thus the exact number of acquired CRT residues is

    sum_j A_j=L sum_j rho_j <=soft(k L 2^-t).           (6)

This charges mask expansion, including rows divisible by some or all selected primes.

## 5. Convert every allowed mask to paid AP products

For each allowed residue r in R_j intersect I=r mod L with that original row's acquired clock interval. Exact floor/ceiling gives an AP with known start and length, or an empty AP. There are at most sum A_j such APs. Their scalar factors have one common ratio q^L; the target and initial q power are explicitly acquired per AP. Negative physical indices pose no problem because q is a known unit.

The total number S' of retained original clock factors obeys

    S' <= sum_j [h_j rho_j+A_j]
        <=soft(k*(M+L)*2^-t)                           (7)

when h_j<=O(M). The additive A_j term accounts for every clipped boundary, so uniform distribution of residues within a short interval is not assumed.

Apply the existing monic variable-window product evaluator once at the common base q^L. It pays all AP starts and unequal tails in

    soft(k + k L 2^-t + sqrt(k*(M+L)*2^-t)).            (8)

All factor operations are division-free except monic polynomial divisions. No order promise for q^L through the enlarged AP range is needed by this evaluator; it does not use scalar q-factorial inverses. Original row/index labels are recovered from I=r+L*s. Aggregate zero/nonunit testing and the inherited localization/annihilator consumer remain valid. For prefix queries the mask is fixed and intersections are merely clipped, so the resulting product still has an exact monotone zero predicate with the retained witness endpoint.

## 6. Optimized nonaxis cost

For M=Theta(k^(3/2)), take

    t=floor[(1/4-1/sqrt(loglog k))*log k/loglog k]

for large k, with the finite small range handled separately. Enough primes in [B,2B] exist by choosing C sufficiently large. Then

    L <= (2B)^t = k^(1/4-1/sqrt(loglog k)+O(1/loglog k)),

so the mask/start term in (8) is smaller than the square-root term. The resulting guaranteed nonaxis cost is

    soft(k) + k^(5/4)
       *exp[-(log(2)/8+o(1))*log k/loglog k].            (9)

This is a subpower improvement within exponent 5/4, not a soft-k bound or a new global factoring record. The baseline global one-fifth algorithm is still faster asymptotically. Choosing a fixed smaller constant in t gives a simpler, slightly weaker explicit saving with the same derivation.

## 7. The full-family limitation: axes are not silently removed

The at-most-four lambda=0 axis rows have already been paid away, but lambda!=0 axis rows remain. For them a*b=0, so (1) is identically a square and all the masks above are full. Their O(k) rows can contribute O(kM) factors and restore the old soft(k+sqrt(kM)) bound if evaluated by the existing query machinery. Consequently (9) is a proved nonaxis operation, NOT a proved improvement for the entire retained family.

In the factor-correlated Euclidean source, the end-stage axes correspond to the possible small-factor alternatives in the sign-change proof. They cannot simply be discarded without a paid branch proving that a nonaxis stage still covers the actual factors. Using ordinary factor search up to their public range costs at least the already available baseline completion in this implementation; it is not hidden in (9).

A precise remaining algorithmic task is therefore to combine this acquired nonaxis sieve with a soft-k coverage-safe axis discharge or a theorem that replaces every needed end-stage witness by a retained nonaxis menu. This is separate from the now-paid quadratic-character mask operation. The present report identifies the actual surviving cost rather than asking for an unspecified square oracle.

No repository files or frozen reports were edited. No test campaign, probabilistic density premise or full-family exponent gain is claimed.
