# Independent audit of the wide-exponent rough torus supplier

24 October 2026. **PASS. No corrections requested.** Exact reviewed source: `/tmp/semiprime-large-order-recurrence-20261024/rough-torus-working.md`, SHA256 `6333f318c8bc1c1e88a398aaeff94efb83b0d2e6ead3d64d455317b41036dcda`. No source or repository changes were made by this reviewer.

## Smooth exponent, projection, and screen

The acquired exponent E contains every possible <=k prime-power divisor of either local norm-one group order, because each order is <=N+1. Its bit length is correctly charged as O(pi(k)log(N+1))<=soft k, not O(log N). The public sieve, exact exponents, factored list and balanced integer product tree fit that bound. Binary powering R^E costs O(bitlength E) fixed-rank modular multiplications; the usual polylog N bit factors preserve soft k. No factorization of N+1 is requested.

Therefore W=R^E has k-rough local orders, including possibly order one. Since every prime divisor of H is <=k, H powering preserves those orders exactly. The algorithm still runs the actual short-order screen and pays its starts/nodes/coefficients. The norm-one identity test is correct in both split and nonsplit local algebras, so a saturated norm leaf means whole identity at both primes. First-block / earlier-child exclusion yields the exact common projected order r, including r=1; it is not inferred from a saturated block alone.

The palette invariant and counts are unchanged from the audited supplier. M<k is an acquired common divisor of the two FULL local group orders. The 2M+1 points have certified small denominators and pairwise unit differences at both primes. Their two M-kernels together cover at most2M entries. The scan therefore either factors or selects an actual point outside BOTH kernels, with soft M work and only one later order screen for that selected point.

## Wide raw annihilator and complementary tree

K=EHr is genuinely a global annihilator of the RAW R. Its full factorization is obtained from the retained factors of E, public k and actual small r. Trial factoring r<=16k² uses at most4k trial divisors and costs soft k. Its bit length kappa=bitlength K is soft k and may be much wider than log N. Each individual prime-power leaf nevertheless has O(log N) bits: its E contribution is <=N+1 and its extra contribution divides polynomial-size Hr.

The complementary-power invariant R_v=R^(K/D_v) is exact. Raising by the other child's integer product gives precisely the corresponding child invariant. No quotient or inverse in B is involved. At a fixed depth the exponent products partition the leaves of K, so their logarithms sum to log K; the O(number of nodes) rounding overhead is also O(kappa). Binary powering across that level therefore costs O(kappa) group multiplications. Balanced depth O(log(w+1)) yields O(kappa log(w+1)), not kappa*w. Product-tree integers, actual rank-two group outputs, storage and all residue bit costs are included in soft k.

I checked the cached primary thesis against SHA256 `5c326306358bd06f5f0ddb47fceb2b179ce29421222acde9094ef85681c0d20f`. Sutherland Chapter7 Section7.4, Algorithm7.3 on printed pages113--114 explicitly computes all alpha^(N/N_i) by recursive product splitting and credits Celler--Leedham-Green. Its generic-group contract applies to the actually factored K; the report proves the needed exponent-bit ledger separately and does not claim a new generic order algorithm.

## Two-local valuation search, including exponent zero

At leaf ell, S_ell=R^(K/A_ell) has exact local order ell^b_p: the complementary exponent is coprime to ell and kills every other primary component. For e>=0, unit norm gcd means BOTH b_p>e, saturation means BOTH b_p<=e, and proper gcd separates them. These statements remain valid on the split side because S_ell remains norm one.

The binary search correctly starts lo=-1, hi=a_ell. The lower endpoint encodes the tautology b_p>=0, without computing an ell^(-1) exponent. The test at e=0 is S_ell^1, so the zero-valuation case is actually recognized. If hi terminates at zero both valuations are zero; otherwise the maintained strict lower and weak upper inequalities force BOTH integer valuations to equal hi. Unequal local valuations cannot be skipped: an adjacent final interval cannot contain two different valuations while preserving both invariants, so a proper gcd must occur first.

All searches are paid. A powering exponent ell^e has O(log A_ell) bits. Summing O(log(a_ell+2)) tests per leaf gives O(sum log A_ell*log(a_ell+2))<=O(kappa log log(N+2)) fixed-rank group multiplications, plus the charged small gcd work. This is soft k rather than one independent kappa-bit power per leaf. The reconstructed d is the ACTUAL common raw order at both primes, not merely a divisor of the supplied annihilator. Thus d<=P+1 and its partial integer products have O(log N) bits even though K was wide. No auxiliary wide-annihilator beta decoder is used.

## AP consumer, progress, and changed seed

For d>=k, the two exact progressions di+1 and di-1 contain the smaller prime regardless of its unknown split sign. All retained terms lie between2 and floor(sqrt N)<Q, so any nonunit product gcd is proper. The special d=P+1>sqrt N case is retained by the minus progression's term d-1=P. Real starts, full blocks and literal tails avoid overhang. The number of terms is O(sqrt N/d+1), giving baby size O(k) from N<=k^6 and d>=k. Thus the complete factor consumer, not just an AP expression, is within soft k.

If d<k, selection outside the old M-kernel proves d does not divide M. The lcm update remains a known common divisor and grows by an integer factor at least two. It either reaches the AP threshold or permits another valid small-kernel palette. There are O(log k) iterations; palette costs sum geometrically and the soft-k screens/extractions repeat only logarithmically. All exponentiation widths and small-r factorizations remain charged. The observation that a nontrivial projected r is k-rough and >k is correct, though the proof does not rely on it.

Using the returned W in every native row preserves norm-one Frobenius coverage and target norms beta^(2E). Rows are reacquired within soft k, and the ACTUAL coupled-seed screen is rerun. Large rough W order does not certify split-coordinate unit differences for beta*W automatically. The field-side beta norm argument pays that rerun and preserves the original saturated-leaf consumer. No coprimality of torus orders at different primes, no safe N+1 projection, no coordinate genericity and no faster long product are asserted.

The extension is a complete uniform factor-or-large-k-rough-order supplier within soft k bits. It strengthens order supply, while the completed long-query bound remains soft(J+sqrt(JL)). Exact reviewed bytes pass end to end.
