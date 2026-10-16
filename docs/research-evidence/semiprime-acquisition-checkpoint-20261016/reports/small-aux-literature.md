# Small auxiliary residue acquisition: primary-source review and constructive reductions

Date: 2026-10-16. Scope: research only, no repository edits, commits, broad gates or new Lean declarations. Read the repository AGENTS instructions and the supplied sparse-residue derivation. No all-input acquisition theorem was obtained.

## What the literature actually supplies

1. Coppersmith–Howgrave-Graham–Nagaraj, *Divisors in residue classes, constructively*, Math. Comp. 77 (2008), 531–545. Primary publisher PDF: https://www.ams.org/journals/mcom/2008-77-261/S0025-5718-07-02007-8/S0025-5718-07-02007-8.pdf . Author-uploaded paper: https://www.researchgate.net/publication/220333750_Divisors_in_Residue_Classes_Constructively . Given r,s,N with gcd(r,s)=1 and s>=N^alpha for fixed alpha>1/4, they explicitly recover all divisors in that class in polynomial time, and bound their number by O((alpha-1/4)^(-3/2)). This is a residue consumer. Enumerating unknown input classes is still charged. It gives no method to discover the class.

2. Hales, *Divisors in Residue Classes Revisited*, arXiv:2410.05030v1, https://arxiv.org/html/2410.05030 . Theorem 1.1 gives the analogous prescribed-class algorithm in Q(sqrt(-d)), d=1,2,3,7,11, when |S|^3>|N|, with O(log|N|) elementary ring operations. The polynomial version requires monic data (or factorization of the leading coefficient); this condition is essential, explicitly preventing the degree-zero integer-factoring shortcut. Ring extension therefore does not generate a missing rational factor residue. This is a genuine extension of a consumer, with its class still an input.

3. Hittmeir, *Integer Factorization as Subset-Sum Problem*, arXiv:2205.10074v1, https://arxiv.org/html/2205.10074 . Algorithm 2.1 / Proposition 2.2 enumerate a CRT product of explicit local sets in output-linear bit time up to log factors. Lemma 3.4 gives the local image of x -> kx+N/x modulo an odd prime r cardinality (r+chi(k^(-1)N))/2. Theorem 3.5 describes prime-power lifting; Theorem 3.7 bounds the CRT image by O(m log B/2^omega(m)) for m the product of primes <=B. These are valid public catalogs for linear forms in the factors. They do not identify which element is the actual factor sum, or restrict the first coordinate x of the hyperbola. The paper's deterministic application is a subexponential improvement of Fermat factoring for small factor difference.

4. Stanica–Mulder–Hittmeir, *Multi-target hyperbolic sieves and elliptic trace obstructions*, arXiv:2606.13018, https://arxiv.org/html/2606.13018 . Theorem 5.1 gives union size r(1-2^(-k))+O_k(sqrt(r)) for k distinct linear-form coefficients. Proposition 6.1 constructs the union in O(kr) field operations. The restricted power-residue image in Corollary 5.7 has size <=(r-1)/d, but its coverage assumption is N=u^d v, with the sought coordinate u^d; this is not automatic for squarefree semiprimes. The authors explicitly do not establish a faster factoring algorithm. The elliptic traces in this paper count curves over the **known auxiliary prime** and compute local image cardinalities; they do not compute traces over unknown factor fields or discover P mod r.

5. Bach–Shallit, *Factoring with Cyclotomic Polynomials*, Math. Comp. 52 (1989), 201–219, https://www.ams.org/journals/mcom/1989-52-185/S0025-5718-1989-0947467-1/S0025-5718-1989-0947467-1.pdf . The cyclotomic factoring construction takes a multiple of Phi_k(P) as its exponent input, generalizing p-1 and p+1 methods; the displayed Cyclo algorithm includes random ring elements. It is not a deterministic all-input method to acquire such a multiple, nor a method to recover the Frobenius class of P from the public product N. Raising a primitive r^2-th root to the public exponent N directly gives only the public action N mod r^2, not either component Frobenius.

6. Dabrowski–Pomykala–Shparlinski, *On oracle factoring of integers*, https://arxiv.org/html/1912.00345 . Definition 1.1 explicitly assumes an oracle returning bounded positive multiples of prescribed elliptic point-count products; Algorithm 3.1 then uses elliptic scalar multiplication and gcds. The theorem concerns almost all inputs, allowing an exceptional set. It neither implements the oracle nor supplies an every-semiprime catalog. A point count over an unknown factor field cannot be replaced by Schoof over the known auxiliary prime.

7. Harvey–Hittmeir, *Deterministic methods for finding elements of large multiplicative order*, https://arxiv.org/html/2601.11131 . Theorem 1.1 returns an element of global order >D or a factor, with bit bound O(D^(1/2) log D log N / sqrt(log log D)), for every 1<=D<N-1. This removes a small-D restriction in prior order setup. Its output is global order information, not a residue of P, and the task already pays stronger local setup.

The known GFHP source https://arxiv.org/html/2512.19076v1 Algorithm 5.1 likewise **inputs** a class P=r mod n. Nothing found in its acquisition/setup algorithms supplies the missing class.

## Positive reduction A: a factor-sum catalog modulo r^2 is enough, including singular cases

Let r be an odd prime, gcd(N,r)=1, n=r^2. Suppose an explicitly acquired set T of K residues modulo n contains P+Q modulo n. Define

    S = union over t in T of { x modulo n : x^2 - t*x + N = 0 modulo n }.

Then P mod n and Q mod n belong to S, and

    |S| <= 2 K + 2 r.

Proof: multiply the quadratic by 4 and put y=2x-t. A t for which D=t^2-4N is nonzero modulo r has at most two square roots, each lifting uniquely to r^2. If r divides D but r^2 does not, there are no roots. If r^2 divides D, y is one of r multiples of r. There are at most two such t modulo r^2 because t^2=4N has at most two roots (both simple modulo r). Thus only at most two catalog entries produce r-root fibers. This proves the bound without assuming P!=Q mod r.

Construct S deterministically in soft O(r+K+|S|) bit work: precompute all square roots modulo r by a single O(r) scan; for each nonsingular D lift its roots via one linear correction; for D=0 mod r^2 enumerate r multiples. Deduplicate explicitly if desired. All arithmetic uses O(log N)-bit values. No factorization of N is involved. For r~N^(1/18), any acquired K=soft O(r) sum catalog therefore gives J=soft O(r), n~N^(1/9), exactly the desired density and total consumer bound.

The familiar hyperbolic sum image modulo r^2 has about r^2/2 entries, so it does not meet K=soft O(r). The remaining step is a stronger **acquired** sum catalog, not quadratic root finding.

## Positive reduction B: two linear-form catalogs avoid all singular fibers at any r-power

Let n=r^k for fixed k>=1 and r odd. Suppose explicit T_1,T_2 contain P+Q and 2P+Q modulo n, respectively. For each a in {1,2}, t in T_a, solve

    a*x^2 - t*x + N = 0 modulo n

but retain only roots with 2a*x-t != 0 modulo r. Then the union S has

    |S| <= 2(|T_1|+|T_2|),

and contains P modulo n. Indeed at x=P the two derivatives are P-Q and 2P-Q; both cannot vanish because r does not divide P. Hence at least one correct target has a simple root. Every simple root has a unique Hensel lift, and each quadratic has at most two roots modulo r. A root table modulo r followed by k fixed lift steps costs soft O(r+|T_1|+|T_2|+|S|). This is an elementary but useful acquisition adapter; the two target lists must themselves be acquired. Applying it to full hyperbolic images supplies no density gain.

## Minimal precise acquisition target

At r~N^(1/18), even a **single known value phi(N) mod r** would suffice: t=N+1-phi(N) mod r gives P+Q mod r, and the quadratic x^2-tx+N yields at most two factor residues modulo r after an O(r) deterministic root-table scan. Then n=r, J<=2, J/n=O(N^(-1/18)), so the supplied consumer is soft O(N^(1/6)). No cited source computes phi(N) mod r within soft O(r^3) on every semiprime. This statement is a clean sufficient acquisition problem; it is not claimed easier than factoring.

A bounded union of Fermat-quotient classes, a bounded-degree equation known to vanish at a hidden factor residue, a sparse sum catalog as in A, or a small value menu for the two linear forms as in B would all suffice. Every route checked still leaves its hidden-factor-dependent datum as an input or oracle. Public exponentiation, CRT construction and modular root finding at r, r^2 and r^3 are inexpensive enough; none of the inspected primary theorems deterministically supplies the needed datum for every squarefree semiprime.

## Local verification of the two constructive adapters

`check_reductions.py` implements the square-root lifting algorithm and simple-root two-form algorithm. It compares all quadratic fibers modulo r^2 for r=3,5,7,11 and all N units against direct enumeration: 15,922 fibers passed. It also checks 69,780 unit-pair cases for r^k, k=1,2,3 (exhaustive when the unit group has <=150 elements, fixed endpoint samples otherwise): correct factor residue retained and at most four output roots. Output: `{'square_fiber_cases': 15922, 'two_linear_form_cases': 69780, 'status': 'PASS'}`. The verification uses factor residues only to test coverage, never as acquisition input to a claimed factoring procedure. It verifies the arithmetic adapter, not the unavailable catalog acquisition or the entire bit bound.

## Correction to the follow-up Umans–Wang interface suggestion

The earlier message suggesting that the current annihilator extractor might remove Umans–Wang's Prefactored condition conflated two frameworks. Rechecked primary Sections 5.1–5.2, https://arxiv.org/html/2511.10851 : Equation (2) sets A_i=s_j-t_l as an **integer difference**. Theorem 5.2 recursively computes gcds of interval products of these integers with N; at a leaf it returns (A_i,gcd(A_i,d)). Its separate Property 3 factors A_i. Lemmas 5.3–5.4 supply interval products, and Theorem 5.5 invokes the **Strong Prefactored** conjecture to supply Property 3. A saturated integer leaf says N divides s-t. It does not say that any group element raised to s-t is one modulo N. There is no direct annihilator substitution or established removal of the prefactorization requirement.

A different, explicitly adapted group-order scheme could cover ord_P(beta)<=sqrt(N) using differences s-t, then batch beta^s-beta^t. A saturated group collision, unlike UW's integer collision, supplies the nonzero annihilator K=s-t. This would be a separate derived reduction requiring its own exponent-array construction, coverage and saturation proof; it is not the published Theorem 5.5.

The root's current long-exponent extraction bound is approximately

    soft O(N^(31/192) + L*N^(5/48)),

where L is the bit length of K. This fits soft O(N^(1/6)) only for L<=soft O(N^(1/16)). No soft O(w+L) theorem is available. At UW's target alpha=beta=1/3 and n~sqrt(N), the differences can have L~N^(1/6), exceeding that present allowance. My earlier suggestion must therefore not be used to claim automatic prefactorization removal, an additive-linear long-input bound, or a target-exponent algorithm.
