# Compact annihilator cover: an N-dependent quadratic lift with a paid residual criterion

24 October 2026. Scratch only; no repository edits, examples or backend work. This pass constructs and executes ONE candidate: smooth/cross-order projection followed by an N-dependent quadratic lift of the ordinary two-list interval cover. Both length-m power lists, all initialization and individual-difference localization cost soft m. Its exact coverage is proved below. The result is a restricted-family algorithm and a precise unresolved arithmetic condition, not a guaranteed all-semiprime cover or sixth-rate factorizer.

## Read scope and prior-credit boundary

The requested scratch `/tmp/semiprime-annihilator-cover-20261016/cover/group-gap-criterion.md` is absent. Read its preserved report at `/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-acquisition-checkpoint-20261016/reports/group-gap-criterion.md`, SHA256 `6fb196a7d87a81a53e1169810044fa5a946f85f683f79b25f2498e648929a5c9`, and its independent archived review. Also read `paid-cover-transfer.md`, `/tmp/semiprime-acquisition-resume-20261022/compact_cover/{report,smooth-menu-proof,three-full-status}.md`, and the recent native/character journal entries. Current journal bytes read were `675b7a75a1f250bd792ba96b5a07c2e3fe5deddfac74122a29da0968b605815d`, rather than the requested older `31536ff` prefix. No source was changed.

The inherited consumer already obtains a factor from PAID individually covering group differences without prefactoring the selected difference under its imported decoder premise. Here that interface is specialized to a projected base and a SHORT explicit gap, so no unverified long-annihilator premise is needed. Smooth projection, the two-rough-factor observation, sparse coindex CF covers, fixed-prime smooth menus, known modular difference covers and product-vs-individual coverage distinctions are prior results. The quadratic extension below is a classical Brent–Suyama type transformation. No absolute novelty is claimed. This pass's contribution is an exact N-aware candidate and joint residual/order ledger in this interface.

## Primary sources and applicability

Chris Umans and Siki Wang, *A number-theoretic conjecture implying faster algorithms for polynomial factorization and integer factorization*, arXiv:2511.10851v1, [primary HTML](https://arxiv.org/html/2511.10851v1), [primary PDF](https://arxiv.org/pdf/2511.10851v1). Definition 3.1 and Conjecture 3.3 concern individual divisor coverage by structured cross-differences; Theorem 5.5 additionally uses prefactored differences for their integer algorithm. Section 6 gives restricted easy classes, combines supplied AP covers, and identifies prime and two-large-factor cases as difficult. Section 7 permits short addition sequences in place of GAPs. None states a uniform soft-m constructor of this task's two lists. The candidate uses an explicit short addition sequence, without assuming their conjecture. Cached `sources/umans-wang-2025.pdf`, SHA256 `70160d59ac73d443f0c9dbd04246e1c35f824f7a6a40e602cd6fb5125cfa0be5`.

Paul Zimmermann, *20 years of ECM*, [primary author PDF](https://members.loria.fr/PZimmermann/papers/ecm.pdf), sections 3.4–3.5, describes polynomial transforms f(s),f(t) of stage-two index sets, finite-difference generation, and the two-modulus grid improvement. Such transforms preserve already covered primes and may add hits; the text makes no worst-case guarantee for every large order. Its stage-two smoothness/remaining-factor premise is not free here. We use only the explicit polynomial-difference mechanism and give the candidate's complete proof below, over the multiplicative group modulo unfactored N. Cached `sources/20-years-ecm.pdf`, SHA256 `79618c17b20775cedeeec0864570ca53060c1f831a29ec2a99253121fba3c2d5`.

A modular difference cover for a KNOWN cyclic modulus v covers residues modulo that supplied v. It does not select the unknown local order d, nor ensure nonzero integer differences with the required multiples when substituted blindly. The ordinary integer interval cover below avoids this issue by covering every integer in a public interval. No stronger constant from a combinatorial difference-cover construction changes its square-root scale.

## 1. Public scale, factored smooth projection and its kernel

Let N=PQ with distinct odd primes P<=Q, n=ceil(sqrt N), m=ceil(n^(1/3)), H=m². Use the supplied prepared beta with COPRIME ODD local orders d_P,d_Q>16H. This is the existing N-1-projected scalar controller, not an assertion that arbitrary gamma has coprime local orders. Its preparation is an imported paid interface. Form

    M=product_(prime ell<=m) ell^floor(log_ell N),
    gamma'=beta^M mod N.                          (1)

The prime-power cap is N, not n: it kills small-prime powers of BOTH local orders even for unbalanced Q. Sieve through m, acquire exact prime powers and their product tree, and binary-power gamma'. The explicit binary length of M is at most pi(m)*ceil(log2 N)+O(1)=soft m. All this costs soft m; factorization of M is supplied by its construction.

Compute gcd(gamma'-1,N). Proper gcd returns a factor. A saturated result must NOT invoke a short-annihilator decoder on beta,M: M has soft-m bits, not polylogarithmic bits. Instead use the following factored-exponent kernel tree, which returns a factor in soft m.

At a node keep a base x with coprime local orders both>1 and an acquired factored exponent K with x^K=1 globally. Split its prime-power factors into two parts K_L,K_R. Compute y=x^K_L and gcd(y-1,N). A proper gcd factors. If the gcd is N, recurse with x,K_L. If the gcd is 1, recurse with y,K_R. In that branch raising preserves coprimality, and the gcd certifies both new orders>1; also y^K_R=1 globally. At a leaf K is a single prime power, which cannot annihilate two coprime orders both>1. Thus a proper factor is reached before that impossible leaf. A balanced tree and its acquired integer products charge at most soft(bitlen M) exponentiation work along this ONE path. No original-base long-annihilator theorem is used.

On gcd=1 the two local orders of gamma' are

    r_P=d_P/gcd(d_P,M), r_Q=d_Q/gcd(d_Q,M),       (2)

both>1, odd and coprime. Every prime factor exceeds m. Coprimality here is inherited from beta and preserved by powering, not inferred from smoothness.

For clarity, the arithmetic reason for the prepared cross-order separation is: if an original unit has local-order valuations bounded by x=v_ell(P-1), y=v_ell(Q-1), then v_ell(N-1)>=min(x,y). Raising to N-1 therefore removes ell from at least one local order. This explains the N-aware setup; it does not rerun or alter the imported controller's own kernel branches.

### One paid order screen before any short decoder

Run the inherited universal monic separator on gamma' with cap 16H. It costs soft sqrt(16H)=soft m and returns a factor, an EXACT common local order, or NoHit. Its first nonunit row and larger-baby-index-first descent inspect positive exponents in increasing order; this ordering is essential to the exact-common-order conclusion. NoHit certifies BOTH local orders>16H, even if only one would have been small. Since the present two orders are coprime and>1, an exact-common-order output is impossible. Hence the screen returns a factor or supplies the desired large-order gamma' branch.

This screen is deliberately not an arbitrary unordered cross-product descent: a saturated arbitrary exponent could be a common MULTIPLE of distinct coprime orders. Only the ordered separator just cited certifies a common EXACT order.

The precise supplied short decoder is `docs/research-evidence/semiprime-unbalanced-annihilator-20261016/reports/unbalanced-extractor.md`, SHA256 `a7765a14e4d0bc82339229f5f3bb445ad8f1f95bd22c49d631259d4e039195be`. It accepts ANY nonzero explicit polylog-bit global annihilator of a unit whose two local orders are odd and>16m², without a balance or coprimality assumption, and factors in soft N^(31/192), hence soft m. Its analytic/finite-input qualifications are inherited. We use it only AFTER this NoHit guard and only on a short gap below.

For the smaller prime, r_P<=P-1<n<=m³. Since its prime factors exceed m, it has at most two counted with multiplicity. This observation was already in the older smooth-projection report; no new universal coverage follows from it.

## 2. Two actual length-m exponent lists

If N<=2m², trial division through sqrt N costs O(m) elementary trials and finishes within the stated budget. Otherwise N>2m². Set

    f_N(x)=x*(N-x),
    S={ f_N(m*b): 1<=b<=m },
    T={ f_N(a): 0<=a<m }.                       (3)

Both lists have exactly m labeled entries, each with O(log N) bits; even explicit exponent storage fits soft m. The recurrence below also avoids individually powering all entries. The function is strictly increasing on [0,m²], since N>2m²; hence every s in S exceeds every t in T as an INTEGER. In particular no group collision can be the useless zero integer exponent gap.

Acquire all residues gamma'^s and gamma'^t by two concrete multiplicative second-difference recurrences. For h in {1,m}, let z_b=gamma'^f_N(hb). Then

    z_0=1,
    z_1=gamma'^(h*N-h²),
    R_b=z_(b+1)/z_b=gamma'^(h*N-h²*(2b+1)),
    R_(b+1)=R_b*gamma'^(-2h²),  z_(b+1)=z_b*R_b.    (4)

All inversions in this initialization are of gamma', a known unit. Acquire z_1 and gamma'^(-2h²) by O(log N)-bit exponentiation, then iterate O(m) modular multiplications. The h=1 sequence supplies T; the h=m sequence supplies S. All initialization and enumeration cost soft m, storing only residues and O(log m)-bit ordinals.

The exact cross-difference is

    Delta=s_b-t_a=(m*b-a)*(N-m*b-a)>0.                 (5)

It has O(log N) binary length, and a selected pair's difference is recovered by a constant number of exact integer multiplications using its two labels. Relative to the original beta, the corresponding exponent would be M*Delta, which has soft-m bits; the algorithm does NOT send that exponent to the short decoder. Individual coverage means divisibility of THIS complete integer product by a local order; no inference from a product over different pairs is used.

## 3. Exact coverage of this candidate

Since gamma' has local order r_p, (3) contains an individual group collision at p EXACTLY when

    exists b in [1,m], a in [0,m-1]:
    r_p | (m*b-a)*(N-m*b-a).                      (C_N)

This equivalence is a proof, not an algorithm receiving r_p. The lists and their consumer never inspect a hidden residual.

The first factor u=m*b-a enumerates every integer in [1,m²] once. Thus if either r_P or r_Q<=m², choose u=r_p and (C_N) holds automatically. This is the ordinary interval-cover guarantee, not a new coverage theorem. In the complete guarded algorithm the preceding 16H screen already finishes every such case (and more), so the quadratic pass is used only on larger residuals.

The second factor enlarges the explicitly characterized covered family of the quadratic lists; no assertion that this family contains every input is made. The sum v=m*b+a enumerates every integer in [m,m²+m-1] once. If r_p divides N-v for any such v, the corresponding SAME pair satisfies (C_N), regardless of u. Equivalently a multiple of r_p lies in

    [N-m²-m+1, N-m].                              (6)

For a PRIME residual r_p>m², u is nonzero and less than r_p. Hence this additional condition (6) is also NECESSARY for the quadratic candidate to cover that residual. For composite residuals the full exact predicate (C_N) additionally permits splitting different prime-power factors between u and N-v; it is stronger than requiring one factor alone to be divisible by the whole residual. This splitting takes place INSIDE ONE integer difference, so it is lawful individual coverage.

The known arithmetic N=PQ makes (6), at the smaller factor, equivalent to r_P dividing Q-v because r_P divides P-1. That is an N-aware improvement over the unshifted interval cover, but it is not automatically true. Neither coprimality of r_P,r_Q nor r_P*r_Q<=N proves that Q (or P at the other factor) has one of these short residues.

## 4. The consumer, localization and actual bit ledger

Form the monic polynomial H(X)=product_(t in T)(X-gamma'^t), evaluate at the m acquired S residues, and scan gcds with N. Monic product/remainder trees work over Z/N even with repeated residues and nonunit differences; total work is soft m. A proper gcd returns a factor. If a row gcd saturates, descend the retained T product tree at that fixed S residue, taking gcds at children. The decreasing degree sum is O(m), and a saturated leaf gives gamma'^Delta=1 modulo N.

Recover the exact positive Delta from (5), with O(log N) bits: Delta<=m²*N. The already guarded gamma' has odd local orders both>16H, and the saturated leaf supplies a GLOBAL annihilator, so call the precisely pinned SHORT decoder once on gamma',Delta. All its hypotheses are now paid/supplied. A merely local collision never supplies this decoder input: it returns a proper gcd instead, or is localized further. No prefactoring of Delta, decoder call on beta,M*Delta, local-order input, individual large-exponent powering per list entry or V*D materialization is used.

If all row gcds are 1, (C_N) is false for both actual residuals, and this candidate returns “no covered pair.” This is an honest initialized outcome, not a factor or an all-input success claim. The algorithm does not keep performing optional family expansions after that outcome.

| Operation | Actual work |
|---|---:|
| Sieve, factored M and gamma'=beta^M | soft m |
| gcd(gamma'-1,N), factored-M kernel tree if saturated | soft m |
| One ordered universal separator / NoHit guard | soft m |
| Two second-difference initializations/enumerations | soft m |
| Monic cross-evaluation and one-leaf localization | soft m |
| Recover one positive Delta, O(log N) actual bits | polylog N |
| Pinned short decoder on guarded gamma',Delta | soft N^(31/192), hence soft m |

This is a short-addition-sequence input to the general paid consumer, not an assertion that a quadratic list is a constant-rank GAP with small box volume.

## 5. Exact remaining arithmetic task and relation to prior deficits

After the paid NoHit guard, the surviving branch has both r_P,r_Q>16m², coprime, and with every prime factor >m. The smaller r_P<=m³ is a prime or a product of two such prime factors (possibly equal). In its PRIME case, P=1+c*r_P with 1<=c<m/16. The missing statement for THIS candidate would be that at least one of the two residuals satisfies (C_N), or in the prime case the concrete short-residue condition (6). No proof of this statement is obtained; it is not asserted as a new conjecture or as true. The equality N=(1+c*r_P)Q retains an unknown small c and an unknown quotient Q; replacing it by N modulo r_P still leaves the uncontrolled Q residue. The candidate does not acquire either unknown merely because c<m.

For the two-rough-factor case, separate divisibility of factors at different pairs would not suffice. The algebra in (5) permits a legitimate within-pair split, but no theorem forces compatible b,a for both factors. Enumerating a quadratic closure of unrelated pair gaps would restore the larger unpaid lists recorded in the old report.

UW's universal Strong Divisor Conjecture would be more than is needed, but it is not used to finish this N-specific condition. Known fixed-modulus difference covers do not supply the missing r_p or justify treating modular-zero integer differences as positive annihilators. Smooth/rough decomposition and Brent–Suyama's additional factors explain exactly which extra orders are covered, without converting an expected-success improvement into deterministic coverage.

Delivered: two explicit O(m)-size lists with a paid power-generation algorithm, strict positive-gap proof, exact individual divisibility criterion, an N-aware coprime residual reduction and a complete covered-branch consumer. No every-input guarantee for these lists is proved. The all-semiprime compact-cover construction and sixth-rate composition therefore remain open; no generic obstruction or lower bound is claimed.
