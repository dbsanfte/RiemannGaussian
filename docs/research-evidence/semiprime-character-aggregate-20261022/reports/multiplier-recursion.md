# Exact multiplier-two recursion and acquisition ledger

22 October 2026. Symbolic investigation of the actual scalar mask; no repository changes, code, tests or rate claim.

Let m be odd, Q=q^m, R_e={0} union residues of sign e, d0=(m+1)/2, D=K d0. Define H_e(X;q,K)=product_(r in R_e,n<K)(X-q^(r+mn)). Multiplication r'=2r modulo m maps R_e bijectively to R_e', e'=Legendre(2,m)e. Its carry c=floor(2r/m) is exactly 0 for even r' and 1 for odd r'.

Set

    A(X)=H_e(X;q²,K),
    B(X)=Q^D H_e(X/Q;q²,K),
    L(X)=product_(odd r' in R_e')(X-q^r'),
    U(X)=product_(odd r' in R_e')(X-q^(r'+2mK)).

For carry zero, A and B together supply n'=0,...,2K-1. For carry one, they supply n'=1,...,2K. Consequently the exact polynomial identity is

    L(X) A(X) B(X)=U(X) H_e'(X;q,2K).       (1)

Both endpoint polynomials have degree O(m); their construction and all J requested values cost soft O(m+J) by product trees/MPE. Thus the q^(2mK) wrap is retained and paid, not discarded as a residue permutation. Nonunit endpoints are localized to original scalar leaves with their public exponent ledger; integer-zero ledgers require symbolic cancellation or the existing finite handling. An odd final K is reduced to even K-1 plus one degree-d0 block, also paid at a fixed level.

The source-squaring identity is

    H_e(X;q,K) H_e(-X;q,K)
      =(-1)^D H_e(X²;q²,K).                    (2)

This is exact for both palettes, with the trivial r=0 channel included. If x and every seed belong to a common odd-order subgroup, H_e(-x) is a unit: x+seed cannot vanish in odd characteristic. This proves zero-mask equivalence in (2), not free acquisition of that whole companion product at J targets.

## A coherent interpretation needs square roots or changed source

At a parent target Y, (1) asks for A(Y) and B(Y), namely two queries of length K at targets Y and Y/Q with base q². Equation (2) converts these to a query with base q at square roots x²=Y and (x/t)²=Y/Q, where t²=Q. Unknown odd group orders do not by themselves provide a public half-exponent or a square-root algorithm. One can make a SINGLE initial step coherent by squaring the prepared source: if q=beta^(2m²) and Y=x², take t=beta^(m³). This preserves own-tag collisions and bounds the recovered annihilator by its explicit factor two. It is not a license to take successively many roots of beta. At depth h, this direction requires initial source exponents divisible by 2^h. Such an initial powering has only O(h) extra exponent bits and is affordable, but it must be chosen and all annihilator multipliers recorded.

## Literal recursion cost, even granting all coherent roots

One parent produces two positive-channel children, x and x/t. Minus channels may be dropped for zero detection on the certified odd-order subgroup; for actual VALUES they must instead be acquired, and their units cannot be treated as known scalars. Suppose h squaring levels are prepaid in the initial source and only zero detection is sought. At depth h the two choices at each level give the complete set of 2^h shifted target origins for each original target, with corresponding shorter index blocks. They are the usual dyadic partition of the original long interval: the multiplier carry reassigns residue classes but does not merge these origin states.

Thus the direct recursive algorithm has up to J*2^h target requests at depth h, while K shrinks by 2^h. Batch MPE for each level's endpoint blocks costs at least its explicit O(J*2^h) output volume if those requests are materialized. At leaves K=O(1), this gives J*K_initial requests, about m² for native J,K~m. Any deduplication or implicit joint action reducing that count must be proved for the actual carried target exponents; it does not follow from having only O(m) residue/carry descriptors. This is the work ledger of the displayed recursion, not a lower bound against another evaluator or compressed state representation.

Equation (1) by itself, without converting via square roots, has the same two-child branching on targets Y and Y/Q at successively squared bases. The resulting shifts encode the same dyadic origin choices. A classical Mahler-style identity has therefore been obtained, but the literal evaluation tree does not achieve soft O(m).

## Remaining constructive target

The new exact acquired object is the multiplier-two carry equation (1), with all endpoints and the true q retained. A useful algorithm must compress its dyadic origin requests AND acquire any value-level minus companions or avoid them through a rigorously factor-only controller. No such whole-family compression was found here. Native lifted-root congruences and antipodal pairing do not currently supply the missing identification of these origin states. No improved acquisition bound is claimed.

## Amendment: paid coherent roots and reviewed all-level ledger

The later `coherent-root-preparation.md` supplies the fully paid repair for ORIGINAL input chains: initially set gamma=gamma0^(2^D), D=ceil(log2(8m)). All original target and step roots through depth D are explicitly acquired in soft O(m), and odd local orders are unchanged. The SAME recovered nonzero K annihilates gamma0 because its local odd orders divide 2^D K iff they divide K; no exponent-bit expansion is necessary. Thus lack of a hidden-order root oracle is not a remaining barrier for those original chains. This amendment supersedes any reading of the earlier root caveat as an unpaid original-input preparation step. It does not acquire the branching shifted-origin query products.

The independent `review-native-multiplier.md` pays the full literal tree: at level h let b=2^h and K_h<=ceil(K_initial/b). There are at most Jb materialized requests and only O(1) length types. All endpoint and odd-final-block polynomials have O(m) total degree per length type; batched MPE costs soft O(m+Jb). Summing to depth ceil(log2(max(1,K_initial))) costs

    soft O(m log(K_initial+1)+J K_initial),

including terminal values. For J,K_initial~m this is soft O(m²), not soft O(m). This is the cost of the displayed explicit tree, not a lower bound against another representation.

The same review gives a uniform INTEGER recovery ledger in the retained native regime L<=4m², N>256m⁴. A depth-h target is gamma^(e_j-Mt), 0<=t<b; its upper correction leaf with base q^b has original scalar index

    I'=kappa_j+m t+b r+2m b K_h, 0<=r<m.

With b<=2K_initial and bK_h<=K_initial+b, it obeys I'<m+10mK_initial<=m+40m²<=41m². Lower and last-block endpoints obey the same bound. Since E_j>N-3m²>41m⁴, every leaf ledger E_j-m² I' is strictly positive and has O(log N) bits. A proper endpoint gcd factors immediately; a saturated product is localized through its monic O(m)-degree root tree, with one geometric-degree-sum O(m) localization path. The controller stops after this first useful correction, so this adds soft O(m), not one new path per tree node. Outside the explicit large native regime, preserve the earlier public nonzero-ledger check and finite handling.

These reviewed amendments preserve the report's history. Neither complete twist-fibre norm compression nor coherent roots identify the actual shifted-origin states, and no soft-m H evaluator is claimed.
