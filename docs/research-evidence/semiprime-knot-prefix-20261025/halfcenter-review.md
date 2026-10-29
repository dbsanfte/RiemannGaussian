# Independent review: native half-center fold and scalar prefix identity

2026-10-25. **PASS, scoped to the appended half-center construction and costs.** Read `row-cancellation.md` and the pinned `/tmp/semiprime-native-family-sharing-20261024/deletion-and-grouping.md`. No repo edits, source search, or new exponent claim. The review supplies an additional exact one-point scalar identity below.

## Native bookkeeping and paid exceptional class

The pinned hard-branch proof uses N>256k^4 and k>16. It excludes public deletion for b!=0, and identifies exactly the two deleted horizontal rows (k,0,H-k),(-k,0,k), plus the two swapped partners discarded by complete-swap pruning. Each of those sets is opposite-closed under (a,b,lambda)->(-a,-b,H-lambda). Complete diagonal deletion also commutes with that involution. Thus the actual remaining nonzero-lambda rows split into label pairs, including when their ring values coincide. There is no need to assume inverse closure at center zero.

For lambda=0, 3^(2e)|ab follows from the root equation and gcd(N,3)=1. For k=2*3^e>16, one has k<3^(2e), so a nonzero product |ab|<k is impossible. Only the four axes remain possible, giving at most four rows/two inverse pairs. These are an actually constant-size class, not O(k) rows.

Its length-M nonunit aggregate can be evaluated and localized at soft O(sqrt M), since its degree is constant and the existing monic geometric evaluator and original consumer apply. This is soft O(k^(3/4)) ring work before the licensed extractor; extractor/controller overhead remains within soft O(k). If this aggregate is unit, every shorter contribution from the class is unit. Discarding it from subsequent zero predicates is therefore valid. Merely OR-ing two separate zero-only answers would be invalid, and the report correctly avoids that.

## Half-center factor and monic modulus

For a retained nonzero-lambda pair x,y=q/x, central screening makes x-1 and y-1 units. Since y-1=(q-x)/x and x is a unit, x-q is also a unit. Put

    W=x+q/x,  W_s=q^-s+q^(s+1).

Then (x-q^-s)(x-q^(s+1))=x(W-W_s), so

    B_pair(m)=x^m prod_(s=1..m)(W-W_s)

is an exact raw-product identity. The multiplier x^m is a unit. Moreover

    W-(1+q)=(x-1)(x-q)/x

is a certified unit. Thus G_half(1+q) is unit. The acquired monic G_half has exactly J_nonzero/2 factors if repetitions are retained, and degree at most that after removing duplicate W values. A product tree acquires it in soft O(J). The report's factor-two claim applies to the actual opposite-closed nonzero-lambda list, not arbitrary center-zero traces.

The recentering eta=beta^(H/2), eta²=q, requires no root extraction. It gives W/eta=(x/eta)+(x/eta)^-1 and the stated half-shifted clock. Its powers cost polylogarithmic work per supplied exponent; acquiring all row W values is soft O(J).

## New exact one-point and full-prefix identities

Define the normalized half-center Laurent polynomial

    D_half(t)=G_half(t+q/t)/G_half(1+q).

For any unit t, direct factorization gives the exact identity over R:

    D_half(t)=prod_pairs
       (x-t)(x-q/t)/[(x-1)(x-q)].                         (1)

No extra scalar t-power or sign is missing. In particular

    D_half(q/t)=D_half(t),    D_half(1)=D_half(q)=1.

Let Delta_nonzero denote the original Delta with the screened lambda=0 class removed. Its pair factor satisfies

    delta_x(t)delta_(q/x)(t)
       =D_pair_half(t)D_pair_half(t^-1).

Multiplying the pairs gives

    Delta_nonzero(t)=D_half(t)D_half(t^-1)
                   =D_half(t)D_half(qt).                (2)

Thus, for m>=1, its exact scalar prefix is

    A_m_nonzero=D_half(q^(m+1))
                   *prod_(i=2..m) D_half(q^i)^2.         (3)

Empty products are 1. Define the deduplicated normalized half prefix

    K_m=prod_(i=2..m+1) D_half(q^i),    K_0=1.

Then the exact alternative form is

    A_m_nonzero=K_(m-1)^2*D_half(q^(m+1)).                (4)

The raw folded pair product normalized by [(x-1)(x-q)]^m gives K_m, because D_half(q^-s)=D_half(q^(s+1)). Consequently K_m is a genuine m-term one-point prefix of a single acquired Laurent polynomial, but shifted to start at q². The already-normalized factor D_half(q)=1 permits starting instead at q if preferred, with endpoint m+1.

**Critical distinction:** K_m is not generally equal to the original A_m_nonzero. Equations (3),(4) retain the original interior multiplicities. Removing them preserves nonunitness over any commutative ring, and preserves exact zero modulo squarefree N=PQ by support at each prime. For repeated-prime moduli the zero equivalence can fail. The report makes the squarefree condition explicit.

The lambda=0 class contributes a unit on the continuing branch, so the full original prefix has the same zero/nonunit predicates as A_m_nonzero and K_m. This does not identify their full scalar values.

## Recovery labels and costs

A first-zero index found using the transformed K_m predicate is the same first-zero index as the original prefix. The previous nonzero original prefix, multiplied by its new original Delta(q^m), proves that new factor is nonunit, even if the earlier prefix is a zero divisor. Scan the original rows at q^m and q^-m as in the established consumer.

If one instead localizes the new half-center endpoints, x=q^-m is already an original negative leaf. The other endpoint x=q^(m+1) maps through its actual opposite y=q/x to y=q^-m. This mapping is essential at m=M: it returns to an original row and index -M, rather than inventing an unlicensed M+1 leaf/exponent. Mixed CRT signs remain separated by the original signed scan.

The full folded query still costs soft O(J+sqrt(Jm)) with the established evaluator. The half degree, the shift from 1..m to 2..m+1, and multiplicity removal change constant factors only. m+1 stays below the local-order bound. Computing scalar q-factorial normalization in soft O(sqrt m) does not compute the aggregate at all W_pair. The appended construction therefore makes no exponent advance, consistently with its conclusion.

## Hypergeometric formulas checked algebraically

Formula (5) is correct: each half factor is -q^-s(1-Wq^s+q^(2s+1)); the latter is (1-xq^s)(1-q^(s+1)/x). At W=1+q the denominator becomes exactly (q;q)_m(q²;q)_m. The finite subtraction formula follows by subtracting (1-q^m)(1-q^(m+1)) from that numerator. Splitting even/odd q-factors gives formula (7) with denominator (q,q²,q²,q³;q²)_n. These are exact scalar normalizations, not a paid acquisition of the large whole-family coefficient. The stated q-Euler formula (6) has the correct transformed upper parameters q/x,x and argument qz; its prefactor ratio is (qz;q)_infinity/(z;q)_infinity=1/(1-z) in its formal domain.

No genuine algebraic, deletion, unit, recovery, or cost gap found in the appended positive half-center section. The new identities (1)–(4) give its exact scalar relationship to the original prefix while preserving the distinction between raw-support contraction and full-value computation.

## Follow-up review: ordinary Alexander polynomial at half the row rank

The root's proposed recentering also passes algebraic/unit/consumer review under the native assumption that ord_p(beta) is odd at both primes.

Let eta=beta^(H/2), so eta²=q. Oddness gives ord_p(eta)=ord_p(q): dividing H by two changes no gcd with the odd beta-order. Screen x-eta for each opposite pair. A proper gcd factors; a saturated equality gives beta^(E-H/2)=1 with a nonzero licensed-size exponent, except when the known integer E equals H/2.

That exact-integer exception can only be on the horizontal axes, because the pinned hard-branch proof gives |E|>HM for b!=0. The two horizontal rows with lambda=H/2-a are each other's opposites and both have x=eta. Every one of their original signed clock differences is unit:

    eta-q^i=eta*(1-eta^(2i-1)),
    eta-q^-i=eta*(1-eta^(-2i-1)).

For |i|<=M, all relevant exponents are nonzero odd integers of absolute value at most 2M+1<ord_p(eta), including the central difference. Their normalized original row contributions are therefore units at every prefix. Removing only these opposite-pair rows preserves every original zero/nonunit prefix predicate. There is no need to remove their vertical swap partners. The resulting list need not remain swap-closed, but the stronger pointwise predicate preservation carries the already proved final-zero promise; do not reapply an old closure-dependent counting theorem to that newly pruned list without checking it.

On the continuing screened branch v=x/eta and v-1 are units. Put

    R(Z)=prod_remaining_pairs(Z-v-v^-1),
    K(T)=R(T+T^-1)/R(2).

R(2) is unit by the v-1 screen, so K is an ordinary reciprocal Alexander polynomial normalized at 1. If L denotes the number of remaining pairs, its sparse Seifert matrix has dimension 2L, whereas the original unfurled construction had dimension 2J. All new coefficients, screens, and sparse entries are acquired in soft O(J), with the existing small-entry lift construction.

The old half-center polynomial for the remaining list satisfies

    G_half(W)=eta^L*R(W/eta),
    D_half(t)=R(t/eta+eta/t)/R(eta+eta^-1).

The denominator R(eta+eta^-1) is unit because G_half(1+q) is unit. Hence

    K(t/eta)=c*D_half(t),
    c=R(eta+eta^-1)/R(2) is a known unit.

Thus the old deduplicated prefix K_m (notation of the earlier part of this review) differs by the unit c^-m from

    prod_(i=2..m+1) K(eta^(2i-1)).

Its zero and nonunit predicates are exactly preserved; original signed-label recovery is unchanged. This is a genuine ordinary-Alexander rank reduction of the acquired presentation. It does not compute the long odd-stride prefix, whose desired fast decision remains unpaid.

## Final simplification: negative-only polynomial prefix and one-sided recovery

**PASS.** For the remaining opposite-closed nonzero-lambda pairs, define the ordinary point polynomial (distinct from the Seifert block named F elsewhere)

    F_point(t)=t^L*G_half(t+q/t)
              =prod_pairs(t-x)(t-q/x).

It is monic of degree 2L, with constant term q^L a unit, and F_point(1)=G_half(1+q) is a certified unit. In fact it is exactly the original point polynomial for all remaining rows. No reciprocal Laurent coefficient conversion or additional knot input is needed to acquire it; product trees cost soft O(J).

The half-center symmetry gives D_half(q^(i+1))=D_half(q^-i). Therefore the deduplicated half prefix is exactly

    K_m=prod_(i=1..m) D_half(q^-i)
       =q^(L*m*(m+1)/2) / F_point(1)^m
             *prod_(i=1..m) F_point(q^-i).              (5)

The prefactor is a known unit and can be ignored for both zero and nonunit predicates. Combined with the earlier squarefree multiplicity-removal proof and the unit lambda=0 screen, the original complete prefix is zero iff this negative-only polynomial prefix is zero. Nonunit equivalence needs no squarefree assumption, while the original-to-deduplicated exact-zero equivalence does.

Binary-search the first zero of

    Z_m=prod_(i=1..m) F_point(q^-i),    Z_0=1.

Its preceding prefix is nonzero (possibly a zero divisor). Since a unit cannot send a nonzero element to zero, F_point(q^-m) is nonunit. Factorization of F_point then guarantees a nonunit leaf in the **single** scan

    gcd(x_j-q^-m,N)

over every remaining original row. Proper gcds factor; a saturated leaf gives beta^(E_j+Hm)=1 with a nonzero integer exponent by the original whole-row zero-deletion rule. No new endpoint m+1 exponent, opposite-row relabeling, or two-sign scan is necessary at this final stage. The row list itself already contains the needed opposites, so mixed CRT signs in the earlier formulation are represented by different retained rows in this one-sided scan.

The full negative-only prefix is known to be zero by the established predicate equivalence and A_M=0. Directly, the surviving native coverage index I cannot be 0 on a continuing centrally screened branch. It also cannot be 1 in the nonzero-lambda opposite-closed list, because its opposite has index 1-I=0 and would trigger that same central screen. A negative I already appears in the negative window; a positive I>=2 maps by the actual opposite relation to 1-I in [-M,-1]. Both local witnesses are retained. Unit lambda=0 removal, and any later removal of the provably harmless eta rows, preserve this coverage; arbitrary further pruning is not covered.

This is an exact constant-factor simplification to m negative clock points and a one-sided readout. The available paid evaluator remains soft O(J+sqrt(Jm)); no soft O(J+sqrt m) prefix method or exponent gain is supplied.
