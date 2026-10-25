# Independent review: twist norm and coherent-root preparation

22 October 2026. Reviewed `twist-norm-aggregation.md` and `coherent-root-preparation.md` in this directory. Verdict: algebraic and cost conclusions PASS, with one necessary qualification to the etale-algebra unit wording. No implementation, tests or repository edits.

## Essential scope and progress distinction

The acquired polynomial F_h(U)=product_j(U-x_j^h) compresses a COMPLETE root-of-unity twist fibre for each original x_j. It does not compress the actual multiplier-recursion descendants, which have shifted geometric origins. Those shifts are generally not roots-of-unity ratios. No identification of the J*2^d shifted-origin requests with these twist fibres is proved. Thus the heading's 'explicit twist branches' is valid only for the formally completed twist family; it must not be read as the previously unpaid recursive state family. The report correctly retains the long resultant as unpaid, and the coherent-root report explicitly retains branching costs. An explicit sentence with this distinction near the twist report's opening/outcome would prevent overstating progress.

## Resultants and signs

For monic F(T)=product(T-x_j), Res_T(F(T),U-T^h)=product(U-x_j^h), with no sign. The original aggregate Res_T(F,H)=product_j H(x_j) also has the displayed orientation. For a seed s,

    product_(zeta^h=1)(zeta*x-s)=(-1)^(h-1)(x^h-s^h).

Therefore product_zeta H(zeta*x;q)=(-1)^((h-1)D) H(x^h;q^h), exactly as reported. The known global sign does not affect gcd support.

All powered x_j^h are acquired by O(log h) squarings per target; the product tree has degree J. No generic Jh-degree resultant computation is needed for this special polynomial. Repeated roots do not invalidate its monic product construction or later aggregate identities.

## Required etale qualification and simpler support proof

The phrase 'zeta!=1' is insufficient for an arbitrary element of an etale splitting algebra: it may equal 1 on one component and differ on another. Consequently x-zeta*s need not be a unit merely from global inequality zeta!=1. Correct it to a nonidentity LABELED root on every geometric component. This can be arranged with a primitive hth root in its primitive cyclotomic algebra: each nonzero exponent modulo h remains nonidentity in every geometric specialization, since the characteristic is odd. There the odd-order ratio cannot equal its nontrivial 2-power-order value, so each companion is a unit in every component.

The needed scalar support assertion has an even simpler proof avoiding this language: in either hidden field, x and s are in a common odd subgroup and h is a power of two. Thus x^h=s^h iff x=s. It follows directly that H(x^h;q^h) and H(x;q) vanish at exactly the same hidden primes. This proof validates all scalar aggregate support conclusions regardless of how a proof-side splitting algebra is represented. It does not acquire the companion unit values.

## Quotient formulas, cost, and localization

The quotient-ring product q^(mn*a) B(T q^(-mn)) equals product_r(T-q^(r+mn)) termwise. Its norm is the stated aggregate. Monic F and unit q make this division-safe; no row-value inverse occurs. The scalar-clock A(Z)=product_(j,r)(x_j-q^r Z) has degree J*a, and the report explicitly charges that size instead of assuming a constant-cost quotient carrier. The remaining H resultant is not acquired by F_h's coefficients or the earlier binomial remainder primitive.

A future uniform evaluator valid on arbitrary public target subsets would support a balanced localization path. At a node already known nonunit, a unit child forces the other child nonunit; a saturated child remains selectable; a proper child gcd already factors. O(log J) uniform calls have the stated soft bound, including one sqrt(L) charge per level hidden in logarithms. A supplied isolated saturated aggregate alone is insufficient, as the report correctly states. After row selection, original unmasked interval descent retains a real original scalar collision and the nonzero annihilator ledger. No twist-unit division or interior-zero cancellation is used.

## Coherent preparation

With gamma=gamma0^(2^D), odd local orders are unchanged, as are q's local orders. The explicit level-d roots gamma0^(2^(D-d) A_j), gamma0^(2^(D-d)m^2), and gamma0^(2^(D-d)m^3) satisfy the displayed equalities globally. Their acquisition for all original J inputs and O(log m) levels costs soft O(J); exponent bit lengths remain O(log N). These are genuine prepaid coherent roots, not a hidden-order square-root oracle.

Local support and annihilator recovery are unchanged because an odd order divides 2^D K exactly when it divides K. The SAME K suffices for gamma0; multiplying its bit length by 2^D is unnecessary. The preparation applies to the stated base-flexible pipeline, not silently to any fixed-numerical-base theorem. It supplies original-input root chains only, not a free evaluation of every descendant or a new terminal base case.

Conclusion: special complete-twist target-polynomial acquisition and coherent original-root preparation are paid. The claimed long evaluator is correctly left open. Qualify the etale root wording and distinguish twist fibres from shifted recursion states explicitly; neither repair changes the correct scalar identities or cost boundary.
