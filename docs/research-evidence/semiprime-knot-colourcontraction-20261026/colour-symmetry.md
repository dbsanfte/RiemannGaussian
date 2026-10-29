# Colour symmetry: a valid constant quotient and the signed-baseline test

26 October 2026. Bounded constructive pass on the authoritative rectanglequery packet and AGENTS tail. Scratch only, no tests or repository edits. **No power improvement in the complete query.** There is a valid factor-oriented swap quotient of the query family once its scale range is made symmetric. Sign reduction instead needs a changed baseline and does not lower the true phase index. Three-adic/basis recurrences supply no further initialized scalar contraction here.

## 1. Input and operational objective

Use the existing carry-free Gauss grid: a public unit colour j modulo k, p0 a public factor-size scale, a weighted basis u,w of Lambda_j, lengths ell1,ell2, dimensions

    A=ceil(2k*sqrt(N)/ell1), B=ceil(2k*sqrt(N)/ell2),

and acquired canonical generator labels E_j(v)=a+bN+lambda_j(v). The target per cell is a signed Cartesian difference-box product over |r|<A,|s|<B, (r,s)!=(0,0), and short q-shifts h=0..4k. Its public coordinate-span filter makes every leaf nonliteral. Some true-factor cell has a nonunit, not necessarily a global zero. Scalar acquisition is unpaid; the completed explicit rate remains soft k² versus the retained old query soft k^(5/4).

Prior credit includes the exact phase image chi_j(Lambda_j)=g_j² Z/H, g_j=gcd(j-1,k), its basis invariance, the same-colour carry law, three-adic image masks, and fixed-shift certification. None is a new preparation result here.

## 2. Execute a coverage-preserving swap quotient

The public involution is J(j)=N*j^-1 mod k. Transposing a vector exchanges Lambda_j and Lambda_J(j) and preserves its canonical phase when the factor orientation is exchanged. Its weighted norm at scale p0 equals the transposed norm at scale N/p0.

To quotient actual scalar queries rather than merely lattice descriptions, extend the public dyadic scale range symmetrically to

    8H <= p0 <= N/(8H).

It still has O(log N) entries. Every candidate factor S=P or Q has a scale within a factor2, and both p0 and N/p0 remain at least8H. All Gauss-grid estimates survive: nonaxis lengths are at least sqrt(2N), horizontal and vertical lattice axes have length at least8kH>=8sqrt N, product lengths have the same kN covolume bound, and AB=Theta(k). For the TRUE orientation S at its correct scale, the span-filter proof uses g_j<S/(16H) and a_span<8k*sqrt N/S, hence still passes. This is an independently valid orientation, not a transpose inserted into an unproved bare-product ledger.

Choose just ONE representative from each involution orbit, optionally maximizing gcd(j-1,k). Acquire and query its ordinary-baseline cells over this symmetric scale range. The two actual factor colours form one such orbit: if P's class was omitted, Q's is retained and its own correctly weighted cell supplies the guaranteed nonunit. Every retained cell has the ordinary public filter and decoder. Prefixes on the retained cell list preserve the same localization contract. Thus the quotient is a real coverage-preserving reduction in distinct scalar QUERY families, not only a reuse of basis computations.

The enlarged scale range changes the public label-size bound. Now
b_span<4k*p0/sqrt(N)<=sqrt(N)/(2k)<=H/2, so exponents can have size
O(HN+kH), rather than the former O(kN+kH). They still have O(log N)
bits. The nonliteral proof uses a_span and the phase-carry bound, so
it remains valid. The inherited extractor accepts any nonzero global
annihilator of polylogarithmic binary length, which licenses this
enlarged bound at the same once-only T_ext.

Since J is an involution, its orbits have size at most2. Fixed points solve j²=N mod k and number at most2. There are phi(k)=k/3 colours and therefore k/6+O(1) orbits. The full explicit completion remains soft k² and the old native rate is not improved: this is only a constant-factor quotient, with a constant-factor enlarged scale range. In fact the logarithmic length of the scale interval doubles, up to endpoint rounding, so the colour saving need not reduce total cell work. No unacquired factor-size oracle is used.

## 3. Why the sign-colour shortcut changes the physical character

The colours j and -j have the SAME lattice. But their phases satisfy

    lambda_(-j)(v)=-lambda_j(v)+H*epsilon_v,
    epsilon_v=1 if lambda_j(v)>0, else0.

Keeping the ordinary label a+bN+lambda_(-j) does not preserve the original stationary collision at factor P=j mod k. It would use signed factor -P but the WRONG baseline: its gap contains P+1, which need not annihilate the prepared split-group element. Selecting -j=1 mod3 to make gcd(-j-1,k) larger therefore does not establish a cheaper valid physical query.

The correct signed-factor baseline is instead

    E_signed,(-j)(v)=-a-bN+lambda_(-j)(v)
                   =-E_j(v)+H*epsilon_v,
    I_signed=-I_j+epsilon_v.

These are valid exact integer relations, so inverse monomials and small acquired clock shifts can transport the query. But modulo H the corrected exponent character is -chi_j. Its image is still g_j² Z/H and has the SAME size (k/g_j)². A common generator-phase lift changes only a q-power, not that image. This is the precise distinction between a valid sign fold and the tempting but wrong small-index colour -j with ordinary baseline.

For the Cartesian grid, signs can be operationally absorbed: each generator epsilon is0 or1 and the new monomial equals X^-r*Y^-s times q^(r epsilon_u+s epsilon_w). With |r|<A,|s|<B, the clock correction is less than A+B=O(k). If an ordinary hit has h in [0,4k], the signed index is -h+r*epsilon_u+s*epsilon_w and lies in [-8k,8k]. This explicit enlarged interval transports coverage. Every added signed leaf maps back to an original-label comparison with shift magnitude below12k; the same-b span filter still excludes multiples of H, and the different-b remainder is bounded by (16k+2)H<N. Thus the overcover is decodable without assuming its extra factors units. It stores the signed-baseline state as well as the ordinary one. At the chosen representative colour c, ordinary and signed characters differ by 2(a+bN); they are not the same state with the low ordinary g_c index. Pairing them into a rank-two norm doubles the alphabet/state data rather than removing one exponent-scale dimension. The existing common-orientation audits already caution against declaring that norm evaluated.

## 4. Can these symmetries force a cheaper phase index?

Under the only ordinary-factor quotient above, one may choose the better of g(P)=gcd(P-1,k) and g(Q)=gcd(Q-1,k), but there is no uniformly growing lower bound on that maximum in this argument. If actual P,Q are both2 mod3, both g values are2. This actual residue branch is permitted by the prepared input contract; no theorem here excludes it. The statement is conditional on that ACTUAL branch, not a manufactured independent-root counterexample or a distributional argument.

For N=1 mod3, every public colour j=2 mod3 is paired by j->N/j with another colour2 mod3. There are k/6 such colours, leaving Theta(k) ordinary swap-orbits with phase index H/4. Sign transport changes their baseline, not their phase-index invariant. Thus this explicit symmetry quotient does not by itself send all high-index states to cheaper ones.

At every three-adic refinement, a colour2 mod3 and all its lifts remain2 mod3. The constant g=2 therefore survives down that entire branch. The prior canonical child law still has one stationary child on a primitive unit-a row and a genuine quadratic phase image on ramified branches. No multiplication over three children is supplied by the lattice equality. A parent-level query would need its own longer physical shift range; choosing fewer colour labels while leaving the old clock/horizon unchanged is not a coverage proof.

An integral basis change inside Lambda_j also cannot change the image index: chi_j composed with an onto GL2(Z) coordinate map has exactly the same image. It CAN change box shape and scalar evaluation strategy, but not the literal-period requirement. The earlier phase-index obstruction is used only in that narrow sense; no lower bound for implicit/shared norms follows.

## 5. Weil/skein/Hecke scope and remaining scalar target

No new Weil/metaplectic theorem was found that computes this native multiplicative box norm from an orbit of colour labels. These representations normally use a specified finite additive character. Introducing an auxiliary Hth root of unity is not identifying beta with it; native beta has large unknown odd order and its exponent lift retains q-boundaries. The previously audited finite Fourier/Gauss formulas concern additive sums/characters, not the acquired multiplicative scalar here. Nor does an invertible representation basis change acquire a norm value.

The primary [Frohman–Gelca torus skein construction](https://arxiv.org/abs/math/9806107) and [Farey-word recurrences](https://ems.press/content/serial-article-files/52234) are prior sources for specified slope transfers, not colour-subtree union predicates. The primary finite-field Weil character formula [Thomas, The character of the Weil representation](https://doi.org/10.1112/jlms/jdm098) concerns its stated symplectic/finite-or-local-field setting; it is not imported as a composite-ring native product algorithm. No analytic modular/Hecke average or field-only normalization is assumed to preserve collision zeros.

The genuinely executed collective reduction is the swap quotient with symmetric factor-scale acquisition. Its factor-or-value cost includes at most one T_ext=soft N^(31/192); whole-family descriptor preparation remains soft k, but actual scalar readout remains the old paid per-cell soft k and whole-family soft k². Arbitrary smaller subsets must retain the additional T_ext term. The sign map and high-index tree analysis give exact boundary/baseline conditions, not another full-query claim.

A further useful theorem must share or evaluate the actual ordinary/signed box norms across Theta(k) distinct states, or prove a much smaller coverage family. This pass supplies no such scalar identity, invariant descent, or guaranteed exponent improvement. The original soft k^(5/4) complete query remains available and the sixth-exponent goal remains open.
