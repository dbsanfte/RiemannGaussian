# Fixed-modulus density accounting for the canonical norm consumer

22 October 2026. Exact canonical dependence, degeneracies, initial gcd and singleton accounting are proved below. The separately supplied uniform generalized-Pell counting lemma in `pell-count.md` closes the final pair-density bound; its ideal-count/unit-separation proof was read and checked here. No numerical examples, implementation or repository changes.

Fix an odd public prime m, M=m^3, and constants c,alpha,beta>0. Consider distinct-prime N=P Q in [cM^2,M^2] with alpha M<=P,Q<=beta M and m not dividing N. This is a fixed admissible-modulus family. It is NOT the literal least-auxiliary-prime selector bin (previousprime^6,m^6], nor an adaptive choice of modulus.

## Canonical parameter dependence

For a residue N0 modulo M coprime to m, the row a is fixed by N0 modulo m; the centered b is fixed by N0 modulo m^2. Under N -> N+M t, c_row -> c_row+m t, so Delta -> Delta-4am t. Therefore kappa modulo m, ell and v=ell-m^2 kappa are fixed. The exact integer norm values are

    z_j(N)=(v_j^2-4a_jN)/M,
    z_j(N0+Mt)=z_j(N0)-4a_j t.

All v are nonzero modulo m and satisfy |v|<=2M for m>=3; all a lie in [1,m). Each occurring a has exactly two tags, and every a has at most two. The interval has O(M) possible higher digits t. The total number of residue-rowpair triples is O(M*m^2)=O(m^5).

## Initial gcd successes: O(m^4)

Fix N0 and a row v. If a balanced hidden prime P divides v, write |v|=P h with positive integer h<=2/alpha. For each h there is at most one candidate P, so there are O_alpha(1) candidates regardless of whether v is factored. Because gcd(P,M)=1, P Q=N0 modulo M fixes Q modulo M. Its interval [alpha M,beta M] contains O_beta(1) choices. Thus each residue-row contributes O_alpha,beta(1) candidate inputs with a nonunit gcd(v,N). Summing O(M*m) descriptors gives O(m^4). This is a counting argument, not an instruction to factor the v values.

Squarefreeness and the exact norm relation imply gcd(v,N)=gcd(z,N), since m is a unit. Thus initial z screens add no cases. In the balanced regime |v|<N for sufficiently large m, saturation gcd(v,N)=N is impossible. Other explicit small-input guards have no effect on the asymptotic count. Also a<m<P,Q, so gcd(a,N) adds none. The choice m|N is excluded by the displayed balanced hypothesis for large m.

## Useful singleton square dependency: O_c(m^3)

A singleton norm relation is actionable only if Mz is an integer square; merely z square is insufficient when m is nonsquare. Write

    W^2=Mz=v^2-4aN, W>=0.

Then |v|<=2M and N>=cM^2 imply a<=1/c. Thus for a fixed N0 only O_c(1) a values and twice as many row tags can contribute. Also 0<=W<=2M and W^2=v^2 modulo M. Since m does not divide v, the only roots are W=+v or -v modulo M; each has O(1) representatives in [0,2M]. Each W determines at most one N=(v^2-W^2)/(4a). Therefore all singleton-square cases number O_c(M)=O_c(m^3), including any trivial ones. W=0 is impossible for distinct-prime N with a<m<P,Q, since v^2=4aN has odd valuations at P,Q.

## Pair reduction and exact zero-discriminant degeneracy

For two rows set

    C=a_i z_j-a_j z_i=(a_i v_j^2-a_j v_i^2)/M.

C is an integer fixed by N0; |C|=O(m^4). If z_i z_j=Y^2 for an integer Y, then

    (2a_j z_i+C)^2-4a_i a_j Y^2=C^2.          (P)

Here |z_i|=O_c(m^4), so the first coordinate is O_c(m^5), and |Y|=O_c(m^4). Every N gives at most the harmless signs of Y and otherwise injects via z_i into the solutions of (P).

When C=0, v_i^2/a_i=v_j^2/a_j. If z_i z_j is square, the normalized rational roots are globally equal up to sign. Indeed z_i/z_j=a_i/a_j=v_i^2/v_j^2, so the rational square root of their ratio is v_i/v_j up to sign. All denominators are units on the screened branch. Hence such pairs are globally trivial and cannot contribute successful root-comparison factors. This includes exactly opposite centered Hensel signs. C=0 must be removed before invoking a nonzero-right-side Pell bound.

If 4a_i a_j is itself an integer square and C!=0, equation (P) factors into two integer factors of C^2 (after the known integer square coefficient is absorbed into Y). The number of solutions is bounded by a constant times the divisor count tau(C^2), which is m^{o(1)} for |C|=O(m^4). No Pell theorem is needed for this split case.

For nonsquare 4a_i a_j and nonzero C, a UNIFORM bound m^{o(1)} for solutions of (P) in the stated box is the exact remaining counting input. Uniformity must cover varying discriminants O(m^2), varying nonzero C=O(m^4), imprimitive solutions, and potentially nonfundamental quadratic orders. A fixed-discriminant statement or an unspecified number of Pell orbits does not suffice. This report defers that input to the independent audit rather than treating it as free.

## Fixed-modulus density conclusion and selector boundary

The uniform lemma in `pell-count.md` holds: pass to the maximal real quadratic order, count at most tau(C²) integral ideals of norm C², and note that same-sign generators of one ideal differ by a positive norm-one unit at least (3+sqrt(5))/2. Polynomial archimedean height then leaves O(log m) generators per ideal. This handles varying orders and imprimitive solutions without a regulator or class-number cost. Therefore the union bound over O(m^5) residue-rowpair triples gives O(m^{5+o(1)}) inputs with any nontrivial square-product pair. Adding all initial gcd and singleton successes preserves that bound. This is negligible compared with a fixed balanced prime box containing Omega(m^6/log^2 m) distinct-prime products: such a box can be chosen inside [c m^6,m^6] when c<1 (for example inside [0.5m^6,m^6]), and the prime number theorem supplies its prime counts. It shows that most inputs in THAT fixed-modulus box defeat the norm pair/singleton consumer, without claiming a factoring lower bound.

This conclusion does not refute a literal least-prime selector, an adaptive modulus menu, higher square dependencies, or another use of the lifted family. A large interval [c m^6,m^6] is not the narrow actual selector bin (previousprime^6,m^6]. Passing between them needs a separate uniform argument and cannot be inferred by deleting an unspecified exceptional set.
