# Independent review: conic-exchange.md

26 October 2026. Read-only algebraic review; no experiments or repository changes. **PASS for the stated original integer-label interval constructor**, with the m=0 and folded-scope qualifications below.

## Reflections, carries, and local scalar identity

Expansion verifies both reflections preserve lambda²-4ac and e=a+c+lambda before reduction. Their reductions modulo H remain involutions. The admissible signed-band lift is unique because its span is less than H; accepting only actual retained images makes the first reflection's accepted edges pairs or fixed points. Its actual E difference is a multiple of H of absolute value less than H+2k<2H, hence -H,0,H.

The composition satisfies D_new=D-4e and the printed quadratic formulas (5). The four-corner representation E=bN+c_b*t²+2t-S*kappa follows directly from the definitions of tauhat and h. Its mixed difference is 2*c_b*nu*omega-S*Delta kappa, proving (6) with the printed sign. The linear and quadratic corrections in (7) are correct; neither is dropped.

For E'=E+H, A_m(E')=q^m prod_(j=2)^(m+1)(y-q^(-j)), which proves (3). For m>=1 the union of the two zero supports is exactly indices 1,...,m+1, and multiplicities do not change local-zero bits over squarefree N. Boundary decoding correctly returns to an actual source row/index. **Minor edge case:** m=0 is a separate empty-prefix value 1; replacing its paired empty products by A_1(E) would be false. The physical long-horizon application already has m>=1, but that guard should accompany the predicate replacement.

## Literal interval mass: proved with explicit assumptions

Use |a|,|b|<=k, 0<=lambda<H, N>256H², k>16, and m<16H. If b'!=b,

    |E'-E| >= N-2k-(H-1).

This excludes integer adjacency +/-H. For E'=E mod H it gives

    |(E'-E)/H| >= N/H-1-2k/H >256H-2>16H>m.

Consequently different-b length-m integer windows never overlap. At fixed b the label span is at most H+2k-1<2H. There are at most two DISTINCT labels in each residue class modulo H. Thus every interval union has at least one full length-m window per at most two distinct labels, giving total mass at least (J_distinct/2)*m. This holds after closing every literal residue-preserving reflection edge: the stronger operation of grouping all equal residues has already been bounded.

No unknown-order congruence beta^(E'-E)=q^d is substituted for an integer equality here. Modular-only aliases are correctly excluded from the conclusion's scope.

## Actual b=1 subset: Omega(k) distinct labels

It suffices to use POSITIVE a in [1,k-1] with aN=1 mod 3, excluding a=1. There are Omega(k) such a. Since N is coprime to 6 and k=2*3^e, S=3^(2e); aN is a unit square modulo S exactly when it is 1 modulo 3. Hence mu²=aN mod S has two roots modulo S, each with two representatives mu in [0,2S). These give exactly four lambda=2mu in [0,H).

Fix an integer E in this subset. Since a=E-N-2mu,

    (mu+N)²=NE mod S.

The permitted positive-a interval restricts mu to an interval of span less than k/2=3^e. For a square congruence z²=A mod 3^(2e):

* If A=0 mod S, all roots form one coset of step 3^e.
* Otherwise, if solutions exist, v_3(A)=2t with t<e, and the roots form two cosets of step 3^(2e-t), which is at least 3^(e+1).

Thus at most one root per coset lies in that short interval: each E has at most two descriptions. Even the report's wider signed-a interval, of span less than k in mu, still has O(1) descriptions; the positive subset gives the sharper <=2 directly. It follows that there are Omega(k) distinct E.

These positive rows and their swap partners have E>=N-O(1), whereas the public deleted physical integer labels satisfy |Hi|<=Hm<16H²<N. Hence integer-zero deletion removes none of this subset. Removing a=1 removes only constantly many descriptions. The claimed complete-family lower bound is therefore supported under the stated diagonal/nonaxis pruning schedule. It is explicitly not asserted after arbitrary new coverage-preserving restrictions.

## Original versus folded scope

Combining the two counts proves Omega(k*m) literal interval-union mass for the currently specified complete ORIGINAL family, after exact integer-label deduplication and stated pruning. It does not alone prove the same statement for every reciprocal-folded representation, an order-dependent modular grouping, a selected coverage subfamily, or a different nonlinear conic contraction. A specific constant-size opposite/root-coset fold may preserve the power-scale lower bound after its own bookkeeping, but that extension must be stated/proved for its actual representative and interval conventions. The report's qualified final conclusion is correctly about the tested original exponent-orbit interval constructor, not the original query's complexity in general.

The local exchanges remain valid finite interfaces. The whole-family count rejects their use as a literal-interval-merging power improvement; it does not reject other weighted identities using the same conic graph.
