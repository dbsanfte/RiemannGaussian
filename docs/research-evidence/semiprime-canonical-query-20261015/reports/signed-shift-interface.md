# Signed same-carrier shifts: exact cancellation and the remaining gcd debt

2026-10-15. Scoped analysis, not a general scalar-query lower bound. No repository changes.

## A real endpoint identity, with a real denominator debt

Let P_L(z)=prod_(0<=i<L)(1-z q^i). Then, as polynomial identities,

    (1-z) P_L(zq) = (1-z q^L) P_L(z).

This is division-free and valid over every commutative ring. The quotient shorthand P_L(zq)/P_L(z)=(1-zq^L)/(1-z) may be evaluated when the small endpoint denominator is a unit, but it computes the ratio of two long products, not either product. The homogeneous identity does not recover P_L(z).

If one proposes instead canceling a denominator long product after checking its gcd, that gcd is precisely a long-query acquisition. For a proper gcd the task succeeds, but gcd=N requires localization; assuming gcd=1 excludes all collisions in its support. A cheap endpoint quotient therefore does not inherit ANY semantics for the original interval. For example over F_p let q have order >L+S, choose 1<=t<L and z=q^(-t). P_L(z)=0 while both endpoint factors 1-z and 1-zq^L are nonzero. The endpoint ratio completely misses that interior zero. Such interior examples demonstrate the interface error, not coverage or noncoverage on every prescribed semiprime input.

## Exact signed-interval plateau theorem

Work first with independent labeled factors f_i. A shifted interval [s,s+L) corresponds to prod f_i over that interval. For integer weights c_s of finite support, its net factor multiplicity is

    w(i)=sum_s c_s 1_[s,s+L)(i).

Let s_min and s_max be the extreme shifts and S=s_max-s_min<L. On the entire common interior [s_max,s_min+L), of length L-S,

    w(i)=C=sum_s c_s.

This is exact for arbitrary signed c_s, so covers ALL finite signed combinations, without a restriction on coefficient magnitude. If C!=0, at least L-S labeled factors remain. If C=0, that long interior cancels, but precisely those interior collision events have vanished from the resulting observable. Total weight C is the augmentation invariant of the shift stencil. The elementary first difference has C=0; every further signed difference retains C=0.

For variable lengths L_s, the same conclusion holds on their common intersection: w=C there. Thus near-equal paired row lengths do not change the logic, apart from endpoint discrepancies. If the intersection is empty or the shift span is comparable to L, this particular long-interior bound says nothing.

Small scalar denominators supported on B explicitly acquired labeled residual factors can remove at most B positions from a nonzero plateau, including repeated factors counted by multiplicity. Therefore they cannot remove its Theta(L) interior with soft O(m) atomic denominator factors when L~m². A denominator described as a long Pochhammer is not B=1 under this contract: its collision support must be acquired or justified by another theorem. This is an obstruction to explicit labeled-factor cancellation, not to compressing a high-degree denominator by a new algorithm.

A ratio with C=0 can still help in an adaptive factorization algorithm: it identifies new boundary events conditional on already excluding all denominator events. The missing theorem is a cheap source-preserving denominator gcd/unit certificate or an independent coverage theorem showing the retained boundaries hit a prime. Neither follows from the endpoint identity.

## How actual source arithmetic restricts formal same-ray pairing

The actual first-current source is

    E_j=N+a_j+ell_j-m² carry_j,
    E_j=N(1-j^(-1))² (mod m).

For any given residue e mod the odd auxiliary prime m, there are at most two nonzero tags j with E_j=e mod m: put t=j^(-1), then N(1-t)²=e has at most two roots since m does not divide N. Exact integer same-ray equality E_j-E_k=m² r necessarily implies equality of these low digits. Hence each integer residue ray modulo m² contains at most two actual tags. The conclusion is only about equality of formal integer exponent rays, not local subgroup orbits.

Indeed q=gamma^(m²) and gamma generate the same local subgroup whenever m is coprime to its order. Distinct E mod m² therefore do NOT imply disjoint orbits in a hidden field. We do not make that inference. To rule out accidental equality of finitely many actual numerical nodes by an integer argument, one separately needs a bound on the relevant exponent DIFFERENCES smaller than ord_N(gamma); a lower bound alone without that difference check is insufficient. The retained normalized-node reports contain such checks in their stated ranges, but no local orbit-disjointness follows from them.

The two tags with the same low digit satisfy t'=2-t (when both tags exist). This is different from the antipodal pair j'=-j, whose inverses are -t. Their low digits are N(1-t)² and N(1+t)², differing by -4Nt, nonzero for nonzero t over odd m. Thus antipodal pairing does not directly align the original formal exponent rays. Its known reciprocal identity uses a pair-dependent origin/phase, exactly the data that prevents assuming a free common shifted interval. It yields a product folding, not a signed ratio eliminating collision support.

At most two low-digit matches do not rule out every source-specific signed algorithm. Different row origins can change the low digit; large shifts can exploit global order wrap; algebraic identities can combine unequal labeled factors; numerical local coincidences are permitted. Any such mechanism needs an exact identity plus a paid denominator/coverage analysis.

## A useful algebraic formulation of the next positive target

Supply identities A_j D_j=B_j in R, with A_j the original long row products, where all D_j are certified units or their gcd failures yield proper factors with a saturation-resolution procedure. Then product B_j and inverse product D_j preserve the zero support of product A_j. A nearlinear algorithm must acquire these certificates and B_j in soft O(m) WHOLE-family cost. Merely giving B_j as a small endpoint expression for a ratio of neighboring long products does not satisfy A_j D_j=B_j with a paid unit D_j.

There may be an independently useful prefix-exclusion strategy: acquire a small batch of boundary values, prove no collisions in the skipped interiors on the actual number-theoretic family, then use endpoint ratios. Such an arithmetic exclusion would be substantive new coverage information, and is not present in the low-digit relation or signed-shift algebra alone.

## Outcome

No genuine soft O(m) signed-cancellation algorithm or actual-family boundary-coverage theorem was obtained. What is now rigorous is the augmentation/plateau obstruction for all short signed shift stencils under an explicit labeled-factor cancellation contract, the exact at-most-two formal-ray source constraint, the failure of antipodal pairs to align those rays, and the precise denominator-gcd debt. General local-orbit algorithms and richer scalar identities remain open.
