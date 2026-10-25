# Independent terminal-contract proof review

Verdict: PASS, no required corrections.

Reviewed exact source `/tmp/semiprime-scalar-terminal-20261024/terminal-contract.md`, SHA256 `202706e6213e9ba5e9957c7e7d712a46e2a2dbd555329f4bf6298c2a017026c8`.

Compared directly with `/tmp/semiprime-paired-weighted-query-20261024/scalar-catalogue.md`, SHA256 `9ded79850c2f200069a7da67502d0de579d1df0457cb06c865fb3d39c9654058`, and verified its cited independent review hash `ce4d15b225d546c8008efaf5e6bdb2d2c0923b2b99d8603d3e1e24273efc6c27`.

* The virtual Gauss lattice proof and automatic nonzero Fermat integer apply independently to either factor R, including the larger factor. Thus both prime components of the complete aggregate vanish. No common row or index is inferred.
* A single labelled nonunit index suffices: scanning its original scalar leaves either finds a proper gcd or a saturated leaf with a nonzero O(log N)-bit GLOBAL annihilator. Public whole-row deletion supplies the nonzero condition; the existing extractor's odd-order and size hypotheses remain intact. No product assembled from different local leaves is passed to the extractor.
* The kernel-coordinate interface is sufficient without acquiring an h-coordinate vector: the permutation shift gives f_s w_s=0 at its labelled coordinate. A proper gcd of w_s factors, while a unit coordinate forces f_s=0 globally. Conversely a globally zero f_s gives the explicit kernel vector e_s.
* Known-zero bisection is valid over the composite ring: a unit half forces the other half's product to remain zero, a saturated half is retained, and a proper gcd terminates. Its first acquired half still costs the same asymptotic restricted query; no speedup follows from skipping the already known complete product.
* The signed opposite is retained in the full catalogue: lambda'=(-lambda mod H), kappa=(lambda+lambda')/H in {0,1}, and I'=kappa-I. Writing A=4sqrt(kN)/H, the source bound |I|<A+1 gives |I'|<A+2<=M, so the opposite index is inside the tested window. Its Fermat integer is exactly the negative of the original. If kappa=1 the indices differ by integrality; if kappa=0 equality would force I=0 and aR+bS=0. Coprimality and |a|,|b|<=k<min(R,S) then force a=b=0, excluded. Hence each local field has at least two distinct zero weights.
* Consequently every cyclic product of h-1 weights contains a zero in each local field, proving T^(h-1)=0 over Z/N. The general identities T^h=0, det(I-T)=1, and its finite geometric inverse are also correct. Neither nilpotence nor the unit inverse denominator acquires a labelled nonzero kernel coordinate.

This is a correct clarification of the acquired-output contract. It claims no faster terminal algorithm, factoring exponent improvement, or completion of the sixth-scale goal. No source or shared repository file was edited.
