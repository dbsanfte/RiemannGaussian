# Algebraic symmetry breaking and sparse collision detection

22 October 2026. Broader constructive follow-up; no frozen edits or backend. The strongest new result here is a proved near-linear separator for an ACQUIRED cyclic automorphism-orbit matching instance, with a deterministic sparse-discrepancy version. Native reduction to that instance is not yet proved. Two further precise bridge targets are given with their actual preprocessing charges. None is claimed to close the original collision query.

## 1. A paid cyclic-orbit equalizer can be separated without its full matrix

Here is an exact primitive over the UNKNOWN-factor base ring R=Z/N, N=P Q. Input consists of two already acquired vectors A,B in R^d, d=O(m), and a cyclic permutation action shift_s(A). Assume there is a tag s for which

    B=shift_s(A) mod P in EVERY coordinate,
    B!=shift_s(A) mod Q in at least one coordinate.             (1)

No field, factor, or such tag is supplied to the algorithm. Choose independent uniform r_k in R and form ALL scalar hashes

    H_s=sum_k r_k B_k − sum_k r_k A_(k+s mod d).

One cyclic convolution and a scalar dot product acquire all H_s in soft O(d) native bit work. This is not d vectors: the output is d scalars. Computing their individual gcds with N is also soft O(d). At the promised s, H_s is zero mod P, while its reduction mod Q is uniform because at least one coefficient of the linear form is nonzero. Hence a proper factor is obtained with probability at least 1−1/Q. Every returned factor is verified. Under promise (1), repeating hashes gives a Las Vegas factor finder with expected soft O(d) work.

FULL bit charge: generate d O(log N)-bit random residues, acquire one exact cyclic integer convolution with coefficients reduced mod N (integer coefficient bounds have O(log N+log d) bits), and d gcds. All are soft O(d log N) up to fast-integer/polylog factors. Reading A,B is paid. Finding an appropriate normal basis or constructing A,B from a family of native rows is NOT free.

A deterministic improvement targets a useful arithmetic characteristic. Suppose the nonzero Q-discrepancy in (1) has at most s0 nonzero COORDINATES, with s0=polylog m, and P,Q>d. Replace the random hash by s0 hashes

    r_k^(h)=(k+1)^h, 0<=h<s0.

For the promised tag all hashes still vanish mod P. If all vanished mod Q, the Vandermonde matrix on the at-most-s0 support positions would annihilate their nonzero coefficients. Its determinant is a product of nonzero integer index differences of magnitude <d<Q, a unit, so this is impossible. Thus some hash gives a proper factor DETERMINISTICALLY. All shifts for each h again use a cyclic convolution; total soft O(d s0)=soft O(m). No unknown-characteristic roots of unity are required by exact integer convolution.

This is a concrete constructive characteristic to seek: native varying-weight equalizers become shifts of ONE paid vector in a publicly supplied cyclic/normal coordinate system, and either have local asymmetry or a sparse asymmetric discrepancy. It would remove the m-by-m comparison matrix. The current T_j vary through C_j raised to a_j, rho_(j^-1)(C_N), and native exponent carries; no identity making that family a single cyclic orbit was found. An unknown long index must also be eliminated into B rather than silently making B_i for all L. Merely writing an arbitrary automorphism in a normal basis does not supply these requirements.

## 2. Target a small-rank defect of an explicit permutation action

A second actually fast consumer is available if a source-bearing equalizer is encoded in

    M=I−alpha Pi−U V^T,

where Pi is an explicit permutation on d=O(m) coordinates and U,V are acquired d-by-r scalar arrays with r=polylog m. This is an INPUT representation of size soft m, not a dense matrix supplied for free. Set D0=I−alpha Pi. For every permutation cycle of length c, D0 inverse is acquired by the elementary cyclic recurrence with denominator 1−alpha^c. Guard these denominators by scalar gcds: a proper gcd is already a factor; a saturated denominator means this chosen alpha is outside the inverse consumer's contract, not permission to divide.

When the denominators are units, solve D0 Z=U in O(dr) scalar operations, form K=I_r−V^T Z in O(dr²), and compute det K with guarded exact small-matrix arithmetic or division-free determinants. The determinant lemma gives

    det M=det D0 * det K.

Since det D0 is a unit, gcd(det K,N) has exactly the same base-prime singularity support. Thus singularity mod P and nonsingularity mod Q yield a proper factor in soft O(m). The r-by-r determinant cost is polylog m; the input arrays, cycle preprocessing and inverse guards are all charged. Saturation at both primes still needs a restriction/leaf theorem, not a claim that every singular matrix factors N.

The useful characteristic is a constant/polylog-rank DEFECT of a known permutation or automorphism, with source-forced CRT rank imbalance. This is sharper than asking for a generic nullspace of a degree-m² carrier. A sufficient new lemma would construct this representation from the original native rows in soft m, show that a true whole-local source forces the relevant defect singularity, and supply either opposite-prime nonsingularity or a restriction-stable certified scalar leaf. No such native low-rank representation is asserted here. Current unit-norm identities alone give no rank-imbalance theorem.

### Why finite-algebra results motivate this target, with exact scope

Rónyai, *Computing the structure of finite algebras* (JSC 9 (1990),355–373), primary publisher abstract inspected: https://doi.org/10.1016/S0747-7171(08)80017-X . It treats finite-dimensional associative algebras over SUPPLIED finite fields; zero-divisor finding is related to polynomial factoring, with Las Vegas polynomial-time applications. This is not a near-linear theorem over Z/N with implicit structure constants.

Ivanyos–Karpinski–Rónyai–Saxena, *Trading GRH for algebra*, arXiv:0811.3165v2 (8 Feb2009), full primary text opened, Sections3–5 inspected: https://arxiv.org/pdf/0811.3165 . Proposition3.2 finds a zero divisor when a given automorphism group is not semiregular, using fixed algebras and linear algebra; Theorem4.7 handles a given noncyclic automorphism group in deterministic polynomial time over a supplied finite field. Theorem5.6 gives factor-or-semiregular-automorphism in deterministic poly(m^(log m),log|A|), not soft m. These are unconditional statements, not GRH oracles. Their internal algebra zero divisor need NOT distinguish P from Q: it may select cyclotomic components at both primes. A base-factor consumer needs CRT asymmetry or a certified same-leaf decoder.

Ivanyos–Karpinski–Saxena, *Schemes for Deterministic Polynomial Factoring*, primary ECCC paper inspected: https://eccc.weizmann.ac.il/report/2008/043/download . Its schemes refine explicit tensor-power algebras, with ranks growing as n^h; its prime-degree smoothness result is GRH-conditional. The design idea is to force a nontrivial stable relation, but constructing tensor rank m² is outside the present budget. Candidate2 deliberately asks for a paid small-rank defect instead.

## 3. Nonnegative sparse support can use a PUBLIC coefficient field

The original scalar orbit has local orders greater than L. Hence for each row at most one index collides modulo each hidden prime. Encode the union mask as

    F(Z)=sum_(j,i: gcd(y_j−q^i,N)>1) Z^(j+J*i),
    0<=j<J, 0<=i<L.

It has degree <J L=O(m³), at most 2J=O(m) terms, and coefficient ONE at each distinct leaf. No hidden field appears in this description. Choose a public prime p0>2J in soft m sieve work. Every bucket coefficient in F mod(Z^s−1), computed in F_p0, lies between zero and2J and cannot cancel. Therefore these are genuine zero-retaining sketches, unlike signed Jacobi sums. Recovered exponents identify ORIGINAL scalar leaves, which can be verified and fed to the proper/saturated scalar recovery contract.

The characteristic to target is an OUTPUT-sparse principal-character mask together with a cheap modular-image mechanism. Exact term sparsity is already proved; image acquisition is not. A sufficient bridge is: after soft m public preprocessing, supply the shifted low-order images required by sparse interpolation with cost quasi-linear in TOTAL probe degree, whose total is soft O(J). In particular the oracle must not acquire the J*L leaves, call a length-m packed routine once per bucket, or rebuild an m-vector for each probe. This is a precise possible character-histogram/automorphism sketch target, not a claim that sparse interpolation constructs the oracle.

Arnold–Giesbrecht–Roche, *Sparse interpolation over finite fields via low-order roots of unity*, arXiv:1401.4744v2, primary full paper opened; Theorem1.1 and probe model inspected: https://arxiv.org/pdf/1401.4744 . For a division-free straight-line program of length lambda computing a T-sparse degree-D polynomial over a SUPPLIED F_p0, its Monte Carlo bit cost is soft O(lambda T log²D(log D+log p0)log(1/epsilon)). This charges program length as well as sparsity. A lambda=Theta(m) program would still cost roughly m²; to use its near-linear output regime one needs a polylog-length representation or the stronger preprocessed-image interface just specified. Deterministic methods listed in its comparison table have larger sparsity dependence; this cited theorem is RANDOMIZED, not a deterministic collision algorithm.

Nonnegative integer bucket coefficients make modular reconstruction safe and enable deterministic verification of a reported leaf, but they do not turn a signed Fourier transform into an acquired principal mask. The image-oracle construction is the substantive missing arithmetic theorem. The same-leaf semantics remain explicit; no Gauss-component OR is substituted for a scalar zero.

## Frobenius/period algorithms: promising symmetry, fully charged hypotheses

Lenstra–Pomerance, *Primality testing with Gaussian periods*, author version20090807, full primary PDF opened, introduction inspected: https://math.dartmouth.edu/~carlp/aks080709.pdf . It constructs auxiliary ring extensions and gives a deterministic primality test with bit bound (log N)^6(2+loglogN)^c. Its output is primality, not a factor or a hidden-characteristic Frobenius oracle. A compositeness relation may fail by a UNIT, so it cannot automatically serve as CRT support. It nevertheless motivates looking for small presentations with prescribed automorphism actions rather than dense coefficient tables.

Pila, *Frobenius Maps of Abelian Varieties and Finding Roots of Unity in Finite Fields*, author full PDF opened; TheoremsA–D/introduction inspected: https://people.maths.ox.ac.uk/pila/Frobenius.pdf . The deterministic polynomial-in-log(q) theorem fixes the defining variety/addition-law complexity; the constants and exponent depend on those data. The roots-of-unity application fixes the auxiliary prime order, and the prime field characteristic is supplied. Growing dimension/order m and unknown P cannot be hidden inside its fixed-data constants. A genuinely bounded-dimensional source-bearing family with cheaply acquired defining equations WOULD be a useful characteristic; no such family carrying all native m-by-m² leaves is constructed here.

## Priority and exact next work

Candidate1 is the clearest new consumer: it proves an actual near-linear equalizer-to-factor algorithm over the composite base, with a deterministic sparse-discrepancy refinement. The next arithmetic search should therefore try to express normalized native constraints as cyclic shifts of ONE acquired object, or show sparse coefficient discrepancy after a source-preserving projection. Candidate2 targets a different explicit structure, small-rank permutation defects. Candidate3 targets directly nonnegative sparse mask sketches over a public small field. None requires a hidden prime as an input; each states the specific missing source-preserving construction rather than assuming its expensive data.

All original whole-local / paired-leaf requirements remain in force. Internal extension idempotents, compositeness witnesses, and globally valid unit cocycles are not automatically base-prime separators. No full collision-query algorithm is claimed, and no generic lower bound is inferred from the missing bridges.
