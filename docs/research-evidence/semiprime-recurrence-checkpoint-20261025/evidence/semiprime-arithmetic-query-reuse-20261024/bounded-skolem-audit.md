# A new bounded-orbit theorem tested on an initialized native triple

24 October 2026. A 2026 primary theorem handles exponentially long bounded zero searches for fixed-order INTEGER recurrences. The native triple can genuinely be initialized as such an integer recurrence in soft k total input work. The theorem tests exact integer zero, however, and its candidate list does not cover unknown-prime divisibility. No finite modular query acceleration is obtained below.

## Primary theorem, version and cost contract

Piotr Bacik, Joël Ouaknine and James Worrell, *On the Complexity of the Skolem Problem at Low Orders*, SODA 2026, pp5255–5269, DOI10.1137/1.9781611978971.191:
https://epubs.siam.org/doi/10.1137/1.9781611978971.191
https://arxiv.org/abs/2507.11234
https://arxiv.org/pdf/2507.11234v3

The checked current v3 is revised17July2026. Cached `sources/bounded-skolem-v3.pdf`, SHA256 `968631400a0ab075528258bde23aedf9fb95b21477bce1f83d0a065875b31982`. An older accepted/v2 manuscript downloaded from the MPG archive is separately cached as `bounded-skolem.pdf`, SHA256 `00eac896057f03bd76272f70d757b32f2c7932e8c9cdd4348c37d7c174d51215`; theorem numbering and the audit below use v3.

Theorem3.1 gives, for each FIXED order d, a polynomial-time disjunctive reduction of bounded INTEGER-LRS zero detection to EqSLP, hence a coRP algorithm. Theorem3.6 gives the corresponding zero-set function problem using EqSLP, with output represented as a finite exceptional set plus finitely many arithmetic progressions. The input coefficients, starts and horizon are binary integers. The order dependence is exponential; the theorem is not a deterministic finite-field or composite-ring zero detector.

Lemma3.2 chooses a small auxiliary prime p not dividing the recurrence's nonzero constant coefficient and finds M with the companion matrix A satisfying A^M=I mod p. The proof of Theorem3.1 examines the M subsequences, isolates p-adic analytic zeros and obtains polynomially many integer candidates. Final EqSLP tests distinguish exact integer zero from a merely nearby p-adic zero. This is an actual algorithmic theorem, not a power-root-search oracle.

## Initialize its input from the actual constant triple

Inherited fixed-triple input: `/tmp/semiprime-jet-recurrence-20261024/constant-blocks.md`, SHA256 `30e92d4286611be1e6a70e28ac2c612e673e44a919d9c281e5d86486964153f7`. Its changed-modulus preparation, orientation scope, original carries and full fallback remain paid as stated there.

Use the forward-root triple polynomial F_c(X)=prod_h(X-Vhat_h)=sum_(s=0)^3 f_s X^s, monic with unit constant term, and the supplied q in B=(Z/NZ)[tau]/(tau²-D), D<0. Its three roots are reciprocals of the inverse Pochhammer arguments, so F_c(q^n)=0 is exactly their native P_L collision. Reciprocation preserves the quadratic-phase form, with curvature inverted, and all original labels remain attached. Lift q and all f_s to the integer quadratic algebra Z[tau]/(tau²-D), preserving the monic leading coefficient. Denote the lifts by tildes. Let Q be the2-by-2 integer multiplication matrix of qtilde=q0+q1*tau:

    Q=[[q0,D*q1],[q1,q0]],
    T=diag(I2,Q,Q²,Q³),
    z=(e0,e0,e0,e0)^t.

If L_c is the2-by-8 block row of multiplication matrices for ftilde_0,...,ftilde_3, the coordinate vector of Ftilde_c(qtilde^n) is L_c T^n z. Its INTEGER norm

    u_n=Norm(Ftilde_c(qtilde^n))

is a scalar matrix sequence with realization T tensor T, dimension64: apply L_c tensor L_c and the norm functional selecting coordinate00 minus D times coordinate11. All entries are actual known integers. Cayley–Hamilton supplies an integer recurrence of order at most64, and its first64 values and coefficients have O(log N) bit lengths up to fixed constants. These data cost polynomial(log N) per class, soft k over Theta(k) triples. Since D<0 and qtilde is nonzero, Norm(qtilde)>0, so the realization matrix is nonsingular over Q and a nonzero constant-coefficient recurrence is available.

Thus there is no unpaid start or hidden growing order in THIS attempted application. The SODA theorem really would give a randomized soft-k family of exact-integer-zero tests. The remaining mismatch is arithmetic, not initialization.

## Execute the attempted modular adaptation and retain its missing condition

Reduction modulo N identifies u_n with the actual quadratic norm of F_c(q^n). The desired good-side event is P dividing u_n, for an UNKNOWN factor P. It is not u_n=0 as an integer. Choosing integer lifts does not change the modular event, while the exact-zero question depends on those lifts. Consequently replacing the final EqSLP tests by gcd(u_n,N) does NOT prove that the theorem's candidate list contains the native hit. Candidate completeness was proved only for exact integer zeros of the chosen lift. This is the precise missing implication in that adaptation.

Nor may the auxiliary small prime p selected by Lemma3.2 be identified with the unknown P. If one hypothetically tries the same interpolation at P on the explicitly supplied realization T tensor T, its required decimation includes Q^(3M)=I. The prepared local q order is k-rough and greater than16H, with3 dividing k and L<4H; in particular it is greater than L. Thus ord(q³)=ord(q)>L. This literal realization therefore requires M>L. Scheduling all M residue subsequences, as the proof does, loses the desired short input bound before any candidate pruning. This is a cost statement about that executed realization, not a lower bound on minimal scalar realizations, alternative interpolations or all local-zero algorithms.

Only the small AUXILIARY prime gives the paper's polynomially bounded decimation; at that prime the theorem isolates exact integer zeros and supplies no completeness statement for P-divisibility. A new argument covering the native modular hit with a polynomial-size acquired candidate set would be a substantive acquisition advance. It is not a consequence of this theorem's p-adic root count or of the local uniqueness promise.

The ordinary full-subgroup gcd shortcut with X^M-1, formal q-dispersion, q-suitable oracles, selected-factor images and dense-input gcd are earlier audits and are not reused as new results here. This pass found no initialized deterministic interval-orbit detector improving soft(J+sqrt(JL)). The original restricted query, native witness checks, orientation qualification and fallback remain unchanged; no impossibility or improved factoring exponent is asserted.
