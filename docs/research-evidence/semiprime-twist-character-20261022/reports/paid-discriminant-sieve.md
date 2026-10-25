# Actual integer-root discriminant: paid CRT sieve and shared group query

2026-10-22. This note investigates the actual sigma-dependent discriminant. It does not substitute the base Gauss-row discriminant, and proves no universal soft-m acquisition bound. No code, examples, repository changes or special-family expansion.

## 1. Exact witness and square-content normalization

Assume a!=0 and a public Gauss row (a,b,c,s,H), gcd(s,H)=gcd(H,N)=1, with

 H²c−sHb+s²a=C N, D=bH−2as.

The candidate integer-root polynomial is

 F_sigma(Y)=aY²+(D−H²sigma)Y+C N.

For the true local factor P and its native row/interval witness sigma,

 F_sigma(P)=0,
 Delta_sigma=(D−H²sigma)²−4aCN=(aP−CQ)².

This is the ACTUAL integer square condition. It differs from the public square congruence of the unmodified row discriminant.

The row identity gives the exact stronger normalization

 Delta_sigma=H² delta_sigma,
 delta_sigma=(b−Hsigma)²−4a(c−s sigma)
            =H²sigma²−2D sigma+(b²−4ac).

Therefore Delta_sigma is an integer square iff delta_sigma is an integer square. Divisibility H|sqrt(Delta_sigma) follows prime by prime, including prime powers. Screening delta_sigma is strictly better than screening the unnormalized Delta at primes dividing H. A normalized square root v gives the candidate

 t=(Hsigma−b +/- v)/(2a), P=Ht+s.

Check exact divisibility and a proper gcd with N. Thus surviving sigma values can also be tested directly without acquiring a group residual.

## 2. Exact local sets, including modulus primes

For an auxiliary odd prime ell, compute the allowed set

 R_j(ell)={r mod ell: delta_j(r) is a square mod ell},

including zero as a square. These are public finite-field computations, not hidden local Legendre symbols. If gcd(ell,N) is proper it already factors N.

For ell not dividing 2 H a C N, multiplication by H² and the affine variable change T=D−H²sigma identify this with T²−A being a square, A=4aCN. Consequently

 |R_j(ell)|=(ell+chi_ell(aCN))/2.

Proof: sum_T chi(T²−A)=−1, and the number of zero values is 1+chi(A). Thus the nonnegative-character count is (ell+chi(A))/2. The row-dependent D changes the affine location but not this density.

If ell|H and ell does not divide a (s is already a unit), the NORMALIZED polynomial is affine:

 delta_sigma=b²−4ac+4as sigma mod ell,

so |R_j(ell)|=(ell+1)/2. The unnormalized Delta is identically zero modulo ell and would miss this restriction entirely. If ell divides both H and a, the normalized value reduces to b², so the local condition is vacuous. If ell does not divide H but ell|aCN, Delta is itself a square polynomial and again imposes no cut. Every degenerate case must therefore be included or handled explicitly; one cannot claim a half-density bound simultaneously for all actual rows without a further proof.

At prime powers the same exact finite-set construction works, but powers of a fixed prime do not generally provide independent half-cuts. The square-image condition has open residue classes of positive p-adic density; increasing the exponent refines their representation rather than supplying a new independent character. Prime-power handling may improve constants or enforce singular-valuation conditions, but no exponent improvement is derived here.

## 3. A fully charged construction preserving the witness

Give each row its native integer interval I_j of length at most L and choose a squarefree auxiliary modulus M with its prime factors supplied by a public sieve. For each row:

1. Enumerate every allowed local residue set above. A direct table costs soft O(sum_(ell|M) ell) field/bit work per row; squares can be tabulated once at each auxiliary prime.
2. CRT-enumerate the full Cartesian product to obtain R_j(M). Its ACTUAL size is R_j=product_(ell|M)|R_j(ell)|. Output-linear CRT enumeration costs soft O(R_j), after the local descriptions and CRT weights are acquired.
3. Keep only progressions sigma=r+Mt meeting I_j. There are at most R_j progressions and each has length at most K=ceil(L/M).

Every true integer-square sigma survives. It is not necessary that all retained candidates be actual integer squares. Directly enumerating them and doing exact square/root tests costs soft O(sum_j R_j(1+L/M)), plus local setup and descriptions. This is a correct universal supplied-row consumer, but often worse than the inherited group query.

A better composition keeps the group acceleration. Write the original collision equation as

 gamma^E_j = q^sigma, q=gamma^(H²).

For the progression beginning at sigma_0=r+Mt_0, re-anchor to gamma^E_j q^(−sigma_0), and search against powers of the SINGLE common base q^M over its remaining length. Let G be the actual total number of nonempty progressions, including at most a constant factor from splits described below. The existing compressed monic collision routine then pays

 soft O(G+sqrt(G K)).

The full charged bound is therefore

 soft O(J sum_(ell|M) ell + sum_j R_j + G + sqrt(G ceil(L/M)) + setup/decoder).

The CRT output and progression anchors are explicitly charged; no unenumerated menu is free. Offsets/exponents have polynomial bit length in the inherited setting and are powered individually at soft O(G). Length truncation retains each progression's exact native endpoints.

As in the inherited consumer, remove the possible integer-zero annihilator before the group query: if E_j/H² is an integer in I_j, test its integer-root polynomial directly and return any factor; otherwise split its progression to omit that single index. A saturated selected leaf now gives a NONZERO exponent E_j−H²sigma and uses the inherited reviewed annihilator decoder. A proper local gcd already factors N. The true witness is preserved because if its exponent were zero, the preliminary exact root test would recover P instead.

This is an explicit paid discriminant-sieve/group-query candidate. It is not a claim that the displayed bound is soft m.

## 4. Quantitative outcome for ordinary CRT half-cuts

In the nondegenerate illustrative case, put delta approximately 2^(-omega(M)), so R_j approximately M delta and G approximately J M delta. The collision portion is

 soft O(J M delta + sqrt(J L delta)).

At J=m, L=m², reaching soft m would require roughly delta<=1/m, as well as J M delta<=soft m. A primorial with polynomially bounded M has omega(M)=O(log m/loglog m), hence delta=m^(-o(1)), not m^(-1). Choosing enough distinct prime cuts to make delta<=1/m makes the literal Cartesian CRT catalog superpolynomial in m before this consumer could use it.

This is a conclusion about this explicit construction, not a universal lower bound. Degenerate actual rows may make cuts weaker still; no uniform subpower saving is claimed from the illustrative approximation. The established hyperbolic sieve's subpower savings must not be renamed as a new acquisition result.

## 5. Why shared N and multiple rows have not supplied stronger cuts

At a common auxiliary modulus, every actual factor pair is parametrized by

 P=u, Q=N/u, u in (Z/MZ)*.

The entire vector of linear-form values is

 H²sigma_j−D_j=a_j u+C_j N/u.

This strongly compresses a JOINT vector description compared with treating its coordinates as independent. It does NOT remove any u from the initial unit menu. More critically, only the appropriate row is guaranteed to have an integral sigma_j in its native short interval. Intersecting all rows' short-interval or integrality promises is unjustified and can delete the real factor.

For two rows, knowing both sigma residues determines u and N/u when det[(a_i,C_i),(a_j,C_j)] is invertible. Those two sigma residues are themselves unacquired data. If coefficient vectors are proportional and their sigma coordinates are affinely identified, the character tests repeat one condition rather than yielding independent cuts. Taking a union across unrelated row targets generally enlarges local images, as the primary multi-target hyperbolic analysis quantifies.

A tempting stronger arithmetic congruence also disappears for primitive Gauss rows. A common factor g=gcd(a,C), if coprime to N, would force D−H²sigma=0 modg at a true root. But with u=Hc−sb, the lattice identity gives CN=Hu+as². After proper gcd handling, gcd(a,N)=1 and primitive Gauss reduction gives gcd(a,u)=1. Hence

 gcd(a,C)=gcd(a,H).

The putative modulus g already divides H and a, so D−H²sigma=0 modg is automatic. Dividing this content creates no extra restriction beyond the normalized discriminant above.

## 6. Primary sources and distinction from the new calculation

- Hittmeir, Integer factorization as subset-sum problem, arXiv:2205.10074v1: https://arxiv.org/abs/2205.10074 ; published primary DOI https://doi.org/10.1016/j.jnt.2023.02.010 . CRT output-linear construction and half-sized hyperbolic images are inherited tools. Their factoring application does not establish the requested one-sixth rate.
- Stanica--Mulder--Hittmeir, Multi-target hyperbolic sieves and elliptic trace obstructions, arXiv:2606.13018v2: https://arxiv.org/html/2606.13018v2 . Its union bounds and elliptic trace statements concern known auxiliary fields and multiple linear-form images; they do not acquire the actual hidden factor coordinate.
- Inherited repository probe: `scripts/probe_semiprime_sparse_residue_gauss.py`, `weighted_gauss`, `factor_sparse_catalog`, `_shared_collision` supply the integer-root identity and compressed group localization used here. The checkpoint's small-aux-literature and 624–626 handoffs record the prior sieve/linear-form limitation.

The new task-specific calculation here is stripping H² from the actual sigma-dependent discriminant, retaining its modulus-prime affine constraints, and composing an explicitly enumerated CRT mask with the existing common-base group query. No whole-family soft-m bound follows from the proved cost.
