# Independent composite row / conductor-first contract review

24 October 2026. **PASS for corrected final bytes.** Reviewed `/tmp/semiprime-native-character-20261024/composite-row-contract.md`, SHA256 `66795af6eae4e0cde23b6e84a6beb7ae18a656e41bdf9f94d739c83f3cbccb74`. No source/repository edits or examples by this reviewer. The initial review requested one Kronecker-conductor precision, now incorporated; no other required correction remains.

## Conductor and public preprocessing

Selecting ell first from ell>=max(5,ceil(N^(1/6))+2), then k=ell-1, gives even k, N<=k^6 and the required sixth-root scale by Bertrand. Deterministic primality tests over O(k) candidates, public SPF/factor data, primitive-root exact-order tests over at most ell candidates, and one logarithm-table power walk all fit soft k including bit costs. These logs concern the public auxiliary field. No growing-progression prime theorem is assumed.

The explicit C>=N-1 branch has sqrt N<=4k+1 and is affordable. The surviving scalar preparation forces P,Q>C, so k,ell and their divisors are units modulo N. Small-input saturated gcds are routed to the affordable branch rather than inverted. Choosing this row modulus does not silently claim a Gauss-base order certificate.

## Composite size parameter and all preparation branches

Read the pinned original uniform setup in full. Its sections 1–5 allow an arbitrary integer size parameter; prime m is introduced only later for the old tag catalog. Thus the same scalar preparation at composite k is justified.

The HH/two-primary-removal/exact-order screen is correctly retained. In its exact common full-order branch r0>C, r0³>4096N and the monotonic factor-sum bound give P+Q<r0², permitting direct factor-sum recovery from the known order. The N-1 projection's local orders are coprime. Its exact-common-order-one branch supplies the short ORIGINAL-gamma annihilator N-1, so the pinned unbalanced extractor has its actual odd-large-order and polylog-bit premises. The q=beta^H screen is separately paid: exact common order one would force both already-large beta orders to divide H, impossible. No automatic composite-H order preservation is used.

Continuing beta and q therefore have exactly the stated guard certificates, and the global beta order exceeds 256H². No numerical hidden order or its factorization is supplied.

## Unit-tag source, coverage, deduplication and recovery

For unit j, a_j is a unit modulo k. With D_j=(N-a_j*j²)/k and centered b_j=-j^-1 D_j modulo k, f_j(j)=k(D_j+j*b_j) is divisible by H and f_j'(j)=k*b_j is divisible by k. Expanding at j+k*h proves divisibility for every integer h. The true P has a unit tag and is a unit modulo H, so the displayed I is integral and equation (1) is exact.

The centered envelope gives the stated delta/ell bounds. P,Q>16H make I positive; a_j<k, P<=k³ and Q<k⁴/16 give I<17H/16+1/2<2H+1. Thus L=2H+2 genuinely covers the original own source for any unit beta. No field arithmetic modulo k or two-preimage claim is needed.

Integer-delta deduplication preserves a representative original offset. Distinct offsets differ by at most 4H, below both local beta orders, so target differences are units in BOTH fields. q-seed separation follows from the independently acquired q guard. The unbalanced factor-sum bound and global-order margin reproduce original saturated-leaf recovery for every retained offset and i<4H, regardless of private tag. Changed transformations require their own nonzero short exponents, as stated.

## Coherent quarter and general content caution

The exact identity E_j=a_j*(j-1)²+k*(D_j+b_j) checks term by term. j and its inverse are odd, so D_j+b_j is even. Consequently FOUR divides E_j and H for every even k, including k=2 modulo 4. Quarter powers are directly acquired integer powers of the prepared odd-order beta.

Their factorization has two plus-companions, both units because a ratio in beta's local odd-order group cannot equal -1 (the squared ratio also has odd order). This remains true when the first difference vanishes. No companion norm is divided out. q=q_quarter^4, and oddness makes their local orders equal, so the actual q screen transfers. Distinct shortened target exponents remain below the same beta-order margin; raising a saturated quarter leaf to the fourth power gives the original bounded leaf. Degree/horizon are unchanged.

For d=gcd(j-1,k), j^-1=1 modulo d gives d|(D_j+b_j), hence d² divides both E_j and H. The report correctly treats odd extraction from this content as unsafe without an additional order-coprimality certificate. Power-of-two extraction is distinguished from those unsupported odd roots and from any index-range improvement.

## Composite fibers and character conductors

The inverse-square map's nonempty fibers are cosets of G[2], with the stated 2-primary counts 1,2,4 and one factor 2 per distinct odd prime. In particular a=1 can have many tags; no cheap independent-query claim for all of them is inserted. The old inverse-tag product congruence remains exact, but its prime-field nonzero consequence is correctly withdrawn over composite k.

Jacobi equality on k_odd is valid, while the complete square coset needs the individual odd-prime signs and the exact 2-part residue conditions. Those CRT unit-square conditions are sufficient and necessary, and the index discriminant is only a necessary descriptor at the even part; no inverse of 2a_j is taken there.

The corrected Kronecker paragraph is precise: failure to be a residue-mod-k function can occur at v2(k)=1, whose 2-character requires modulus 8. At v2(k)=2 that factor is squared/trivial; for larger odd valuations the required modulus 8 already divides k. The previous blanket modulus-4 warning has been removed.

## Packed Gauss signs, shared pairs and scalar components

The old general-k corrected histogram routine is applicable with this acquired ell=k+1 and all its exceptional projectors. Its cost includes the public log table, histograms, cyclic products and one length-k output. It does not supply all conjugate or all native row vectors for free.

For unit odd j the antipodal identity is g_j*g_-j=D=e0+ell*X^(k/2)*(1-e0), not the old odd-order signless specialization. The inverse, automorphism invariance and C_E*bar(C_E)=D^(E-1) for unit odd E all check. U=g_1^k and its inverse are legitimately acquired; no target value inverse is required.

Native Frobenius cancels the auxiliary phase using a_j*j=Ns modulo k, while retaining the same original integer I. Grade zero reveals no new index residue. One-row packed acquisition and the full k-by-k expansion have their actual different costs. Opposite carries give ell_j+ell_(k-j)=H*tau with tau in {-2,-1,0}; N+a_j is even, so the epsilon phase drops from D^(N+a_j). The three shared V_tau vectors and actual scalar multipliers therefore represent all pair products in soft k, including the correct e0 term. Pair products are units, not the sought shifted differences.

At augmentation every native T_j and q_G equals one, forcing all full cyclic difference norms to zero. This is explicitly treated as unusable. At X=-1 the quadratic Gauss square is (-1)^(k/2)*ell; E_j,H divisible by four remove that sign and yield exactly the scalar base ell² with quarter exponents. Its own equality follows because (Q-a_j)/2 is integral, but no beta order or saturated decoder is transferred to ell².

## Verdict scope

The contract acquires the conductor-first composite source, complete scalar preparation, coherent quarter inputs and phase-correct shared packed data with honest costs. Neither the pair/unit aggregate, the quadratic component nor the conductor supply acquires the long difference query. The complete original scalar query remains soft(J+sqrt(JL)), at most soft k^(3/2); no all-input sixth-rate or completed backend claim is made. Final corrected bytes pass.
