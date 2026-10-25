# Multiplier/symbol recursion: exact zero masks and the unpaid terminal product

22 October2026. The doubling zero-mask identity is exact and requires NO plus-product acquisition: the prepared odd-order promise itself certifies those factors as units. It transfers the same mask to a squared base and squared target, but supplies neither a terminating base case nor a smaller native interval. No new soft-m simultaneous evaluator was obtained. The integer-wrap calculation below specifies the precise sparse family a multiplier implementation must retain.

Let R_e={0} union the nonzero e-quadratic residues modulo the odd public prime m, let S_e={r+mn:r∈R_e,0<=n<K}, D=K(m+1)/2, and write H_e(X;q)=product_(i∈S_e)(X−q^i). Native X and q belong to the common prepared subgroup of odd local orders. Distinctness of roots is unnecessary for the polynomial identities, though native local orders exceed the relevant interval lengths.

## Exact doubling and all zero-support branches

For every commutative ring,

    H_e(X²;q²)=(-1)^D H_e(X;q)H_e(−X;q).        (1)

Indeed (-X−q^i)(X−q^i)=−(X²−q^(2i)) for each factor. For either hidden prime, X/q^i has odd order. It cannot equal−1, which has order2. Therefore every X+q^i and the whole H_e(−X;q) are units. This includes ALL supplied native rows and every repeated doubling stage, because raising elements to2 preserves odd order and subgroup membership. Negative X is used only as the plus-factor argument, not assumed to have odd order.

Consequently, without numerically computing even one unit correction,

    gcd(H_e(X²;q²),N)>1 iff gcd(H_e(X;q),N)>1,

with EXACT agreement of the local prime-divisibility supports. The same equivalence holds for saturated/nonunit/unit classification, apart from unit scalar factors. Iterating,

    H_e(X^(2^h);q^(2^h))
      =(-1)^(hD) H_e(X;q)
         product_(s=0..h−1)H_e(−X^(2^s);q^(2^s)). (2)

All corrections are units. The exponent hD sign is correct because each successive equation multiplies by one(-1)^D. Thus any acquired terminal zero mask can be transferred back for FREE apart from logarithmic descriptor work. No square-root oracle or local order is needed for the forward iteration.

Equation(2) does not acquire the mask itself. At every h the root count is still D and the requested target count is still J. The local order of q^(2^h) equals that of q since it is odd, so repeated doubling does not make this orbit short. This is an exact statement about this recursion, not a lower bound against other algorithms. There is no supplied h for which the terminal products have become empty, degree-O(m), known units, or otherwise affordable.

## Plus corrections: exact acquisition cost and symbol meaning

Define the common plus polynomial P_e(X;q)=product_(i∈S_e)(X+q^i)=(-1)^D H_e(−X;q). Its values at native X are certified units. Generic simultaneous evaluation costs the existing soft O(J+sqrt(J*mK)) clock; unit safety does not make the actual unit values cheap. Explicitly building P_e has degree D~m², and independently evaluating J degree-one geometric products for each r or target is not the requested soft-m batch construction.

The earlier paid Cayley palette is different: its seed product at geometric parameter shifts shares one degree-one q-factorial and a literal sliding-window boundary update. Here the arbitrary native row X_j=gamma^E_j q^(−kappa_j) is not supplied as an affordable common short q-window of parameter shifts, and its large-mask roots remain the selected r+mn family. No common-plus-palette theorem is imported for P_e(X_j;q).

Ordinary Jacobi multiplicativity yields

    Jacobi(H_e(X²;q²),N)
      =Jacobi((-1)^D,N) Jacobi(H_e(X;q),N)
         Jacobi(H_e(−X;q),N).                    (3)

Its last factor is±1, not generally1; odd subgroup membership guarantees units, not a constant ordinary Jacobi symbol of sums. The full rational-denominator Gaussian quartic symbol of that last rational product IS1, but this simply recovers the Boolean zero-mask identity already certified without calculation. Fast reciprocity on explicit numerators cannot compute the implicit P_e value, and computing only its unit symbol cannot turn(3) into a terminal mask evaluation.

One could compute every P_e symbol after supplying its values, with logarithmic overhead per row, but this does not improve acquisition. No such symbol or product is charged as free here.

## Literal multiplier wraps: the seed intervals do not stay unchanged

For an integer a>=1 coprime to m, write for each0<=r<m

    a r=r'_r+m c_r,   0<=r'_r<m, c_r=floor(a r/m).

The residue map r→r'_r sends R_e bijectively onto R_(e Legendre(a,m)). But the ACTUAL exponent is

    a(r+mn)=r'_r+m(a n+c_r).                    (4)

Thus n' runs through the arithmetic progression c_r,c_r+a,...,c_r+a(K−1), not all consecutive n'=0,...,K−1. For doubling, c_r is0 or1, and n' has residue c_r modulo2. These residue-dependent parities survive even when Legendre(2,m) swaps the two outer palettes. Treating the two wrapped subsets as one consecutive K-block silently adds or removes Theta(mK) factors, not just O(m) boundary leaves.

Equivalently, keep the squared step q² and the original S_e exactly: that gives identity(1), with no wrap error but no shortening. Or keep q and accept the sparse interlaced index sets described by(4). Restoring a full consecutive range would require the complementary residue/parity products and their paid acquisition/localization. That extra product is not supplied by a root-of-unity identity, because q^m is not1 and is not assumed to have small order.

For a general multiplier a, generating every c_r and residue label costs soft O(m) for polynomial-size a, but those descriptors do not evaluate the interlaced products. For h repeated doublings, exponents X^(2^h),q^(2^h) can be generated with h squarings per target. This is soft O(Jh), so h must itself be polylogarithmic to meet the native soft-m clock; no unbounded iteration is hidden. A backwards square-root step would additionally need an acquired root with the correct original interval labels; an unknown global order is not used to select it.

## Sufficient genuinely new theorem needed

A successful multiplier recursion would specify a finite sequence of exact, unit-safe identities, a terminal family whose zero masks are acquired at paid cost, and a bound on TOTAL boundary/terminal work across all J targets. Identity(1) already transfers masks without any actual correction products, so acquiring those units alone is not the missing theorem. The missing part is a terminal acquisition or a real shrinking transformation that preserves the original exponent/interval ledger, including the residue-dependent carries in(4).

At present no such terminal identity was proved here. This report does not replace that missing construction by the old Cayley gauges, by an unknown-order square-root choice, or by a generic impossibility statement. It retains the exact forward mask recursion as potentially useful if a separate terminal evaluator is found.

Only this new scratch report was written. No repository edits, new norm classes, backend, examples, or subagents. All claims are direct finite-ring algebra; the earlier reciprocal-symbol report contains the primary explicit-input reciprocity audit and its limits.
