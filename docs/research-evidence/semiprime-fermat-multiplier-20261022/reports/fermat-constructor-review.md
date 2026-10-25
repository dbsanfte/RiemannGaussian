# Independent implementation and consumer review

22 October 2026. Reviewed `scripts/probe_semiprime_fermat_multiplier_cover.py` in `/home/dbsanfte/riemann/formal`. PASS for the stated public cover-constructor and algebra-check scope. No code edits were needed. This review does not certify a soft-r collision evaluator or a factoring algorithm.

## Packed convolution and bit costs

At lines59–68 the digit width is `ceil(bit_length(size)/8)` bytes. Thus radix `256^width` is strictly greater than size, including size=256 and size=65536. Every ordinary convolution coefficient is at most size, so there are no digit carries. A product of two size-digit words needs at most `2*size−1` digits; the fixed `to_bytes` length is sufficient even when the top digit is nonzero. Folding ordinary coefficients i and i+size gives exactly cyclic convolution modulo X^size−1, with no orientation reversal.

Packing uses fixed-width byte encodings, one `bytes.join`, and GMP import; unpacking slices one fixed-width digit at a time. It does not perform size repeated shifts or additions of growing packed integers. These passes cost O(size*width) byte/bit-copy work, with O(size log size) packed bits. The one GMP multiplication is the intended fast integer-multiplication kernel. The use of lists, binary coefficient checks, output digit arrays and Python integer metadata adds at most polylogarithmic factors. The code therefore realizes the claimed soft-linear convolution arithmetic, rather than merely documenting a faster kernel than the one used.

Sieve primality verification, all quotient powers, image/representative storage, maximum scans, explicit removals and catalog construction are charged. Their bounds are soft O(r), multiplied by the proved polylogarithmic number of rounds. The program uses no probabilistic primality shortcut and does not require a supplied primitive root.

## Finite image bound and greedy orientation

Let pi count primes strictly below r. For those primes, let n_a count quotient value a. The exact prime-ratio argument in Ostafe–Shparlinski gives sum n_a^2 <= pi+r−2: diagonal pairs account for pi, and each nonidentity Teichmuller ratio permits at most one ordered unequal-prime pair. Cauchy gives pi^2 <= d*sum n_a^2 <= d(pi+r−2), where d is the full nonzero-input image size. Thus the finite check at lines90–91 is valid for every odd prime r; it is not an empirical density substitute. Removing input0 changes no image because q_r(0)=q_r(1)=0.

The cyclic convolution at line97 gives score(tau)=sum_q 1_U(tau−q), exactly the removed set in lines104–109. Its maximum satisfies r*score>=remaining*d, and the code checks both this bound and equality with the actual removal count. It cannot select a previously used tau while uncovered points remain. The round bound `ceil(r/d)*(bit_length(r)+1)` safely exceeds `(r/d)*(ln r+1)`, so geometric shrink forces zero remaining points before that bound. The image theorem supplies d=Omega(r/log^2 r), hence O(log^3 r) rounds. Its unknown asymptotic threshold does not affect algorithm totality: actual d and an exact finite round bound control execution.

## Catalog, witnesses and selected-pair bijection

The catalog loop order is shift-major and then increasing j. The lift j^r has residue j modulo r and Fermat quotient zero; multiplication by 1−r*tau gives quotient tau, with the correct sign. Those two invariants determine a unit modulo r^2, so catalog entries are distinct across (tau,j). Every witness t=(tau−q_r(c)) has 1<=c<r. The `locate_multiple` index uses the correct j=c*x mod r and thus retrieves c*x mod r^2.

For each witness t and each j, mapping its catalog row s to x=s/c mod r^2 produces a unit with q_r(x)=t. Different t give disjoint quotient fibers and j ranges through each fiber once. Thus the selected labeled pairs represent exactly r(r−1) units, bijectively. This proves coverage while retaining the missing multiplier label; it does not reduce the labeled collision family to soft-r size.

`build_cover` takes r alone. `locate_multiple` is explicitly restricted to a known value and computes its quotient directly. It is not callable on an unknown factor without acquiring that factor's quotient. The constructor therefore contains no hidden-factor oracle.

## Independent checks run

Used `/home/dbsanfte/riemann/.venv/bin/python -B`, with GMP6.3.0. System Python lacks gmpy2; the repository virtual environment supplies the dependency. Independent all-ones convolution checks used sizes254,255,256,257,65535,65536,65537; expected cyclic output is the constant size. Single wrap impulses at size255,256,257,65536 checked the wrap index independently. At auxiliary primes3,5,7,43,101,257, independently counted prime-quotient energy and verified the exact finite image inequality, witness identities, catalog distinctness and round bounds. All17 grouped checks passed. These are algebra/radix checks, not a native semiprime coverage campaign or an asymptotic timing benchmark.

## Balanced linear collision recovery: strongest inherited decoder suffices

Read the inherited `semiprime-unbalanced-annihilator-20261016/reports/uniform-setup-and-query-interface.md`, including its paid setup and bounded-global-leaf method. Set m=r. Its surviving base beta has local odd orders>16r^2 and global order D>256r^4. It also already certifies short seed-order promises for q=beta^(r^2).

Assume the balanced branch P,Q<=2r^3, N<=r^6. For the public rows

    H=r^2,
    b=center(−N/s mod H), |b|<=H/2,
    d=(N+s*b)/H,

coverage at cP=s+Hh gives H*sigma=b*c+Q. Therefore |sigma|<2.5r, so a common searched interval |sigma|<=3r is safe. The true local collision is beta^(N+b*c)=q^sigma mod P.

Now take ANY globally colliding public leaf with 1<=c<r and |sigma|<=3r, whether or not it is the private coverage witness. Let K=N+b*c−H*sigma. Global equality gives D|K, and Euler's theorem gives D|phi(N)=N−(P+Q−1). Hence

    D | P+Q−1+b*c−H*sigma.

The absolute value is strictly below

    4r^3 + r^3/2 + 3r^3 = 7.5r^3 < 256r^4 < D.

It is therefore zero, and

    P+Q = 1+H*sigma−b*c.

The inherited exact square-root factor-sum decoder recovers P,Q. A proper local leaf gcd already factors. Thus a restriction-safe collision query has complete leaf recovery without requiring sigma uniqueness from a local q order, a true-pair promise at the chosen leaf, or a new annihilator theorem. This is the inherited bounded-decoder argument instantiated with the new exponent band, not a new decoder theorem.

For completeness, the inherited nonzero-polylog-bit annihilator extractor would also apply with gamma=beta and K if needed; the bounded factor-sum identity is stronger and avoids that invocation. Both are classical paper-level interfaces, not an assertion that an executable or Lean bit backend has been integrated.

A future fast query must still justify its own arithmetic assumptions. In particular, giant exponents b*c vary over an O(r^3) band, so pairwise giant differences are NOT automatically units from the local beta-order lower bound16r^2. Monic product/remainder arithmetic can handle repeated nodes and zero divisors without point-difference inversions; algorithms using stronger interpolation promises must establish them separately. No such query is acquired by this review.
