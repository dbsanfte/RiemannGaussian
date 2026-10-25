# Independent implementation review: composite-colour metadata

22 October 2026. Reviewer: residue_trace_acquisition agent. PASS for the documented public metadata scope; no correction request and no edits to reviewed files. This is not a review establishing a universal factoring algorithm.

Reviewed byte-identical files and SHA256:

- composite_colours.py: f242c896cc78447a529db84e9f7a000a7ce39cac7b1bf1df68c57bbed9c3c0cf
- test_composite_colours.py: e0141aa8c90bee26107e84f9af364beda94d18a6c95e3274e0b4dbd2a90e31fd
- README-composite-colours.md: 291cf3d91ff955355e86e210ef2d64de75ed137c5e0703316374951e844761b1

Ran the requested focused suite once: `python3 -m unittest -v test_composite_colours.py` in the implementation directory. All five groups passed. These bounded tests check conventions, exact identities, and exceptional inputs; they are not statistical family evidence or a runtime benchmark.

## Exact root, selector and public screens

For every positive integer N, the initial hi in ceil_sixth_root has hi^6>N, and binary search retains lo^6<N≤hi^6 until consecutive integers remain. The N=1 endpoint also returns one correctly. Exact sixth powers and adjacent inputs are handled without floating point. preprocess restricts its integrated domain to odd N>=3, so u>=2 and the chosen ell yields m>=3; the helper auxiliary_prime also has its stated positive-integer domain through the root routine.

The Eratosthenes sieve is correct on every interval size used here (at least eight). Each search round scans ALL admissible integers strictly above the fixed threshold 2u and returns the first flagged 3-mod-4 prime. Resieving previous portions on a doubled limit cannot skip an earlier prime. The final limit is O(ell), and the geometric sum of all sieve work is soft O(ell). Existence and ell=O(u) use the separately audited fixed-modulus AP-prime theorem, not an empirical stopping cap. Then m=(ell−1)/2 is odd and m>=u, hence m^6>=N.

The factors used by screen_public_primes are known primes from exact trial factorization of m plus the prime ell. Every nontrivial screen is proper for a composite N, even if a combined gcd would equal N. N equal to a screened prime is accurately reported as INPUT_EQUALS_PUBLIC_PRIME; the function does not falsely call N a proper factor. For small semiprimes (including the N=15,m=15 saturation control), individual screening is still correct. The implementation expressly does not certify semiprimality or the external prepared-order promises.

## Full unit rows and exact colour

canonical_rows enumerates every j in (Z/m)^* exactly once. Under gcd(N,m)=1, a=Nj^−2 is also a unit. The chosen b is the unique centered representative of ((a j²−N)/m)j^−1 modm, so c=(N+jm b−j²a)/m² is integral. All inverses exist, including 4aj since m is odd. The cubic v identity is an exact integer divisibility assertion, not an approximate root check.

Completing the square in (a h²+b h+c)/j gives kappa+(a/j)(h+b/(2a))². The stored colour is Legendre((4aj)^−1,p), which equals Legendre(a/j,p) because their ratio is (2a)^−2. Thus the colour code is correct although its expression differs from the usual lambda=a/j. This equality holds separately at every odd prime divisor, which is required for composite m. The canonical image test includes prime powers and nonunit square residues. The independently implemented aggregate row descriptors also matched a,b,ell,E in the coordinated aggregate controls.

## CRT palettes, nonunits and charged materialization

At each p^e, the code marks every t² modp^e for 0<=t<p^e. Multiplying this COMPLETE square set by a fixed unit nonsquare nu gives exactly the other unit-square-class multiple, including all even-valuation nonunit strata and zero. The class of a unit multiplier modulo p determines its square class modulo p^e (odd-prime unit Hensel lifting), so these two lists suffice. One must not replace these lists by unit quadratic residues plus zero when e>1; the code correctly does not do that.

The incremental CRT expression is correct since the preceding modulus is coprime to the new prime power. It creates each residue once within each colour tuple. Zero occurring in multiple colours is intentional, not a duplicate within one palette. Every final palette is actually materialized and sorted; there is no free implicit output.

For n=p^e the local coloured count is t_n=2+sum_{0<=v<e, v even} phi(p^(e−v)). Equivalently t_n=2 times the number of squares, and t_n<=n(1+1/p). Hence final descriptor count T=product t_n <=m product_{p|m}(1+1/p)<=m H_m<=m(1+log m). Each local t_n>=4. Thus the total incremental CRT pair visits are bounded by T(1+1/4+1/16+...)<2T, including a single-factor case. Sum of distinct prime-power scan lengths is at most their product m. Sorting, exact CRT arithmetic, and row inverses/Legendre powers contribute polylogarithmic factors. Trial factorization costs only soft sqrt(m), within the claimed soft m envelope. No loop here visits m residues for each of 2^omega(m) colours.

## Limits verified against README

The output is the complete public colour catalog plus canonical unit rows and scalar descriptors. The ledger truthfully reports zero long-H evaluations. The hidden-factor inequality 13<I<(17/16)m²+3<4m² is cited as an EXTERNAL retained-branch theorem; this implementation neither checks it nor treats its deliberately small algebraic test inputs as satisfying large-order/prepared-gamma promises. Original gamma preparation, source recovery, and simultaneous long-product evaluation remain external. The reference's complexity is an arithmetic/fast-bit ledger, not a formal certification of CPython multiplication speed. These qualifications are appropriate and sufficient for this metadata implementation.
