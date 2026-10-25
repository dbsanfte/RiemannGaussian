
## Coarse residue output and controlled quadratic blocks, 2026-10-24

This pass weakens the output required from acquisition and constructs an
actual family adapted to that output. A supplied residue P mod m with
m>=N^(1/12) permits deterministic factor recovery in soft N^(1/6), with
all interval enumeration and lattice bit costs paid. A prime-cube modulus
supplies such an m and gives exact quadratic-phase blocks of native rows,
with only bounded, acquired index shifts. Their present shared evaluator
still costs soft k^(3/2). Neither the coarse residue nor a faster whole
query has been acquired. The all-semiprime sixth-rate and full executable
Lean bit proof remain open. Scratch proofs/reviews/validator:
`/tmp/semiprime-partial-tag-20261024/`.

### Classical small roots give an explicitly paid coarse-tag completion

For public gcd(m,N)=1 and a candidate c in [0,m), there is a deterministic
bounded attempt of bit cost soft(1+N^(1/4)/m). It returns a verified factor
whenever c is the smaller prime P modulo m; wrong c still has the same
cost bound and can return only a verified factor or failure. This uses
univariate unknown-divisor small roots plus PAID high-interval enumeration,
not the previously rejected claim that one-sixth known bits alone imply
polynomial-time factoring.

Here is the fully initialized construction. Put n=ceil log2 N. Enumerate
dyadic bins [2^b,2^(b+1)-1], clipped at floor sqrt N, b=1,...,floor(n/2),
and beta=b/n. Compute with integer powers/roots

    R_b=N^(beta²)                 (proof notation only),
    T_b=floor(root_(n²)(N^(b²))),
    X_b=max(1,floor(T_b/16)).

For each bin enumerate the actual integers s with c+ms in that bin,
in blocks of at most X_b consecutive s-values starting S0. If X_b=1,
test the candidate gcd directly. Otherwise set z=s-S0 and acquire the
monic f(z)=z+[m^-1(c+mS0)]_N. A promised block has an actual root
0<=z0<X_b modulo P>=2^b>=N^beta.

Use lattice dimension d=n and multiplicity t=b, with basis polynomials
N^(t-i) f^i for i<t and z^a f^t for a<d-t, scaling coefficient column
h by X_b^h. Its determinant is

    N^[t(t+1)/2] X_b^[d(d-1)/2].

All entries have polynomial(log N) bit size. Deterministic LLL returns
a nonzero integer polynomial H of degree <n whose absolute value at
z0 is bounded by sqrt(n) 2^[(n-1)/4] det^(1/n). Since X_b<=R_b/16 when
X_b>=2, this is strictly below N^(beta*t)<=P^t. Each basis polynomial
vanishes modulo P^t, so H(z0)=0 over the integers. Deterministic integer
root isolation and candidate gcd checks have polynomial(log N) bit cost.
The source gives an exact integer certificate for the strict norm bound.

The rounding bounds X_b>=R_b/64 and
2^b/R_b<=sqrt(2)N^(1/4) show that each bin has
O(1+N^(1/4)/m) blocks. All bins cost only a further logarithm. This is
also the epsilon=1/ceil(log2 N) specialization of May's Theorem 6/7,
whose runtime charges 1/epsilon; no fixed N^epsilon loss is hidden.
The primary dissertation and an independent finite lattice proof are
retained in partial-tag.md. This is an integration of the classical
decoder, not a new small-root theorem.

Consequently the weak readout may return just A,B with A nonzero at the
good nonsplit P and B/A=[j*]_m=P mod m, provided m|k. Existing norm and
coordinate gcds give a factor or a global scalar. A paid integer interval
query of length m extracts c, or factors, in soft sqrt m work. The decoder
then costs soft(1+N^(1/4)/m). The entire consumer fits soft k when
k is at sixth-root scale and m>=N^(1/12). Repeated labels are intentional;
the exact original row or grid index need not be acquired.

### Supply a suitable divisor and rebuild the native family

Let K0=ceil N^(1/6), c0 the known negative fundamental conductor, and
B0=bit_length(2N)^33 from the existing orientation palette. Its conductor
bound c0=O(N^(5/32) B0²), known factorization and explicit QRH orientation
condition remain in force. Set Kmax=125K0 and FIRST run the actual common
small-factor prefix through 16 Kmax², with its bounded finite-input
fallback. This costs soft K0 and certifies P,Q>16k² for every later label.

Require c0<=K0/128 and let T be the least integer with 2c0 T³>=K0;
also require T>B0. Acquire primes in (T,2T) and (2T,4T). Only one old
conductor prime can exceed B0, so at least one of these two primes r is
coprime to c0. The public sieve, tests and factorizations are paid. Set

    d0=2c0, k=d0 r³, m=d0 r², H=k².

Then K0<=k<125K0, m|k, m³=d0 H, m>=k^(2/3), and k/m=r<=k^(1/3).
All factors are supplied. Every unit class modulo m has exactly r unit
lifts modulo k of the same character colour. This is a genuine acquired
divisor of k, rather than a smoothness promise on the old modulus.

Rebuild the scalar/torus rough bases, native rows, parity repair and the
ACTUAL coupled q=(beta W)^H screen through 16H at this new k. Their
proved composite-modulus hypotheses persist. The guards eventually hold
uniformly over the old polylogarithmic palette because 1/6-5/32=1/96;
finite and analytic exceptions retain the previous bounded whole-algorithm
fallback. The unknown smaller-nonsplit orientation is still conditional.

Prime cubes require care: arbitrary delta fibres can now have O(r B0²)
members, and the old constant/polylogarithmic PLUS-collision and auxiliary
ideal-width claims do NOT transfer. Needed factor-or-unit separation has
a different soft-k proof. Sort/deduplicate actual global root coordinates,
form F and evaluate F' at all roots. Any nonunit derivative localizes one
nonunit pair difference in one further soft-k scan. A globally nonzero
difference with saturated norm yields a proper coordinate gcd on the
nonsplit side. Otherwise every difference is a certified unit. No
quadratic pair array or growing fibre scan is required.

The exact-one MINUS argument remains valid for arbitrary even k: a hit
forces A P+Q+ell-Hi=0 by the coprime local-order product exceeding
256H². The original quadratic expansion then gives
A(P-j)²+k b'(P-j)=0 mod k². Comparing valuations at every prime divisor
of k forces k|(P-j), including valuation three at r. The own index is
positive and below 3H+2. No PLUS-fibre estimate is used in this argument.

### Exact quadratic phases with paid, bounded index shifts

Canonical parity repair has the particularly simple identity

    A_j=[N j^-2]_(2k).

Because m² is divisible by 2k, in each coarse class j=j0+mt the repaired
A-values form exactly one arithmetic progression

    A_h=A_c+2mh,  0<=h<r,  0<A_c<2m,

in an acquired permutation of the original tags. Take its A_c row,
the actual lift J0, and s0=A_c J0 mod H. The unit s0 satisfies
s0²=NA_c mod H. With inverses only modulo the PUBLIC integer H, put

    s(h)=s0+m N s0^-1 h-(m²/2)N²s0^-3 h² mod H.

There is no inverse of two: m²/2 is an integer. Direct squaring gives
s(h)²=N(A_c+2mh) mod H because m³=d0 H and H divides m^4/4. Moreover
j_h=s(h) A_h^-1 mod k permutes the original coarse class. The actual
lift and s(h) agree modulo k; their remaining difference is 0 or H/2
mod H, so multiplication by -2 removes the two-adic ambiguity.

Center the three coefficients of -2s(h) modulo H and call them
ell0,ell1,ell2. Set ellhat(h)=ell0+ell1 h+ell2 h² and acquire the exact
integer d_h=(ellhat(h)-ell_native,h)/H. With pi=beta W and barpi=beta/W,

    q^d_h V_h=C_c D_c^h E_c^(h²),
    C_c=pi^ell0 barpi^(N+A_c),
    D_c=pi^ell1 barpi^(2m), E_c=pi^ell2.

This is an equality in the actual global quadratic algebra, with all
starts, permutations and carries acquired in soft k. Choose
U=r²+r+12, e_h=U+d_h in [0,2U], and use shifted roots
Vhat_h=q^U C_c D_c^h E_c^(h²)=q^e_h V_h over
Lnew=3H+2+2U<4H. This OVERCOVERS the original intervals. Each leaf maps
to its known original integer index i-e_h in [-2U,3H+2+2U).
The same native order margin still gives the unique own MINUS hit on
this extended range. For a saturated leaf the scalar exponent is nonzero,
and global scalar order >256H² divides S-(P+Q) with
|S-(P+Q)|<7H²; hence the original factor-sum conclusion still follows.
This explicitly pays for extended indices rather than borrowing an
unbounded outside-index decoder.

### Execute the coarse-class readout; retain the unresolved cost

Keep ALL r canonical rows in every class, including any shifted nonhit
aliases. No interpolation or root separation is required for this reset.
Original-root separation does not certify shifted-root separation. A later
algorithm that needs it must rerun the actual separator, and any deduplication
then requires recalculating class sizes and degree formulas.

For the full class products F_c, acquire

    F=prod_c F_c, H0=sum_c F/F_c, H1=sum_c c F/F_c.

All coefficients cost soft k; deg F=J and deg H0=J-r. At the good grid
hit, H0 is nonzero and H1/H0 is its coarse label. The initialized reset
(Z,A,B)=(1,0,0), with step
(FZ, FA+H0 Z, FB+H1 Z), therefore gives the required local ratio.

An actually constructed b-step polynomial block still has diagonal degree
Jb. Its A entry has degree Jb-r and, for dyadic b, a unit leading
coefficient proportional to sum_(t<b)q^(-rt). Thus the explicit blocked
execution, with every giant value and tail paid, remains
soft(Jb+Lnew/b+J), optimized to soft k^(3/2). Neither the off-diagonal
degree saving nor the quadratic phase has supplied a faster terminal
contraction. The even/odd class recursion builds F_c cheaply but retains
both child queries. The successive phase ratio D_c E_c^(2h+1) retains
barpi^(2m); it is not a supplied fixed q shift.

The concrete next target is a shared zero-safe query on THESE acquired
quadratic-phase blocks that returns only the coarse class. A future
soft-k acquisition would have a fully paid soft-k completion, retaining
the orientation condition where used. The present pass supplies the
family, weaker output and completion, not the missing acquisition bound.

Exact source SHA256 pins: partial-tag.md
`79da1b9032b30777bd940709277f1687d47c51c5df431eb0d753168cdcfbd9cb`;
modulus-supplier.md
`91c4e5e0f8b0c84cb9a5eca349191c5728b0566af77f20444e9da335c6451387`;
residue-block.md
`359dba948c766eea58d9b6f2e556a851d0e1354fb860126122afacb842e4d7f9`.
No sample campaign, backend-only lemma expansion, or improved factoring
exponent is claimed. All earlier prefixes and frozen evidence are preserved.
