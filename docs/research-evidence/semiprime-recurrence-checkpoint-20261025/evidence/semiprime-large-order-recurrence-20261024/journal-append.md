
## 2026-10-24: rough torus orders and the initialized joint seed graph

The quadratic order supplier has a stronger paid variant: in soft k BIT
operations, return a factor or an actual norm-one W whose TWO local
orders have no prime factor <=k and exceed C=16k^2. Since H=k^2 has
only primes <=k, powering W by H leaves both orders unchanged. This is
a uniform preparation theorem on the continuing hard branch, not a
faster long-query theorem or a claim of coprimality across the primes.

Acquire the fully factored smooth-killing exponent

    E=prod_(prime ell<=k) ell^floor(log_ell(N+1)).

Its bit length is O(k log N), within soft k. The sieve, prime powers,
integer product tree and actual R^E powering are all charged. Replace
the previous odd projection by W=R^E, retaining the same selected
Cayley point outside both small M-kernels. Run the same ordered screen
on q=W^H through C. A successful screen gives the asserted rough
orders; a proper norm gcd factors. Otherwise the first nonunit leaf
gives a common exact projected order r<=C, and the RAW point R is
killed by the fully factored K=E H r. Trial factoring r costs soft k.
K is WIDE, with kappa=bitlength K=soft k; it is not handed to the
old short-annihilator beta decoder.

The expensive-looking raw order extraction is batched. For prime-power
leaves A_ell=ell^v_ell(K), build their product tree. At a node with
subtree product D, store R^(K/D). Send this value to each child by
powering it by the OTHER child's product. Thus every leaf acquires
S_ell=R^(K/A_ell). At one tree depth the total powering-exponent bit
length is O(kappa); all levels cost soft kappa. This established
complementary-exponent algorithm is credited to Celler--Leedham-Green
in [Sutherland's thesis, Section 7.4, Algorithm 7.3](https://math.mit.edu/~drew/sutherland-phd.pdf).
The claim here is its paid application with simultaneous unknown local
orders and the norm-gcd branch, not a new generic exponent algorithm.

For each leaf binary-search the threshold of
gcd(Norm(S_ell^(ell^e)-1),N). A unit means BOTH local valuations exceed
e, saturation means BOTH are at most e, and a proper value factors.
Initialize the threshold interval by -1 and v_ell(K), including the
possibility of valuation zero. Adjacent final bounds force the two
valuations equal; differing valuations necessarily expose a proper
factor. Summing actual exponent lengths over the leaves costs
O(kappa log log(N+2)) group operations, hence soft k bits. If no factor
appears, their product is the common exact raw order d. Although K was
wide, d divides both p-chi_D(p) and is therefore O(log N)-bit.

The earlier termination mechanism now applies without a hidden wide
powering cost: a common divisor >=k triggers the exact BOTH-sign AP
factor search through floor(sqrt N); otherwise lcm(M,d) at least
doubles M. O(log k) rounds still cost soft k. Nontrivial projected r
is itself k-rough, so r>k already forces the AP branch; only r=1 can
feed the below-k growth branch. All native rows are rebuilt using the
returned W and the actual beta-coupled seed screen is RERUN. Coverage,
norm labels and original same-leaf recovery are preserved. No N+1
projection, cross-prime coprimality or balanced coordinate profile is
inferred from this roughness result.

The direct recurrence experiment uses the genuinely acquired norm and
angle coordinates

    t=beta^(2H), v=W^H,
    n_j=beta^(2E_j), u_j=W^T_j.

At either prime, (n_j,u_j)=(t^i,v^i) is exactly the whole local original
row equality: odd beta order removes the square in the norm coordinate.
At the nonsplit prime the t and v orders are coprime and both >C, so
their joint trajectory has period >C^2. Its numerical period and the
hidden prime are not supplied as algorithm inputs.

For a block of b<=L=2H+2 indices, all t-node differences are units.
Acquire B_b(T)=prod_(a<b)(T-t^a) and the actual interpolant C_b(T)
with C_b(t^a)=v^a, degree<b, in soft b. The exact joint seed ideal is
(B_b(T),Y-C_b(T)). With n=b-1 the leading interpolation coefficient is

    prod_(r<n)(v-t^r) / prod_(r<n)(t^n-t^r).

The denominator is a certified unit. At the nonsplit side no numerator
factor vanishes: v!=1, and v=t^r for positive r<n would imply
t^(2r)=1, contrary to 2r<C. An actual norm-gcd of this coefficient
therefore either factors N or certifies a unit leading coefficient.
This PARTICULAR graph interpolant has exact degree b-1. It does not
rule out different implicit ideals or nonlinear recurrence algorithms.

For giant block g the actual shifted states are
(n_j t^(-bg),u_j v^(-bg)). There are J floor(L/b) such row states.
Acquiring them, evaluating the two same-state tests and handling the
literal final partial block costs soft(J+b+J L/b). Norm-node sharing
does not erase the angular row comparisons. The joint test is safe
even on the split side: at a matching norm node both angular values
are norm one, so zero difference norm means whole angular equality.
Saturated states are localized with their original row/index before
using the beta consumer. Products of the two tests over DIFFERENT
states are not substituted for this common-incidence operation.

Optimizing b returns the existing soft(J+sqrt(JL))=soft k^(3/2)
guarantee. Large order also implies that all nonsplit chi=+1 hits obey
the SAME integer relation delta_j-H i=constant and lie in a window of
at most five index values. This does not locate that window or ensure
that colour has any hit. For chi=-1, the two unknown local orders
impose a small-offset CRT relation; enumerating its possible offsets
does not acquire the indices. Neither restriction provides a faster
whole-family query.

Thus the stronger rough-order preparation is now paid, while the
specific initialized joint-graph continuation retains the old clock.
The required new operation remains an actual restricted common-index
contraction of the implicit row/block states, with valid original
factor recovery. The one-sixth factoring theorem and complete Lean
bit-cost composition remain open. No finite-instance campaign or new
backend formalization is offered as a substitute.

Sources and independent audits are in
`/tmp/semiprime-large-order-recurrence-20261024/`:

- [Rough-order supplier](/tmp/semiprime-large-order-recurrence-20261024/rough-torus-working.md), SHA256 `6333f318c8bc1c1e88a398aaeff94efb83b0d2e6ead3d64d455317b41036dcda`, and [independent review](/tmp/semiprime-large-order-recurrence-20261024/rough-torus-review.md).
- [Joint seed graph and actual continuation](/tmp/semiprime-large-order-recurrence-20261024/recurrence-followup-working.md), SHA256 `45c2f89d53d509bab46d43db3f2cc6d9f64e992c6748d4cc27a3df93268f41c1`, and [independent review](/tmp/semiprime-large-order-recurrence-20261024/recurrence-followup-review.md).
- The primary Sutherland PDF is cached at `sources/sutherland-phd.pdf`, SHA256 `5c326306358bd06f5f0ddb47fceb2b179ce29421222acde9094ef85681c0d20f`.
