# Product characters for the native odd-stride norm

2026-10-26. No improved complete prefix algorithm is proved. This pass uses the actual remaining point alphabet behind the odd-stride knot norm, tests a principal-alphabet product-character contraction, and gives a paid near-linear selected-shift branch valid with native known overlaps. It does not repeat the already archived Toeplitz/Schur far-boundary construction or Toda/moment identities.

## 1. Product character and the precise useful specialization

After the paid unit-class pruning, use the equivalent one-sided point polynomial

    F(T)=prod_(j=1..J)(T-x_j),  J=2L,
    x_j=beta^(E_j), E_j=a_j+b_j*N+lambda_j,
    q=beta^H, H=k², 0<=lambda_j<H.

The odd-stride K-norm and prod_(i=1..m)F(q^-i) have the previously proved identical zero predicates, with known-unit normalizations and squarefree multiplicity removal. No equality of their full scalar values is asserted here.

The rectangular supersymmetric Schur factorization is

    s_(m^J)(X/-Y)=prod_(j=1..J)prod_(i=1..m)(x_j-y_i),
    X=(x_1,...,x_J), Y=(q^-1,...,q^-m).                 (1)

Since J is even, this is exactly prod_i F(q^-i). Formula (1) is a polynomial identity and remains valid at collisions; it is not permission to invert cross differences. The rectangle has Jm boxes. Naming its character does not acquire its scalar evaluation.

**A concrete sufficient contraction:** suppose the point alphabet can be acquired as a small number B of complete q-strings

    X_b={c_b,c_b*q,...,c_b*q^(ell_b-1)}.

For one such string, the row/clock factors have exponent i+t, 1<=i<=m and 0<=t<ell_b. Their support is exactly the interval 1,...,m+ell_b-1. Therefore, for squarefree N, its zero predicate is preserved by the single scalar Pochhammer

    prod_(n=1..m+ell_b-1)(c_b*q^n-1).                  (2)

No collision denominator is introduced. Every selected factor maps back to an actual row/clock pair by choosing i+t=n, so label recovery is concrete. For a constant B and sum ell_b=O(J), scalar q-factorial baby/giant evaluation acquires the B products in soft O(J+sqrt m). Products, gcds and the existing consumer finish the prefix. This is an actual conditional acquired algorithm, not a character descriptor.

With many strings, their supports still require a paid batched interval evaluator; B comparable to J recovers the old soft O(J+sqrt(Jm)) scale. Thus a representation-theoretic specialization would be genuinely useful if it supplied a much smaller positive-support principal alphabet (or an equally explicit zero-preserving replacement), including starts, lengths, units and row labels.

## 2. Actual native alphabet: short strings, plus a paid hidden-neighbor branch

The principal-string hypothesis can be checked on this actual family rather than dismissed for arbitrary polynomials.

### Exact integer strings have length at most two

Write r_j=a_j+lambda_j, so E_j=b_j*N+r_j and -k<=r_j<H+k. If E_v-E_u=H, then

    (b_v-b_u)N=H-(r_v-r_u).

The right side has absolute value below 2H+2k, whereas the native hard branch has N>256k^4. Hence b_v=b_u. At a fixed b, the allowed r interval has width H+2k<2H. It cannot contain three values separated by H. Consequently every exact integer q-string in the full native exponent labels has length at most two. Deletions and subsequent pruning only shorten such strings. The previously proved primitive block a=1, positive b<k with bN=1 mod3 supplies Omega(k) distinct surviving exponent labels: different b values cannot coincide because their N spacing exceeds the entire phase range. Thus literal exponent deduplication does not turn this candidate into a sublinear number of strings.

This is a proof for the current a+bN+lambda catalogue. It is not a transfer of the older canonical-offset at-most-two-fiber theorem. Integer labels alone do not rule out local order wraparound, addressed by the next paid branch.

### Near-linear selected-shift screen without skipping known zero factors

This is an extension of the earlier selected-shift monic-evaluation screen, with derivative deflation for this unseparated native family. It should receive old screen credit, not be advertised as a new factoring bound.

First deduplicate identical **integer exponents** E. For zero/nonunit support this is safe (zero equivalence uses squarefree N), and opposite closure is preserved if whole opposite label classes are deduplicated together. Let the resulting monic point polynomial be D(T). Acquire D and D' in soft O(J). **Make the shift-zero separation screen mandatory:** evaluate D'(x_j) at every distinct integer label. A nonunit resolves by one scan omitting its own label, yielding a proper factor or a saturated nonzero relation beta^(E_j-E_t)=1. If this screen continues, all distinct remaining labels are distinct in each residue field, with every pair difference a unit. Thus the Omega(k) distinct native integer labels also supply Omega(k) distinct local points. Each label has at most one known integer successor E+H in this list. Set Q_j=q*x_j and compute the shift-one tests by monic multipoint evaluation

    v_j = D(Q_j),   if E_j+H is absent;
    v_j = D'(Q_j),  if E_j+H is present.                (3)

When the successor exists, Q_j is exactly its point in R, and D'(Q_j) is exactly the product of all the other root differences. This equality uses no division. Thus (3) omits only the one publicly known exact-zero factor; it does not silently skip an entire point that could also have hidden partners modulo a prime.

Take gcd(v_j,N). A proper gcd factors. At the first nonunit value with saturated gcd, scan D's original roots, excluding that known successor if present. Its product identity guarantees a nonunit leaf. A proper leaf gcd factors; a saturated leaf yields

    beta^(E_j+H-E_t)=1 mod N,
    E_j+H-E_t !=0 as an integer.                        (4)

The nonzero exponent has O(log N) bits and is passed to the already licensed global-annihilator consumer. All original root labels are retained. The one final scan costs O(J), so the complete branch costs soft O(J), plus the licensed extractor if invoked. Neither root separation nor a field polynomial gcd is assumed.

If **both mandatory screens** continue, the local roots are distinct, every local q-neighbor is exactly its known integer successor, and there are no additional local partners. Hence the surviving local point set also has only the length-at-most-two q-strings established above. A longer local chain would force consecutive known integer successors, contradicting the fixed-b interval bound. Multiple hidden representatives at a target do not evade this certificate: derivative deflation leaves all but the one exact successor in the tested product.

This can find a factor on favorable native inputs and gives an explicit certificate on the continuing branch. It does not prove that the branch always terminates. It also does not rule out two strings whose points lie within q-distance 2,...,m; such longer-distance overlap can merge their clock supports. Discovering enough of those useful distances is still the original missing sharing problem. No exclusion of all support-preserving character transformations is claimed.

The mandatory shift-zero screen also allows ordinary within-alphabet Vandermonde divisions on its continuing branch. It does not certify cross differences against the clock at collision points; those must remain polynomial rather than canceled. Both screens together still cost soft O(J). Shift one alone would not exclude isolated duplicate local roots and would not justify the strongest local-cardinality statement.

## 3. Colored Alexander one-hook scaling: a real theorem, a different operation

Primary: Andrey Morozov, Alexandr Popolitov and Alexander Sleptsov, *Direct proof of one-hook scaling property for Alexander polynomial from Reshetikhin–Turaev formalism*, [arXiv:2410.13676v2](https://arxiv.org/html/2410.13676v2), 2024-11-06, Theorem 1.1. It proves the normalized one-hook identity

    A_lambda(z)=K(z^|lambda|)

for knots. The proof obtains the one-hook R-matrix blocks directly; it is not merely the earlier eigenvalue-conjecture argument. The source explicitly warns that the statement fails in general for multicomponent links.

Thus each factor K(eta^(2i+1)) can be viewed as one-hook colored Alexander at eta. The theorem gives one evaluation with one index. It does not identify the product of different colors with the color of their tensor product or with one hook of total size. A knot-colored invariant is not a ring homomorphism from direct sums/tensor products to these normalized scalar products. Connected-sum multiplicativity would require acquiring the connected-sum/cabled object, which reintroduces the m factors.

A precise diagnostic against “replace all odd colors by the hook of total size” is already available among genuine genus-one Alexander polynomials. Let eta=16 modulo N=101*103; its local orders are 25 and 51, both odd. Let w=eta^7+eta^-7-2, a unit, choose the integer lift c=-w^-1 mod N, and take K(T)=1+c(T+T^-1-2), an integral symmetric polynomial normalized at 1. For m=3, the product K(eta^3)K(eta^5)K(eta^7) is zero globally, while the single-hook total size is 3+5+7=15 and K(eta^15) is a unit. Indeed equality of the relevant traces would force eta^8=1 or eta^22=1 locally, impossible for orders 25,51. This diagnostic is not claimed to be a native factoring instance or a lower bound; it falsifies only the proposed universal product-to-one-hook identity, even with odd local orders.

The existence of fixed-sequence selected-index algorithms cannot be transferred by calling these values “colors”: the acquired knot varies with J, and its degree-L coefficient data enter the sequence. An applicable theorem must explicitly include that growing data, rather than fixing the knot/recurrence before measuring m.

## 4. Supercharacters, Weyl denominators, and the remaining native requirement

Primary: E. M. Moens and J. Van der Jeugt, *A Determinantal Formula for Supersymmetric Schur Polynomials*, Journal of Algebraic Combinatorics 17 (2003), 283–307, DOI 10.1023/A:1025048821756, [primary fulltext](https://www.kurims.kyoto-u.ac.jp/EMIS/journals/JACO/Volume17_3/l66lh57578211177.fulltext.pdf), equations (1.10)–(1.12). The Sergeev–Pragacz factorization for a partition containing the full rectangle gives (1); the determinant identities combine Cauchy and Vandermonde factors. They are exact character identities, not complexity claims for this acquired specialization.

The old scalar-factorial report `/tmp/semiprime-scalar-native-20261023/scalar-factorial-constructor.md` already gives a J-by-J Toeplitz/Schur determinant with only 2J-1 far-boundary coefficients. Its unpaid far boundary is not made paid again by this paper's different character expression. First Schur/q-hook constants and selected initial coefficients were already acquired and are not new outputs of this pass.

The specific principal-alphabet algorithm (2) is therefore blocked by the actual remaining q-string structure after the paid screen, not by a generic-polynomial analogy. Its long-string savings would require a different, explicitly acquired alphabet transformation. Virtual alphabets can have negative multiplicities, but canceling a numerator/denominator root that is a local collision can erase the only witness. A proposed virtual/supercharacter transformation must either keep a positive-support replacement or resolve every canceled nonunit with the original consumer. Auxiliary roots of unity or topological-locus variables must not be identified with arithmetic q. No quantum-Frobenius threading theorem is used here.

A concrete sufficient remaining structure is a public construction of few positive-support geometric strings whose length-m clock unions cover the actual surviving witness and whose every selected point maps to an original nonzero exponent relation. Alternatively it could supply useful nonmetadata selected shifts in a soft O(J)-size batch; (3) completely consumes each supplied shift with known-successor deflation at cost soft O(J), but does not acquire which larger shifts matter. The primitive-content block and axes of the current family are not removed by these character identities.

## Cost and status

Acquiring the selected-shift tests, integer-label grouping and derivative data costs soft O(J). The one-hook and rectangular identities supply exact equations but no paid whole-family contraction beyond that branch. The complete worst-case prefix still costs soft O(J+sqrt(Jm)), with J=soft O(k), m=Theta(k^(3/2)); the target soft O(J+sqrt m) remains open. No full-rank expansion, canceled collision denominator, unacquired local order, or unproved fixed-knot complexity theorem has been counted as a fast scalar algorithm.

The single explicit one-hook-collapse diagnostic was also checked by exact modular arithmetic: N=10403, eta=16, c=5352 gives K(eta^3)=3693, K(eta^5)=9318, K(eta^7)=0 and K(eta^15)=4829 with gcd(4829,10403)=1. This is a convention/candidate falsification, not a native coverage or asymptotic experiment.
