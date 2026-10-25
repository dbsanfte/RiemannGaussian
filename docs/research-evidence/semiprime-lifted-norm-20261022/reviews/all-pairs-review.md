# Independent review: all-pairs lifted square-relation consumer

22 October2026. Reviewed /tmp/semiprime-common-product-20261022/lifted_relations/report.md and Bernstein's complete primary paper. Verdict: PASS as an unconditional acquisition/consumer theorem for the supplied native family. It does NOT prove that this family contains an actionable pair or establish an all-input factoring rate. No finite examples, backend, or repository edits were used.

## Algebra, units and exceptional inputs

The quotient identity gives ell²−4aN=m²Delta. With v=ell−m²kappa,

    v²−4aN=m²(Delta−2ell kappa)+m⁴kappa².

Since ell=−2aj modm and kappa=−Delta/(4aj), the first bracket vanishes modulo m. Thus z=(v²−4aN)/m³ is an EXACT integer, and v²=M z modN with the COMMON M=m³ for every row, irrespective of a. This is why different-a rows belong in the same batch. The scale estimates |v|=O(m³), |z|=O(m⁴) for a<=m,N=Theta(m⁶), and O(log N) descriptor bits are correct.

Standard preprocessing gives gcd(N,m)=1, and native a,j are units modulo m. Consequently v=−2aj modm is nonzero. The canonical |delta|<=3m² with delta=a+ell and |a|<=m gives |ell|<=4m², hence |v|<=m³+3m²<=4m⁴. Retained P,Q>16m² imply N>256m⁴, so 0<|v|<N. Therefore gcd(v,N) cannot be N: it is1 or a proper factor, which ends the algorithm. On the all-unit branch M is a unit and v²=M z implies that every z is a unit modulo N. In particular z≠0 as an integer. Alternatively z=0 would imply N|v², then N|v by squarefreeness, contradicting the bound.

Thus the positive-integer basis routine never receives0. Absolute value1 is allowed and has empty factorization. A saturated gcd in a later square-root comparison is NOT claimed as a factor or as a prepared-gamma annihilator: it is a trivial global-sign relation and the consumer continues. These roles must remain distinct.

## Primary coprime-base theorem really includes decomposition

Bernstein, *Factoring into coprimes in essentially linear time*, author version2004.04.04, permanent ID f32943f0bb67a9317d4021513f9eee5a:

- Algorithm18.1 and Theorem18.2 acquire the natural coprime base.
- Algorithm21.2 and Theorem21.3 acquire all input factorizations over that base.
- Algorithm20.1 explicitly outputs pairs(base,exponent), rather than merely a yes/no representation test.

The explicit M-time bounds in Sections8,18,21 are input logarithmic size times polynomial logarithmic factors times the cost multiplier mu. Fast integer multiplication, exact division and gcd allow polylogarithmic mu. Hence the claimed SOFT-linear specialization is justified by these bounds, rather than by silently equating the abstract b^(1+o(1)) wording with soft O(b).

Use the SET of distinct |z| values for the theorem, retaining row pointers and signs when deduplicating. Deterministic sorting/deduplication costs soft O(T), where T=sum_rows(1+log_2|z|)=O(m log N); identical rows must remain distinct metadata instances but need not be factored twice. The natural base B excludes1. Each base element divides an input, and product B divides the product of the distinct inputs (Theorem7.5), so the total base bit size is O(T). The source uses big integers of aggregate-bit scale T; it does not perform m² pairwise gcds of separate O(log N)-bit norm values.

Full primary PDF retained as bernstein-dcba-20040404.pdf, SHA256 49a78cd05264e3c0c544ef40d36b593218c422b2c02f8547ad8b6f44d71a0e46, from https://cr.yp.to/lineartime/dcba-20040404.pdf . DOI10.1016/j.jalgor.2004.04.009.

## Signatures and all output-size charges

Write |z_j|=product_b b^e_jb with pairwise coprime b>1. Test each base element for being an exact integer square. Define a row signature to be its sign sigma together with the ordered list of IDs of NONSQUARE b having odd e_jb.

Two rows have equal signatures iff z_i z_j is a positive integer square. Equal signs are necessary for positivity. On a given nonsquare b an odd total exponent leaves at least one odd prime valuation; that prime occurs in no other base element by coprimality, so cannot be canceled elsewhere. Even powers and arbitrary powers of square bases are squares. This proves both directions without prime factoring any b. D need not be squarefree.

For a row, the number of nonzero exponent incidences is at most log_2|z_j|; indeed each b>=2 and each nonzero exponent contributes at least1 to that logarithm. Thus there are O(T) incidences over the whole list. Base IDs and exponent encodings add only logarithmic factors. Square testing all bases, canonical ordering of incidence lists and deterministic lexicographic/radix grouping cost soft O(T), with no dense m-by-|B| parity matrix. Source decomposition output is used sparsely, not expanded into a quadratic table.

Within a signature class acquire D as the product of its listed nonsquare bases. It divides every |z_j| in the class, so D and each row's exact quotient have O(log N) bits. Set s_j=isqrt(|z_j|/D); the proved signature condition makes this exact and gives

    z_j=sigma D s_j².

Empty signatures use D=1. Product trees/exact division/square roots across all rows cost soft O(T). Check gcd(s_j,N) before inversion. In this branch it is provably1 because s_j² divides the unit z_j. A proper result would already factor; gcd N would contradict the retained unit contract and is not misreported as a proper factor.

## Representative comparisons are complete over ALL pairs

Put r_j=v_j/s_j modN. Every member of a class satisfies

    r_j²=M sigma D modN,

with a UNIT right-hand side. Choose any one representative r_0, and test gcd(r_j−r_0,N) and gcd(r_j+r_0,N) for every other row. At each odd local prime, the only roots of this nonzero square are ±r_0. Thus the two local signs either agree, giving r_j=+r_0 or−r_0 globally, or disagree, giving proper scalar gcds. The saturated outputs in the agreeing cases are legitimate trivial comparisons. Both plus and minus gcds cannot be N because2r_0 is a unit.

If no representative comparison returns a proper factor, every r_j is globally ±r_0. Consequently every pair is globally equal up to sign and is trivial. Contrapositively, ANY actionable pair forces an actionable representative comparison. This is an exact completeness proof, not a random representative heuristic. Repeated identical rows and the explicit v,−v pair only give the predicted trivial signs and do not create false positives.

For clarity this also matches the usual two-row product construction. If z_i z_j=W² with W=D s_i s_j, then

    X=v_i v_j, Y=M W

satisfy X²=Y² modN. Since r_j²=M sigma D, the gcds of X±Y are, up to multiplication by units and exchange of signs when sigma=−1, exactly those of r_i±r_j. Therefore the consumer screens every actionable two-row integer-square-product dependency in the supplied family, not just a more restrictive same-a subset. It does not assert completeness for pairs whose integer norm product is nonsquare, arbitrary higher dependencies, or other uses of these values.

There are O(m) representative comparisons and modular inversions. Each has O(log N)-bit operands; all earlier work is soft O(T)=soft O(m) in the retained regime. The algorithm returns a certified proper factor, or certifies that no supplied two-row square-product relation is actionable through this standard congruence-of-squares construction.

## Acquisition versus existence

The list, its coprime-base decomposition, exact square-class grouping and complete actionable-pair screen are genuinely ACQUIRED at the stated cost. No prime-factor oracle, hidden local root or sparse-nullspace algorithm is an input. Universal existence of a useful signature class with mixed local root signs remains OPEN. Neither the cubic lift nor the size bound proves it, and the consumer's no-actionable-pair output is a valid possible result under the current theorem.

Only this new independent-review file and the primary source copy/text were written in the allocated scratch reviews directory. No source-report or repository edits.
