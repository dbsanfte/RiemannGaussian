# Complete bit-complexity argument to audit

Status: candidate argument, pending independent adversarial review and complete
kernel-level execution composition. This document must not be cited as an already
verified end-to-end runtime theorem. It identifies a concrete algorithm and the
remaining correspondences to check, rather than postulating a fast counter.

## Algorithm and size conventions

The input is an integer N>=2 in binary, of length L. Construct the public typed
macro multiplication graph from MacroParameters/PublicFactorCount, with its actual
ordered local 0/1 tables. Let n be its Boolean edge count, F its number of factors,
M its total incidence and w its maximum scope. Then L<=n<=6400L, M=2n,
w<=512L^(3/4), and F is polynomial in L (indeed the explicit graph counts are
linear in n). This n is not the macro FFT word length.

Compute lambda=ceil(log2 n), nu=ceil(log2 lambda),
r=floor(sqrt(lambda))/nu^2, Q=floor(lambda/(128nu)),
R=4ceil(sqrt(lambda)), epsilon=1/(r lambda). Test the exact integer guards
implemented in source_parameters.py. If they fail, use ordinary trial division.
On acceptance construct the complete-bucket source layout, retaining actual
integer measurement rows. Evaluate the streamed exact counter, and recover an
ordinary factor using at most L+1 restrictions on original input ports. Check
the final integer product and proper-divisor condition. Public graph coverage,
uniqueness and restriction/count recovery provide the correctness specification.

The executable Python modules are a concrete implementation reference. This
argument concerns the explicitly described finite algorithms and typed public
graph; it does not silently assert a verified compiler-ID isomorphism between
the Python graph builder and every Lean graph identifier.

## 1. Construction work and scalar size

Under the schedule, D=r^(2Q) has D^2<=2n^(1/64). Each finite universal word,
matrix or bucket table has polynomially many entries. Trying every candidate
word and recomputing conditional incidence/head energies requires polynomially
many arithmetic steps in n,D,Q,R,F. The pairwise expectation formulas use only
the denominators r, r^Q and those of epsilon and the displayed potential weights;
their products are shared within each finite potential sum. Each potential
therefore has polynomial binary numerator/denominator length. A sum of
polynomially many such terms does not acquire an unrelated new denominator per
term. This assertion needs to be checked against every exact conditional-score
formula, including partially assigned tables.

The binomial system has dimension R and entries bounded by 2^(Q+R), with signed
unit right-hand side. The universal integer operator is a sum of at most 3^Q
terms, each a binomial-system coefficient times a power of two. Since r>=2,
3^Q<=r^(2Q)=D; hence this literal expansion is polynomial-size. Its integer
partial sums have polynomial bit length. Interpolation multiplies at most Q
linear factors whose nonzero integer denominators divide Q!, so all intermediate
polynomials also have polynomial coefficient bit length. Complete copies and
owner-fibre summation preserve this property.

For exact elimination/row selection, use polynomial rational Gaussian
elimination. After a fixed ordered sequence of pivots, each completed
Schur-complement entry is a ratio of bordered minors of the original permuted
integer matrix. Every minor of order k has absolute value <=k!A^k if the
original entries have absolute value <=A. This bounds completed stored basis
rows and the Gauss-Jordan solve. It does NOT give the same tight bound for every
partial scratch row in the sorted-pivot row selector. For those partial rows,
retain the product of the common denominators of the at most k stored basis
rows already subtracted. Each elimination step multiplies this denominator
by at most the next stored-row denominator and increases its numerator by the
corresponding bounded multiplication/subtraction. This gives the looser
O(k^2*(log(A+1)+log(s+t+1))+inputbits) bound, still polynomial. Raw arithmetic
temporaries have a fixed multiple of these operand lengths. No minor is
enumerated by the algorithm; the determinant expansion is only a height proof.

The original-row selector's sorted pivot list must be explicitly checked against
this invariant. New pivot columns can precede older pivots, but older rows then
have zero at that new column; the new row has already eliminated all older pivot
columns. Consequently sorting preserves row-echelon independence. It need not
reproduce the intermediate matrix of Gaussian elimination on reordered original
rows; the creation-time minor and partial-scratch invariants above are used.
Only the original input row is retained as a measurement. Gaussian scratch
normalization never enlarges the measurement ranges. Design validation repeats
the same polynomial-size exact algebra and no global Boolean enumeration.

## 2. All contraction fractions have polynomial bit length

Set delta=2^(R-1)*(Q!)^(Q+1). Actual constructed rows have degree<=R and one
common denominator delta. Their cleared integer coefficients have a logarithmic
bound polynomial in Q,R,log(B+1), with B=2 for this graph. At integer node
1<=t<=Q, Taylor shifts preserve delta and have the explicit bound supplied by
TaylorHeight. Summing at most n row contributions gives the actual corrected
port numerator bound P=n*shiftBound(...). Complements also have denominator
delta and numerator bound delta+P.

For any selected set of factors, any partial local Boolean expansion, and any
retained coefficient below J, the resulting polynomial has denominator dividing
delta raised to its used incidence count. A product of at most M input-port
factors contributes at most J^M convolution terms per retained coefficient.
For the local truth expansion, the sum of the truncated coefficient l1 norms
of each cleared yes/no pair is at most delta+2JP<=J(delta+2P). Multiplying these
pair bounds controls ALL local truth leaves; their number is not incorrectly
charged to the 2^n head-assignment bound below. The new LocalPrefixHeight
identifies each actual truth subtotal with a zero-masked table, and each
selected-port leaf product with its explicit padded integer product.
Every partial convolution contains a subset of its product terms, so the same
triangle bound holds independently of cancellation. Constant
one factors pad the common denominator to delta^M when comparing different
selected products. Missing groups therefore do not force new unrelated
denominators.

For a fixed summary label, a product of partial group sums expands over a subset
of the product of local Boolean assignments. Its size is at most 2^n because
the groups partition the original variables. Each factor belongs to one group;
its off-group representative is an ordinary Boolean base. Factor-dependent
Boolean bases are permitted in the integer-numerator bound. Partial label sums
add a further factor at most Y, the full summary-box cardinality. Partial signed
support sums add at most 3^n choices. Thus even a deliberately loose envelope

    (3^n Y 2^n) * J^(F+M) * (delta+2P)^M * delta^M

bounds every numerator after padding to a single denominator delta^M. Extra
delta^M is harmless overpadding. Local partially expanded terms and group
prefixes are covered separately before using the full fibre identity; the small
final count is not used to bound large intermediates.

Coarsely Y<=(2nW+1)^(2n), where W is the proved literal integer constraint bound.
Its logarithm is polynomial in n,logW. Also log(delta),logP,logW are polynomial
in log n under the actual schedule, and J=floor(MR/Q)+1<=n+1. Consequently all
these numerator and denominator bit lengths are polynomial in n. The new
PacketHeight/FibreAccumulatorHeight statements are the intended formal
attachments for the exact partial sums in this argument; check their coverage
of product prefixes, local partial truth-table sums and convolution prefixes.

## 3. Intrinsic Hermite recovery also has polynomial heights

The executed cardinal builder multiplies affine factors 1+z/(t-s), with J
copies of every other sample. Its full common denominator is
dL=(Q!)^(QJ), its normalized constant term is one, and its coefficients have
absolute value <=2^(QJ). All recursive builder suffixes and partial convolution
sums have explicit bounds. Evaluating the same factors at -t computes the
cardinal value at zero; it is not supplied as coefficient advice.

For normalized input with denominator d and numerator bound B, inverse
coefficient k has denominator d^k and numerator at most
[J(d+B+1)+1]^k. Every recurrence dot-prefix has the corresponding proved bound.
After the cached quotient, evaluation and multiplication by the cardinal value,
one denominator dL*(dH*dL^J) works for EVERY sample t. Partial node sums therefore
add numerator magnitudes without accumulating pairwise unrelated denominators.
HermiteArrayHeight gives explicit polynomial bit budgets, including all relevant
builder, inverse, convolution, evaluation and node-sum prefixes. The H inputs
are the actual packets of the preceding step, not free samples of the global
count polynomial.

## 4. Primitive arithmetic, entry evaluation and data movement

An H-bit signed rational represented by reduced numerator and positive
denominator supports add, multiply, negate and inverse in O((H+1)^3) Boolean
work by school arithmetic, Euclidean GCD and exact division. RationalBits
constructs these operations on physical Boolean words and proves this bound,
including the unreduced temporary width and paid copies back to a public
template. A height bound on the output justifies that copy; it is not a runtime
oracle. DotBits applies those operations to actual products and all partial
sums with a common denominator. Other rational loops use the same primitive
operations. Raw temporaries before reduction are at most a fixed multiple of
the operand bit lengths.

Every actual local graph entry is a deterministic polynomial-size calculation
on at most w bits: binary word reading, canonical comparison, finite forward or
normalized inverse DFT equations, twiddle/product equations, integer carry
equations, and Boolean flag checks. The modulus 2^m+1 has m+1 bits, with m the
macro word length, not exponentially many bits. Modular products/powers and
the explicit dyadic inverse normalizer have polynomial bit cost. EntryExecution
and EntryBitPrimitives eliminate the noncomputable reader/normalizer and supply
real Boolean operations; the per-vertex BitCheck assembly is the intended
formal whole-entry bound. Building target-digit descriptors from the original
binary input uses shifts/division by powers of two in polynomial time.

No random-access operation needs to be free. All stored row/cache/graph tables
have polynomially many entries of polynomial bit width. A lookup, update, copied
array or dictionary operation can be implemented by scanning a flat binary
table in polynomial time. Enumerators retain one current support, Boolean word
or measurement vector and polynomially many active frames. Their indices and
summary counters have polynomial bit width. Implementing each such control
step by scans of the retained polynomial-size state introduces a polynomial
factor. Alternatively, a generic tape simulation with polynomial overhead in
the total runtime preserves a 2^o(L) exponent, even without using a sharp space
bound. Neither route assumes a word-sized unbounded integer operation.

## 5. Complete operation count

The support enumeration has Cq=sum_(j<=q)2^j choose(n,j) callbacks with
q=floor(2nR/Q) and J=q+1. Each callback enumerates at most Y summary labels. For
one label it scans the head groups separately: finding representatives and
evaluating each group costs at most poly(n)*2^h, h=max_g|head_g|. It does not
scan the Cartesian product of head assignments. A local multilinear extension
uses at most 2^w actual Boolean entries. The factor count, array width, node
count, validation, construction and L+1 prefix queries add polynomial factors.

Hence, after the height/control bounds above, a full accepted-guard run costs

    poly(n) * Cq * Y * 2^h * 2^w

BIT operations, with a fixed polynomial independent of N. The same expression
was previously only an arithmetic-operation ledger; Sections 1--4 identify
the obligations needed to justify promotion to bit cost.

Eventually Q>=lambda/(256nu), R<=8sqrt(lambda),
r>=sqrt(lambda)/(2nu^2), and q<=4096nnu/sqrt(lambda). The finite weighted
entropy bound, constructed summary bound and actual head bound give, for
example,

    Cq*Y*2^h <= poly(n)*2^(16435nnu^2/sqrt(lambda)).

The numerical constant 16435 is retained from the previous operation ledger,
but has not been independently pinned by this audit and is not needed for the
subpower conclusion. A separate finite proof is available: for 0<x<=1,
Cq<=x^(-q)*(1+2x)^n. With alpha=q/n tending to zero, choose x=sqrt(alpha)
when q>0; this gives log(Cq)/n<=-(alpha/2)log(alpha)+2sqrt(alpha), which tends
to zero. The q=0 case is Cq=1. The proved summary/head bounds also give
log(Y)+h=o(n). Thus the independently reviewed candidate conclusion is

    poly(n)*Cq*Y*2^(h+w)=2^o(L),

because n=Theta(L), w=O(L^(3/4)), and (loglog n)^2/sqrt(log n) tends to zero.
Every fixed polynomial overhead, including a coarse tape simulation, preserves
the last relation. Eventually this is <=2^(L/12), hence O(N^(1/12)); the choice
1/12 leaves room below the requested 1/6 and is not an optimized exponent.

## 6. All inputs, rather than an accepted subfamily

The exact source/executable guards are proved eventually true on the actual
public graph family. Thus every guard failure occurs below one fixed input
length threshold. Trial division handles those finitely many N exactly; its
maximum cost over that finite set is a constant in the asymptotic theorem.
The algorithm tests the guard and does not need the numerical threshold as
advice. Optional resource caps are excluded from this mathematical algorithm;
a capped diagnostic can return no result and has no all-input guarantee.
Prime inputs return no proper divisor, square inputs and either factor
orientation are covered, and all prefix restrictions preserve the original
scope/occurrence graph. The final product test is polynomial time.

## Review gate before treating the candidate as proved

The dominant open task is correspondence, not a new exponent calculation.
Independently check each of Sections 1--4 against the concrete executed loops,
including Gaussian pivot height, every separation/local/convolution prefix,
all constructor loops and scalar divisors, public entry descriptors, and actual
cached H-packet acquisition. A generic scalar backend theorem or a final-result
height theorem alone is insufficient. Any unmatched loop remains an explicit
hole; until those checks and the required formal assembly are complete the
goal stays active and the guaranteed runtime is not claimed as achieved.
