# A paid GAP criterion for acquiring a decodable annihilator

2026-10-16. This is a constructive conditional criterion for **supplied GAP descriptions with a proved cover property**. It constructs the annihilator or a factor with every arithmetic cost charged. It does not construct a universal cover and does not claim that the existing Umans--Wang conjecture supplies the additional data below.

## Exact theorem

Let N=PQ with distinct odd primes, and put

    n=ceil(sqrt(N)),     m=ceil(n^(1/3)),     B=16m^2.

Suppose a supplied unit gamma modulo N has odd local orders d_P,d_Q>B. Accept the reviewed QRH decoder: a supplied nonzero L-bit K with gamma^K=1 modulo N yields a factor in deterministic bit cost soft O(L+N^(1/12)). Its use here is an external theorem, not a new proof of QRH or a Lean declaration.

Give two finite integer GAP descriptions

    s(i)=a_S + sum_(j=1)^(c_S) i_j*b_(S,j),   0<=i_j<ell_(S,j),
    t(k)=a_T + sum_(j=1)^(c_T) k_j*b_(T,j),   0<=k_j<ell_(T,j),

with all lengths positive. Empty ranks are allowed and describe a singleton; below c=1+c_S+c_T. Let

    V_S=product ell_(S,j),     V_T=product ell_(T,j),     V=V_S+V_T.

All offsets and steps are signed integers with at most D bits in absolute value, D>=1. Lengths and their actual products are binary input data, and their bit lengths are charged. Assume

1. c is bounded by a fixed power of log(2N), and cD+V=soft O(m).
2. The interval hulls are strictly separated: **max s(i)<min t(k)**.
3. Some local order of gamma divides one difference t(k)-s(i). A sufficient public mathematical promise is that for every integer 1<=d<=n, some difference is divisible by d. The latter covers d_P when P is the smaller prime, since d_P<=P-1<n. The algorithm never needs the hidden prime, local order, or the witnessing pair.

Then a deterministic algorithm returns a proper factor of N in bit cost

    soft O(cD + V_S + V_T + N^(1/12)) = soft O(m).

No prime factorization of any integer difference or annihilator is an input or subroutine. The GAPs need not be proper: distinct parameter tuples may give the same integer inside either GAP. No deduplication is required.

The cover property in item 3 is a promise requiring its own proof; it is not efficiently verified by this consumer. Items 1 and 2 are directly checkable at the displayed cost. If a cover-construction algorithm outputs these descriptions for every promised N in soft O(m), composing it with this theorem and the already paid gamma preparation would give the requested factoring budget. No such universal construction is claimed here.

## 1. Cheap hull and size checks

For one description, its exact extrema are

    low=a + sum_j min(0,(ell_j-1)b_j),
    high=a + sum_j max(0,(ell_j-1)b_j).

The independent box coordinates attain these extrema. Computing them, the box volumes, and the strict comparison high_S<low_T takes soft O(c(D+log(2V))) bit work. With D>=1, this is soft O(cD) under the theorem's size promises.

Every represented exponent has at most

    D_* = D + ceil(log2(1+cV)) + 3

bits in absolute value. Hence every difference has at most D_*+1 bits. The offset/step descriptions have only soft O(cD) input bits; the theorem never charges only for distinct sumset cardinality while silently enumerating a larger parameter box.

Strict hull separation is the explicit certificate excluding the integer-zero leaf. It also makes every selected K=t(k)-s(i) positive. No comparison between all V_S*V_T pairs of large integers is performed.

## 2. Generate modular powers, retaining only short witnesses

Compute gamma^(-1) modulo N once by extended gcd. Since gamma is a promised unit this succeeds; a proper gcd would already factor N. Signed exponentiation by each offset and each step now costs soft O(cD) modular bit work. Wrap multipliers for the mixed-radix traversal cost an additional soft O(c log(2V)), which is absorbed.

For one GAP write r_j=gamma^(b_j). Start at gamma^a. A mixed-radix increment multiplies the current residue by r_j when a coordinate increases, or by r_j^(-(ell_j-1)) when that coordinate wraps to zero. After discarding length-one coordinates, the total number of increments and carries over the complete parameter box is O(V+c), since every remaining radix is at least two. Thus all modular powers are enumerated using soft O(cD+V) bit work.

Store each residue with its mixed-radix enumeration ordinal. The ordinal has O(log(2V)) bits and determines the parameter tuple by c successive divisions by the public lengths. The algorithm does **not** materialize V different D-bit integer exponents. Duplicates of integer exponents or modular residues remain separate labeled entries and cause no difficulty.

## 3. Find a nonunit cross-difference without forming the matrix

Over R=Z/NZ form the monic polynomial

    F(X)=product_(k in T-box) (X-gamma^(t(k))).

Use fast monic product/remainder trees to evaluate F at every gamma^(s(i)). This costs soft O(V) operations on O(log N)-bit coefficients, hence soft O(V) bit work. Multiplication can be implemented by integer convolution and reduction; monic division uses no inverses of arbitrary ring elements or differences of evaluation points. Repeated roots and repeated evaluation points are permitted.

Scan gcd(F(gamma^(s(i))),N). The promised local-order cover forces at least one nonunit row. If any gcd is a proper divisor, return it.

Otherwise choose a saturated row, whose gcd is N, and descend the retained balanced product tree for T. At a node, evaluate a child's monic polynomial at the fixed row residue and take its gcd with N. A proper gcd returns a factor. A gcd N allows descent into that child; if the gcd is 1, the other child must be saturated because the parent is saturated. Evaluating both siblings directly along the descent costs O(V_T) ring operations in total by the geometric decrease of degrees. It never forms the V_S by V_T matrix.

At a saturated leaf we have

    gamma^(s(i)) = gamma^(t(k)) modulo N.

Since gamma is a unit, this gives gamma^K=1 modulo N for K=t(k)-s(i). Strict hull separation guarantees K>0 as an **integer**, even when many integer parameters or modular powers coincide within a single GAP.

## 4. Recover exactly one integer K and decode it

Decode the selected two ordinals into their parameter tuples. Compute the two signed integer linear combinations and their difference. This costs soft O(c(D+log(2V)))=soft O(cD) bits, and constructs a nonzero annihilator with bit length L<=D_*+1.

Call the QRH long-annihilator decoder once. Its charge is soft O(D_*+N^(1/12)), absorbed in

    soft O(cD + V + N^(1/12)).

Because n=ceil(sqrt N) and m=ceil(n^(1/3)), m=Theta(N^(1/6)), N<=m^6, and N^(1/12)=O(m). Initial powers are paid only for the short GAP description. The long selected difference is read/powered only by the decoder after localization. There is no V*D charge from materializing all exponent integers, and no prefactoring charge for the leaf.

## Relation to the exact primary source

Primary source: Chris Umans and Siki Wang, *A number-theoretic conjecture implying faster algorithms for polynomial factorization and integer factorization*, arXiv:2511.10851v1 (13 November 2025).

- HTML: https://arxiv.org/html/2511.10851v1
- PDF: https://arxiv.org/pdf/2511.10851v1
- Local frozen text: `umans-wang-2511.10851v1.txt`.

Exact local locations: Definition 3.1 at lines 286-287; Conjecture 3.3 at lines 328-346; Lemma 4.2 at line 409 onward; Conjecture 5.1 at lines 817-821; Theorem 5.2 at lines 838-861; Theorem 5.5 at lines 988 onward.

Definition 3.1 introduces its divisor property for positive integers. Conjecture 3.3 describes S,T as positive-integer sets with S-T satisfying that property, cardinality at most n^beta, magnitude at most exp(n^alpha), and rank at most n^{o(1)}. It does not separately present a disjoint-hull certificate, a proper parameter-box bound, a polylogarithmic rank bound, or an every-input uniform cover-construction algorithm. A literal positivity reading of the difference set would exclude zero differences, but this theorem uses the explicit checked hull condition and makes no additional implication claim about that source.

UW's integer Theorem 5.2 computes gcds of integer products of A_i with N; its singleton guarantee is supplied by a separate prefactoring assumption. An integer leaf with N dividing s-t does not give a gamma-annihilator. The algorithm proved above instead uses the **group** differences gamma^s-gamma^t and obtains gamma^(t-s)=1 at a saturated leaf. It is a derived adaptation, not a restatement of their integer theorem.

There is also a coverage distinction: Theorem 5.2 requires divisibility by the whole product of A_i. For composite local orders, that alone does not force a zero among the individual group differences. The criterion here explicitly requires an individual cross-difference multiple. It neither silently strengthens a product-cover promise nor counts an unconstructed cover as available.

## External decoder pin

The accepted analytic input is QRH Theorem 1.1 from the frozen primary source at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`:

https://raw.githubusercontent.com/openai/math/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf

The exact parent decoder statement is in `/tmp/semiprime-first-jet-acquisition-20261016/fresh/qrh-wide-annihilator-extension.md`; its independent review is `qrh-wide-annihilator-review-independent-616.md` in the same directory. The new contribution of this note is the supplied GAP-to-nonzero-annihilator construction and its complete bit charge. It does not acquire the GAP descriptions or prove their hidden-order cover property.
