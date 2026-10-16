# The constant-leading-coefficient redesign has an exact global Sidon target set

2026-10-16. New classical actual-source result for a natural row-adaptive denominator family. Choosing denominators to make every leading coefficient equal to one retains soft-linear setup and guaranteed own-factor coverage, but its global targets are an exact multiplicative Sidon set on the retained large-order branch. This rules out cheap geometric-cover representations of this family; it is not an operation lower bound or a new query evaluator.

## 1. Redesigned native rows and their coverage

Let m be an odd prime not dividing N=P Q, with P,Q=Theta(m^3) and max(P,Q)<=sqrt(3/2)*m^3 as on the inherited balanced family. For j=1,...,m-1 choose the canonical denominator

 t_j=(N^(-1) j^2 mod m) in {1,...,m-1},
 a_j=1,
 b_j=centered(-j^(-1)(N t_j-j^2)/m mod m),
 c_j=((N t_j-j^2)/m+j b_j)/m.

Both integer divisions are exact. These are literally the positive-branch denseRow constructors: their canonical representative N t_j j^(-2) modulo m equals one. Unlike a fixed-denominator subfamily, the denominators vary across up to m-1 values. Put

 delta_j=1+m b_j-2j,
 E_j=N t_j+delta_j,
 z_j=gamma^(-E_j).

The quotient relation m^2 c_j-j m b_j+j^2=N t_j holds. For j=P mod m, the native factor-sum mechanism gives the INTEGER

 i_P=(P+t_j Q+m b_j-2j)/m^2,
 E_j-m^2 i_P=(P-1)(t_j Q-1).                    (1)

For completeness, divisibility of the numerator follows by multiplying it by P: the result is m^2 times the quadratic x^2+b_j x+c_j at x=(P-j)/m, and P is a unit modulo m^2. The numerator is eventually positive because t_j>=1 and P,Q=Theta(m^3). Since |b_j|<m/2, its upper bound is m*max(P,Q)+m^2/2, so i_P<2m^2+2. This gives a genuine P-field collision for gamma with local order dividing P-1. Swap P,Q for the other own-factor witness.

Setup is softly O(m) arithmetic: compute the public inverse of N modulo m, generate t_j from j^2 residues, obtain all j inverses, and perform the exact divisions and centering. The bit lengths are O(log N); target powers can be computed within the corresponding soft O(m log N) bit envelope. No hidden prime or order is algorithm input. This is a coverage family, not an acquired scalar product.

## 2. Global-order reduction and exact Sidon theorem

Write S=P+Q-1. Assume the inherited large global element order

 D=ord_N(gamma)>16m^4,
 D divides (P-1)(Q-1),
 2(m^2+m)<S<=3m^3.                              (2)

These conditions hold eventually on the retained actual source: the exact local orders are distinct primes R_P,R_Q>16m^2, hence D=R_P R_Q>256m^4. The bounds on S follow from balanced size and P,Q=Theta(m^3). Since phi(N)=N-S,

 N=S mod D,   z_j=gamma^(-(t_j S+delta_j)).        (3)

This is a GLOBAL reduction, not a claim that a local order exceeds the larger phase span.

Let h=(m-1)/2. Exact centering gives -h<=b_j<=h, so all delta_j lie between 3-mh-2m and mh-1. Their span is m^2+m-4<m^2+m. The effective phases t_j S+delta_j therefore have span at most (m-2)S+(m^2+m). A difference of two pair sums has absolute value less than 8m^4<D, using S<=3m^3 and m>=3. Thus equality z_1 z_2=z_3 z_4 forces the exact INTEGER identity

 (t_1+t_2-t_3-t_4)S+(delta_1+delta_2-delta_3-delta_4)=0.       (4)

The second term has absolute value less than 2(m^2+m)<S. Hence the integer denominator-sum difference is zero. Equation(4) then equates the delta sums. Reducing that equality modulo m gives

 j_1+j_2=j_3+j_4 mod m,

since delta_j=1-2j mod m and m is odd. The denominator-sum equality also gives, using t_j=N^(-1)j^2 modulo m,

 j_1^2+j_2^2=j_3^2+j_4^2 mod m.

Equal sums and sums of squares imply equal products, so the two unordered pairs of residues j coincide. Tags lie in {1,...,m-1}, so they coincide as integer tag multisets. Conversely those trivial unordered-pair coincidences always give equal products.

The targets are distinct as well: equality of two targets embeds into a product equality with any common third target, and the just-proved multiset criterion forces equal tags. Therefore J=m-1 and the exact multiplicative energy in the GLOBAL unit group is

 E_times(Z)=2J^2-J.                              (5)

There are J repeated-pair ordered pairs and two choices of ordering for each distinct pair, giving (5). This theorem needs no averaging over N digits and no new exceptional-input deletion. It holds on every input satisfying (2). It does NOT assert the same energy in each hidden field; local phases may wrap.

## 3. Consequences for advised geometric carriers

For any cover by k finite geometric progressions in an ambient ABELIAN group containing these global targets, with total listed length T, partition the distinct targets among the cover pieces. Each assigned subset V_i has productset size at most 2T_i-1, even with holes, overlaps, privately chosen origins/ratios, ratios outside the gamma subgroup, degeneracy or cyclic repetitions. Energy and Cauchy--Schwarz give

 2J^2-J >= J^4/(2k^2 T),
 k^2 T >= J^4/(4J^2-2J) >= J^2/4.               (6)

The containing group must embed the actual global target group faithfully; passing to a local quotient does not preserve (5). The bound holds simultaneously for all advised covers, without enumerating them.

For any finite containing carrier C, |CC|>=J^4/(2J^2-J)>=J^2/2. A rank-r geometric progression box of listed size T satisfies |CC|<=2^r T and hence 2^r T>=J^2/2. Thus a polylogarithmic number of progressions cannot have nearlinear total listed length, and nearlinear progression boxes of fixed or o(log m) rank cannot contain this redesigned family.

The result answers the natural promise that making every a_j=1 will make the target geometry cheap: its complete global target set is maximally low-energy instead. It does not exclude a scalar norm evaluator, shared operations across a large carrier, implicit non-cover representations, further denominator redesign, local field algorithms, or factor-selective consequences. No arithmetic-operation lower bound, improved factoring exponent, native proof, experiment or build is claimed. All prior packets remain unchanged.
