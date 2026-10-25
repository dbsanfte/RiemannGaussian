# Uniform count of nonproportional lifted square-product occurrences

22 October2026. Verdict: the proposed uniform m^{o(1)} bound is valid for each FIXED nonproportional pair with positive multipliers, in the stated polynomial-height interval. In fact the ideal count is at most tau(C²), rather than tau(C²)². This is a counting lemma, not an efficient Pell solver, class-coverage theorem, or a claim about which varying N are semiprimes.

## 1. Exact reduction

Fix prime m, M=m³ and a residue representative N_0 modulo M. Assume the canonical row multipliers a_i,a_j and lifts v_i,v_j are held fixed as N=N_0+M t varies. Their exact norms satisfy

    z_i=B_i−4a_i t, z_j=B_j−4a_j t,
    B_i=(v_i²−4a_iN_0)/M,
    B_j=(v_j²−4a_jN_0)/M.

The B are integers. Canonical data are indeed consistent with this fixed-residue statement: a depends on N modm, the canonical b on N modm², c changes by m t, Delta=b²−4ac therefore has fixed residue modulo m, kappa is fixed, and consequently v=ell−m²kappa is fixed. This presumes the deterministic canonical choices are made from those residues, rather than additional N-dependent tie breaking. The counting lemma itself only needs the displayed fixed linear functions.

If z_i z_j=W² with integer W, put

    A=a_i a_j>0,
    C=a_j B_i−a_i B_j,
    X=8A t−(a_j B_i+a_i B_j), Y=2W.

Expansion gives exactly

    X²−A Y²=C².                                 (1)

No primitiveness of(X,Y) is assumed. If C!=0, the map t→X is injective, so counting all integer solutions of(1) in a box overcounts the possible t and suffices. With a_i,a_j<m, |B_i|,|B_j|=O(m³), and |t|=O(m³), one has |C|=O(m⁴), |X|=O(m⁵). A nonnegative interval0<=t<=m³ is a special case. The parity condition Y even and the condition X in one arithmetic progression only REDUCE the count and need not be imposed for the upper bound.

## 2. A uniform bounded-Pell lemma

Let A be ANY positive integer, C any nonzero integer, H>=1. The number of integer pairs(X,Y) satisfying

    X²−A Y²=C², |X|<=H

is at most

    2 tau(C²) [1+log((2H+|C|)²/C²)/log lambda]

when A is nonsquare, where lambda=(3+sqrt5)/2. If the logarithm is negative the set is empty; one can equivalently put a positive part on the logarithm. For square A the bound2 tau(C²) suffices. Constants are ABSOLUTE and do not depend on the quadratic discriminant or its regulator.

### Nonsquare A: integral ideals in the maximal order

Write A=s²d with d>1 squarefree and s>=1. Let K=Q(sqrt d) and work in its MAXIMAL order O_K. The element

    alpha=X+sY sqrt d

is integral, because Z[sqrt d] is contained in O_K, and has field norm C². Thus its principal integral ideal(alpha) has absolute norm C². Passing to the maximal order avoids all questions about invertible ideals in a nonmaximal order. It can only enlarge the set of possible generators; the required lattice condition s|coefficient(sqrt d), parity conditions for d=1mod4, and the original order constraints can be dropped in an upper bound.

There are at most tau(C²) integral ideals of this norm. To see this directly, factor the integer C² as product p^e. For split p the two primes above p have norm p, so an ideal of norm p^e has e+1 exponent choices. For inert p the prime has norm p², giving at most one choice. For ramified p the unique prime has norm p, also giving one choice. Unique ideal factorization in O_K makes the total count at most product(e+1)=tau(C²). Primes dividing the discriminant are included in the ramified case; no omitted conductor factors occur. Class number is irrelevant: some of these ideals might not be principal and then contribute zero solutions.

### Uniform count of generators of one ideal

If alpha,beta generate the same ideal, beta/alpha is a unit of O_K. Since both field norms equal C², this unit has norm+1. Their two real embeddings have the same sign individually for each generator because their product is positive. Separate generators according to the sign of the first embedding, contributing at most a factor2.

For a unit u>1 in the first embedding with norm+1, the other embedding is1/u, and the trace u+1/u is a rational integer strictly greater than2. Thus it is at least3 and

    u>=(3+sqrt5)/2=lambda.

This elementary separation bound avoids needing a fundamental unit, a regulator estimate, or the unit theorem's effective construction. Any two positive generators of one fixed ideal, ordered by their first real values, differ by at least this multiplicative factor. It applies uniformly even if their ratio lies outside the original nonmaximal order.

From(1), |sY sqrt d|=sqrt(X²−C²)<=H whenever a solution exists. More conservatively, both embeddings of alpha have absolute value at most B=2H+|C|. Since their product is C², each also has absolute value at least C²/B. Therefore generators of one sign lie in the finite multiplicative interval[C²/B,B], which contains at most

    1+log(B²/C²)/log lambda

lambda-separated values. This proves the stated bound after multiplying by2 and by the ideal count. The association alpha↔(X,Y) is injective, so there is no hidden multiplicity. Signs of Y, Y=0, endpoints of the box, imprimitive solutions, and all possible common divisors of X,Y are already included.

### Square A

If A=s² is a positive square, use the exact integer factorization

    (X−sY)(X+sY)=C².

Both factors are nonzero and have the same sign. There are2 tau(C²) ordered signed divisor pairs before imposing parity or divisibility by2s. Each gives at most one(X,Y). Thus the claimed bound follows without introducing a degenerate quadratic field.

## 3. Native polynomial-height consequence

For the fixed pair in Section1, take H=O(m⁵), |C|=O(m⁴), C!=0. The archimedean factor is O(log(m+2)), uniformly even when |C|=1. The elementary uniform divisor bound tau(n)=n^{o(1)} yields

    number of possible t <=tau(C²) O(log(m+2))=m^{o(1)}.

Equivalently, for each epsilon>0 there is a constant depending only on epsilon and the absolute height constants such that the count is at most that constant times m^epsilon. This is uniform across all positive a_i,a_j<m and admissible integer B_i,B_j. It is not soft O(1): the divisor factor is subpolynomial, not generally bounded by a fixed power of log m.

For O(m) rows there are O(m²) nonproportional unordered pairs. A union bound therefore gives at most m^{2+o(1)} integer t for which ANY of those fixed nonproportional pairs has an integer-square norm product, inside a length-O(m³) parameter interval. This last conclusion concerns integer parameters with fixed canonical residues; it does not by itself prove the existence of a semiprime satisfying all preparation/size conditions outside the union. No prime-distribution or class-coverage claim is made.

C=0 is ESSENTIAL to exclude. Then the two affine norm functions are proportional, and square products can persist throughout the interval when the multiplier ratio is a rational square. Equation(1) degenerates to X²=A Y², where the divisor argument based on nonzero norm cannot apply. For the useful negative-pair criterion, C=0 is exactly constant proportionality of the normalized integer invariants: a_j v_i²−a_i v_j²=M C, so these pairs are already the provably trivial proportional class. The count is not asserted for them.

## 4. Source and algorithmic scope

The proof above supplies all quantitative details directly. Author-written context for the ideal/associate method is Brian Conrad's *Generalized Pell equation*, https://math.stanford.edu/~conrad/154Page/handouts/genpell (PDF also at https://virtualmath1.stanford.edu/~conrad/154Page/handouts/genpell.pdf). Its finite-ideal/units explanation is not used as an oracle or as a ready-made uniform bound; the absolute ideal-count and unit-separation estimates are proved above.

This is an existence-COUNT upper bound. It does not assert a soft-m procedure to enumerate all solutions, factor C or A, compute a quadratic class group, construct ideal generators or find fundamental units. Those are proof-side objects only. No class number, nonmaximal-order algorithm, hidden-factor call, experiment, repository edit or backend is needed. Only this allocated scratch report was written.
