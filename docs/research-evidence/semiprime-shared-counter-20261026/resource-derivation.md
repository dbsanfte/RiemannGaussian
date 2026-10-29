# Resource connection for the implemented counting route

This is an algorithm-level derivation for the code in this packet. It is not a
compiled primitive-machine runtime theorem. The earlier source lemmas and the
full factor-network correctness proof remain external/manual dependencies until
the planned Lean connection is complete. Finite tests do not prove the rate.

## Input and actual algorithm

The input is a bit-network with `n` variables, factors `T_f : {0,1}^w_f -> {0,1}`,
total scope length `M=sum w_f=2n`, maximum arity `w<=C*n^(3/4)`, occurrence two,
and polynomial-time/space local entry verifiers. The macro-FFT compiler supplies
this description from the original integer, without using its factors. Its
stored port lists have total length 2n; no Boolean truth tables are input data.

`shared_parameters.py` computes the beta=1 numerical schedule by integer
arithmetic and checks Lemma 4.7 itself. `shared_layout.py` constructs the design
from the actual scopes. `shared_counter.py` executes the separated fibre sums,
the Boolean Möbius substitutions for the jets, and rational Hermite recovery.
`factor_solver.py` applies conditional counts to the actual original factor
bits. It reports the finite-size fallback separately from the counting branch.

Put lambda=ceil(log2 n), nu=ceil(log2 lambda), r=floor(sqrt(lambda)/nu^2),
Q=floor(lambda/(128nu)), R=4ceil(sqrt(lambda)), tau=1/(r lambda), and
D=r^(2Q). The interval starts at floor(Q(r-1)/(2r)-(R-1)/2). The checker does
not assume that w is polylogarithmic. It explicitly tests positivity, the
interval, `2*(2+w)*D^2<=2n`, `2*Q*r^2<=n`, and the exact rational binomial tail.
Additional concentration-range checks R>=32 and 6R<=Q make the eventual-validity
argument transparent. These checks involve polynomially many bits in log n.

For fixed C, D^2<=2^(lambda/64)=O(n^(1/64)), so the first balance expression is
O(n^(49/64))=o(n). The second is polylogarithmic. For W~Bin(Q,(r-1)/(2r)),
the interval contains every integer within R/4 of the mean eventually, giving
Pr[W outside I]<=2 exp(-R^2/(8Q))<=2 exp(-256nu), eventually below
1/(2*r^2*lambda). Consequently the schedule fails only at finitely many n for
this input family. These are mathematical estimates requiring formalization;
the executable guard checks each actual input without an unknown threshold.

## Construction is polynomial, including intermediate arithmetic

The actual conditional-expectation implementation fixes entire r-ary words of
length Q. There are K=r^Q=sqrt(D) candidates at each of n+|F| decisions. Its
score evaluates O(M^2+Q*n^2) pair indicators. Independence of the variable-label
and factor-label families factors each probability into 1, 0, or 1/K, with
coordinate equality 1/r. All scores have a common denominator dividing
`D*r*M*(b+w)*Q*n`; reduced fractions and their temporary products therefore
have polynomial bit length. The history stores O(n+|F|) scores, not all branches.

The auxiliary eigenbasis has D vectors of length D with entries 0,+1,-1.
Each squared norm is a power of two at most 2^Q. Every partial spectral sum has
denominator dividing 2^Q and polynomial bit height. The dense matrices and rows
use polynomial(D,Q,r) work and storage; this is genuinely materialized polynomial
data, not a purported implicit matrix shortcut. The final common row denominator
is delta=(R-1)!*Q!, with log(delta)=O(Q log Q). Under the accepted schedule D is
polynomial in n. Copy embeddings and exact rational row-space validation also
have polynomial dimension and polynomial bit height (minor/determinant bounds).

## Fixed-denominator jets

Let A bound the sum of absolute coefficients in every integral row delta*P.
The row construction gives log A=O(Q log Q). For a sample t<=Q and fixed Boolean
U, each input jet is

    P(t) dot x + (P(t+z)-P(t)) dot 1_U  (mod z^J).

It has denominator dividing delta. Its integer numerator has coefficient l1
norm at most B=2*A*(Q+1)^R, hence log B=O(Q log Q). This follows by binomial
expansion of each T^k at t+z and the original row's coefficient l1 bound. The
constant term comes from x; the positive-degree terms come from U. No expansion
in n independent formal variables is performed.

For a w_f-port Boolean factor, the true multilinear extension is

    Phi_f(X)=sum_eta T_f(eta) product_i (eta_i*X_i+(1-eta_i)*(1-X_i)).

The recursion for its numerator combines `(delta-X_0)*left + X_0*right`.
Its l1 norm is at most `(delta+2B)^w_f`, and its denominator divides delta^w_f.
Truncating modulo z^J cannot increase l1 norm. Alternatively a coefficientwise
bound of `[J*(delta+2B)]^w_f` suffices; the new Lean height module proves the
corresponding finite-coefficient bound for the actual polynomial recursion.
This looser bound still has polynomial bit length. Integer numerator height
depends linearly on w_f in bits, not on 2^w_f.

The Python evaluator streams the 2^w_f Boolean assignments and multiplies their
jet factors. It uses O(w_f*2^w_f) jet operations and polynomial workspace; it is
algebraically the sum formula proved for the recursive Lean evaluator. The code
does not claim its execution is already compiled from that Lean recursion.

Let c be the total number of measurement rows at a point, and
C_q=sum_(s<=min(q,n)) 2^s*binom(n,s). Every partial group product uses denominator
delta^(its port count). A complete product uses delta^M. Summing group assignments,
measurement tuples and signed Möbius terms preserves that fixed denominator.
A sufficient absolute numerator bound for any Taylor accumulator is

    C_q * (2D+1)^c * 2^n * (delta+2B)^M.

The compiled coefficientwise version inserts a factor J^(M+|F|). Since C_q<=3^n, c<=2tau*n<=n,
M=2n and J=O(nR/Q+1), its logarithm is polynomial in n. Fraction addition may
temporarily multiply two denominators before gcd reduction, but this only
doubles their bit bound at one step; each stored result again divides the same
fixed denominator. There is no new denominator per enumerated summand.

## Hermite recovery has polynomial bit cost

Let J=floor(MR/Q)+1, so QJ>MR. The code forms the normalized polynomials

    L_t(T)=product_(s!=t) ((T-s)/(t-s))^J.

It computes H_t(z)/L_t(t+z) modulo z^J and sums
`L_t(0) * [H_t(z)/L_t(t+z)]_(z=-t)` over t. The inverse jet's constant is one;
every denominator used here is a known nonzero integer difference, not a
factorization oracle or a modular nonunit. This is the usual Hermite CRT formula
for the unique polynomial of degree <QJ.

The normalized factors have powers of differences at most Q in the denominators.
The explicit negative-binomial expansion of their inverses bounds all order-<J
coefficients by polynomial bit length in Q,J. Products over Q nodes and powers
up to QJ preserve polynomial height. Equivalently the QJ-dimensional confluent
Vandermonde matrix has polynomial-height integer entries, and determinant/minor
bounds give polynomial-height inverses. Thus all retained rational numbers and
the final interpolation arithmetic cost polynomially many bits/bit operations.

## Total time and space of the executed loops

At each of Q nodes, the code streams C_q pairs (E,U). Each pair scans at most

    2*(2D+1)^c * sum_g 2^|S_g| <= 2*r*(2D+1)^(2tau*n)*2^(2n/r)

Boolean group vectors. Using actual measurement row radii only reduces this
count. For each vector at most |F| factors are evaluated, with at most
poly(n+description)*2^w local work after charging their entry verifiers. The
precise operation counts in diagnostics are observations, not assumptions in
this bound. Validation and construction add polynomial work. Therefore

    time <= poly(n+description) *
            2^[ O(n*(R/Q)*log(2Q/R) + n*tau*log(2D+1) + n/r) + O(w) ]
         = poly(n+description) * 2^O(n*(log log n)^2/sqrt(log n)).

All loops are streams. Retained data consists of the polynomial-size layout,
one Boolean assignment per group, current integer measurement coordinates,
current E,U, jet accumulators, QJ Taylor coefficients and polynomial-height
Hermite data. Counters themselves have polynomial bit length. There are no
materialized truth tables, assignment fibres or sets of all Möbius pairs.
Thus workspace is polynomial in n+description in the ordinary bit model.

## Original integer and uniform recovery

The actual macro-FFT network has n=Theta(L), w=O(L^(3/4)), where
L=ceil(log2(N+1)). Every conditional query modifies only an existing local
predicate on an original P-bit edge, preserving scope lengths and all layout
data. An initial positive count followed by one zero-child count per P bit
recovers P in at most L+1 queries: if the zero child is empty, all of the positive
parent count belongs to the one child. The final arithmetic division is checked.

When the schedule fails, the wrapper scans divisors through sqrt(N). Since n
grows with L and only finitely many n fail for the actual network family, this
branch affects only finitely many input lengths. It is absorbed into one fixed
asymptotic constant and uses polynomial space. It does not turn small diagnostic
examples into evidence for the fast rate; the result explicitly names fallback.

The resulting proposed bound for every input is

    poly(L) * 2^O(L*(log log L)^2/sqrt(log L)) = N^o(1).

In particular it is eventually O(N^(1/6)), indeed O(N^epsilon) for every fixed
positive epsilon, with a finite constant for the small inputs. This is not a
practical threshold assertion: the conservative schedule can start extremely
late. The full goal remains open until these all-input algorithm and bit-resource
claims are connected into the required kernel-checked end-to-end theorem.
