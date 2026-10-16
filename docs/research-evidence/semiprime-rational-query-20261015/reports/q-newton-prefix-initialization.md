# Ring-safe nearlinear q-Newton initialization; long implicit propagation remains open

2026-10-15. Positive partial algorithm for the actual holonomic interface. No soft O(J+sqrt L) long-horizon evaluator, new Lean endpoint or scalar complexity lower bound is claimed.

## A cost that can be paid: the first J formal weighted values

Let F_n(w)=sum_j w_j P_n(z_j;q), with J targets and formal independent weights. Suppose q is a unit and 1-q^r is a unit for 1<=r<J. These conditions hold on the retained actual source because the local q orders exceed 16m^2 while J=m-1. Put

Q_0=1, Q_n=prod_(r=1)^n(1-q^r),
s_k=sum_j w_j z_j^k.

Then all F_0,...,F_(J-1) can be acquired in soft O(J) ring operations and soft O(J) storage, with all parameter acquisition charged. This removes a potential quadratic INITIALIZATION charge; it does not solve long recurrence propagation.

The q-binomial identity gives

P_n(z;q)=sum_(k=0)^n (-1)^k q^(k(k-1)/2) Q_n/(Q_k Q_(n-k)) z^k.

Therefore, exactly in R[w],

F_n/Q_n=sum_(k=0)^n A_k B_(n-k),
A_k=(-1)^k q^(k(k-1)/2) s_k/Q_k,
B_k=1/Q_k.                                                (1)

Thus ONE ordinary truncated convolution of A and B gives the whole prefix after rescaling by Q_n.

Acquire s_0,...,s_(J-1) by the already established ring-safe rational tree

sum_(k>=0)s_k t^k=sum_j w_j/(1-z_j t).

Each denominator has constant coefficient one. A balanced rational-function assembly and power-series inverse/expansion costs soft O(J), with no inverse target differences. The resulting arithmetic circuit is formally linear in the weights; the parameter denominators are weight-independent. No numerical finite-function substitution is used.

Acquire q powers, Q_n and chirps q^(k(k-1)/2) by O(J) operations. All inverse Q_n can be obtained from one inverse Q_(J-1) and a backwards pass: Q_(n-1)^(-1)=(1-q^n)Q_n^(-1). On the promised actual source its gcd with N is one. Outside that source a proper gcd is a factor, while gcd=N requires separately routed handling; it must not be called automatic success. Hence the only extra inversions in (1) are certified weight-independent parameter units.

The convolution is over ring elements or over the corresponding weight circuits, without expanding polynomials in the w_j. For the formal circuit, the B array and all rescalings are parameter constants, and the numerator rational tree is assembled by multiplying weight-dependent numerators only by parameter denominators. Its soft-linear operation bound is therefore a genuine formal weighted-SLP bound for this J-length prefix. It remains valid with zero divisors or zero P_n(z_j).

## The q-Newton prefix transform itself is invertible cheaply

The preceding triangular transform can also be inverted in soft O(J). Normalize the supplied prefix by Q_n to form C(t). In (1), B(0)=1, so invert B(t) modulo t^J with the ordinary unit-constant power-series algorithm. Recover A(t)=C(t)/B(t) modulo t^J, then s_k from A_k by the known unit factors Q_k and chirps. No Vandermonde inverse is needed for this prefix/moment transform.

This gives a concrete short implicit representation for q-Newton basis conversion when applying it to a vector. It explains why the quadratic coefficient table in the previous holonomic report is a DENSE-OUTPUT contract rather than an inherent cost of transforming one short vector.

## Why this does not yield the long jump

The order-J unit-leading recurrence from H can use the acquired prefix as initial data. Its long-horizon evolution still encodes P_L(z_j) values. The explicit dense operator table can be avoided for initialization, but this does not make its ordered transition product a constant matrix power or make it cheap to apply.

At a later start n, the same convolution applies to the next J values with nodes q^n z_j and weights w_j P_n(z_j). These new weights are exactly the unknown long products multiplied by the input weights; treating them as supplied would assume the missing query. The cheap base-change algorithm therefore cannot be invoked at a distant n by merely changing q^n without also acquiring that weight state.

On the actual source, publicly deduplicate equal INTEGER offsets delta_j and merge their formal weights. The remaining target nodes have pairwise unit differences: offset differences are nonzero and smaller than both retained local orders. Fast interpolation/transposed Vandermonde transforms then turn a complete J-value state at n into its individual weighted P_n(z_j) values at soft-linear additional cost, with the required parameter-unit checks. Thus a sufficiently fast general full-state jump would indeed solve the batch query. This is a diagnostic equivalence, not a new acquisition algorithm or a claimed lower bound; a horizon-specific scalar or other compressed representation could still be better.

## Known matrix q-factorial accounting

The saved primary Bostan--Yurkevich author text, section 3.4/Theorem 5, explicitly gives O(r^theta sqrt(Nd)+r^2 M(sqrt(Nd))) field operations for recurrence order r and coefficient degree d. Its Algorithm 3 forms a polynomial matrix block and evaluates entries on a geometric progression, so it retains both matrix dimension and block degree.

For the natural closure here r=J and d<=J, direct invocation has a growing-dimensional cost and gives no improvement over the original scalar-polynomial q-product BSGS soft O(J+sqrt(JL)). The fixed-order square-root-in-horizon headline cannot be specialized while dropping r. This is a cost of that existing matrix method, not a lower bound on structured matrix-vector propagation. The companion's unit leading coefficient and unit q make its elementary arithmetic patterns ring-safe, but no new soft-linear algorithm for its implicit block state is supplied here.

## Outcome

A precise paid positive interface is now available: acquire and invert the first-J formal weighted q-Newton prefix in soft O(J), with parameter unit certification on the actual long branch. The remaining challenge is long implicit high-order propagation or a horizon-only formal weighted transform, not initial-value construction. No actual source multiset cancellation, fast displaced matrix-factorial jump or nearlinear long query was found in this investigation.
