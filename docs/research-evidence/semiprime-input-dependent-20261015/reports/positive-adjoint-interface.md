# A positive formal-adjoint bridge from weighted sums to the full collision product

2026-10-15. Conditional algorithmic interface, proved self-contained over an arbitrary commutative ring. No fast weighted-inner-product algorithm is presently supplied. No repository edits or new Lean endpoint.

## Exact sufficient contract

Let R be a commutative ring, and let a_j=P_L(z_j) be the desired J q-Pochhammer values (or other target values). Suppose a branch-free straight-line program of T arithmetic gates (+,-,*) computes

    F(w_1,...,w_J)=sum_(j=1)^J w_j a_j

as an IDENTITY in the polynomial ring R[w_1,...,w_J], with the w_j formal input variables. The constants may depend on q,z_j,L and other public parameters. All cost to acquire those constants must be charged. A supplied parameter-specific program is acceptable only with this formal identity, not merely agreement of finite-ring point evaluations.

Then all J values a_j can be acquired in O(T+J) ring operations and O(T+J) working memory by reverse-mode formal differentiation at w=0. Multiplying those outputs takes J-1 additional multiplications and returns prod_j a_j, with every hidden-field zero preserved. In particular a softly linear formal weighted-inner-product program would be a substantive sufficient route to the requested batch product; the earlier warning about a numerical black-box weighted sum does not apply to this stronger program interface.

## Algorithm

Evaluate the program once at w=0 and store every gate value. Allocate an adjoint for each input and gate, initialized to zero, and set the final output gate's adjoint to one. Process gates in reverse order, updating their input adjoints with the following rules, where v is the current output node and bars denote adjoints:

    v=a+b:   bar(a) += bar(v),       bar(b) += bar(v)
    v=a-b:   bar(a) += bar(v),       bar(b) -= bar(v)
    v=a*b:   bar(a) += bar(v)*b,     bar(b) += bar(v)*a.

Here a and b on right-hand sides are the STORED forward values at w=0. Multiple occurrences or a=b simply cause both listed contributions to be accumulated. The final adjoint of input w_j equals the formal derivative (partial F/partial w_j)(0)=a_j. Constants need not have adjoints computed if their derivatives with respect to the weights are zero.

## Correctness over zero divisors and positive characteristic

Formal partial derivatives are defined coefficientwise in R[w]. Their sum and product rules hold over every commutative ring, with no division or field hypothesis. Each reverse update is exactly one local chain-rule contribution. A reverse induction through the acyclic circuit shows that a node's final adjoint is the sum of all output derivative contributions passing through that node. Thus the input adjoints are the formal derivatives of the output polynomial, evaluated at w=0.

The promised polynomial identity is linear in the weights, so those derivatives are precisely the a_j. Intermediate expressions may be nonlinear and cancel; the same formal chain-rule proof still applies. Zero divisors, vanishing a_j, and characteristic-dependent cancellations cause no problem. The algorithm never divides by a target value or candidate collision residual.

Agreement as FUNCTIONS on a finite ring is insufficient. For example, over F_p the polynomial w^p-w vanishes at every field point but has formal derivative -1. A program pointwise equal to a weighted sum after adding this polynomial would have incorrect derivatives for the desired coefficients. Hence formal polynomial identity is an essential part of the contract.

## Explicit cost

The forward pass uses T gates. Each reverse addition/subtraction gate uses at most two ring additions/subtractions. Each multiplication gate uses at most two ring multiplications and two additions. Therefore at most 5T ring operations suffice for the forward and reverse arithmetic, followed by at most J-1 multiplications for the product. Initializing and storing O(T+J) values/adjoints takes O(T+J) memory and elementary bookkeeping. This bound includes circuits whose intermediate degree is large; it does not require explicitly expanding any polynomial in the weights.

If parameter preprocessing uses inversions independent of w, they can be precomputed as constants before running this argument. Over Z/N each such inverse must be licensed by a unit gcd test or return a proper factor; a saturated nonunit requires its separately proved recovery rule. Treating those inverses as free unexplained constants is not permitted. The clean sufficient contract above keeps the weight circuit division-free.

## Connection with the sparse moment stream

If P_L(T)=sum_(k=0)^L c_k T^k and s_k=sum_j w_j z_j^k, then

    sum_k c_k s_k = sum_j w_j P_L(z_j)=F(w).

Thus a fast formal inner-product program combining the implicit q-binomial coefficient stream with the sparse-exponential moment stream would meet the stated contract. Reverse AD would recover all P_L(z_j) at the same asymptotic arithmetic cost, despite the weighted sum itself having no ANY-collision semantics. This is a concrete positive reduction, not merely an analogy to transposition.

The unresolved step remains building that fast FORMAL weighted-inner-product program without reading L dense coefficients or producing L moments. Existing cheap moment generation to length K costs soft O(J+K), so choosing K=L does not close the desired bound. No new algorithm removes that acquisition cost here.

## Proper-factor controller and scope

The resulting exact product preserves ANY zero in each hidden field. To obtain the existing canonical bisection recovery guarantee at softly linear total cost, the weighted program's cost and constant-acquisition contract must hold uniformly for the needed target subsets and contiguous exponent subintervals. A general q-Pochhammer interface with public origin/start and length supports those restrictions by explicitly transporting the origin; an algorithm ONLY for one full-grid instance does not automatically supply them. Reverse AD preserves the cost of each permitted invocation; it does not create unpromised parameter coverage.

The bridge proves no scalar lower bound and supplies no fast inner-product evaluator. It demonstrates that an efficient formal arbitrary-weight linear observable is a sufficient positive target for whole-batch acquisition, even when its internal calculation is nonlinear in the weights and even over the composite base ring.
