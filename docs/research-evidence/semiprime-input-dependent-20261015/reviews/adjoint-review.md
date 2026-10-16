# Independent review: formal-adjoint positive interface

2026-10-15. Verdict: PASS, with no substantive correction requested.

Reviewed exact artifact implicit/positive-adjoint-interface.md SHA256 c703190ef3e657a3375e8b681e45e3353a85cdcedde01f5a8a6abb5b749243d7. This review verifies the self-contained algebra, gate count, zero-divisor domain and restriction contract; no external literature theorem is needed.

## Formal identity and reverse correctness

The sufficient premise is properly stated as a branch-free (+,-,*) straight-line circuit computing F(w)=sum_j w_j a_j as an identity in R[w], with public parameter constants independent of the weights. Formal derivatives obey the sum/product rules over every commutative ring. Thus the displayed reverse accumulation computes (partial F/partial w_j)(0)=a_j exactly. This remains true with shared nodes, repeated operands, nonlinear intermediates that cancel, zero divisors, positive characteristic and zero target values. No target or residual inversion is used.

One can formulate the reverse induction directly on the acyclic circuit: after processing all descendants of a node, its adjoint is the accumulated formal chain-rule derivative of the output with respect to that node, evaluated at the stored forward values. Each reverse gate adds precisely the two correct incoming contributions. For repeated operands these are two contributions to the same adjoint and must both be added, as the report specifies.

The distinction from pointwise finite-ring agreement is essential and correct. In F_p, adding w^p-w changes the formal derivative by -1 while preserving every point value. A numerical oracle agreeing on ring elements alone cannot be differentiated to get the promised coefficients. The report does not grant access to such an oracle as if it were a formal circuit.

## Operation and space counts

Let T count arithmetic gates. The forward pass costs T operations. An addition or subtraction costs at most two reverse additions/subtractions. A multiplication costs at most two reverse multiplications and two additions. Therefore forward plus reverse costs at most 5T arithmetic operations. Multiplying J>=1 resulting values uses J-1 further multiplications, giving the claimed 5T+J-1 upper bound. This is an upper bound even when some contributions are zero or constant adjoints can be omitted.

The stored forward values, gate adjoints and J input adjoints occupy O(T+J) ring elements and bookkeeping entries. Circuit size and preprocessing are charged separately as the contract requires. If the output is itself an input or constant with T=0, seeding that output node's adjoint directly gives the same conclusion; this harmless degenerate implementation detail does not change any bound.

Neither polynomial expansion in the weights nor a bound on intermediate formal degree is necessary. Evaluation and reverse propagation operate on ring elements and the finite gate graph.

## Constants, units and parameter restrictions

The report correctly forbids treating parameter-dependent constants as free: their acquisition cost is part of the primitive. Inversions independent of formal weights can be preprocessed only with the stated unit/factor/saturation handling; inversions depending on weights are outside the clean division-free circuit premise. A weight-independent parameter branch may choose a parameter-specific circuit, but that chosen circuit must still satisfy the formal polynomial identity and its acquisition clock.

The moment identity sum_k c_k s_k=sum_j w_j P_L(z_j) is exact by finite distributivity over R. Therefore the proposed implicit coefficient/moment inner-product circuit, IF acquired with the required bound, is enough to recover all values and hence their product through reverse AD. The report clearly says no such fast circuit has been constructed and does not erase the L-term acquisition cost of the ordinary transform.

Finally, the bisection controller needs the primitive uniformly for target subsets and exact contiguous exponent subintervals, with transported known-unit origins and paid constants. The report explicitly includes that restriction-stability condition; reverse differentiation alone does not create a promise for unhandled parameter instances. Consequently the bridge does not imply a complete factorizer from a program handling just one prescribed full rectangle.

This is a valid conditional positive matrix-free interface, not an achieved nearlinear evaluator, a scalar lower bound or a new Lean endpoint.
