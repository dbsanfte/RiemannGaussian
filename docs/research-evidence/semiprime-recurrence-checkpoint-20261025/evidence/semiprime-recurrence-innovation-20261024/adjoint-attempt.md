# Initialized adjoint contraction attempt

24 October 2026. Scratch only; repository read only. Result: a cheap short scalar jet, but no acquired soft-J terminal determinant. This assesses a concrete adjoint algorithm and its failure, not a lower bound for all scalar algorithms.

## Actual initialized operation

Let C be multiplication by Y in R[Y]/F(Y), R=Z/NZ. Its companion representation is explicitly acquired from F. Define

    A(t)=product_(0<=i<h)(I-t*q^i*C),
    E(t)=det A(t)=product_(i,j)(1-t*q^i*Y_j).

To obtain the requested V=product_i F(q^i), use C inverse instead: V=(-1)^(Jh)(product_j Y_j)^h E_inv(1). Constructing C inverse uses only the supplied unit F(0). The following argument is unchanged under Y_j -> 1/Y_j.

Tested algorithm: compute the scalar logarithmic derivative by the adjoint identity, reconstruct it rationally from a short jet, then integrate/evaluate at t=1.

Since A(0)=I, all formal inverse operations here are legal even when E(1) is a zero divisor. Exactly,

    g(t)=E'(t)/E(t)=-sum_(k>=0) s_(k+1)*G_(k+1)*t^k,
    s_l=tr(C^l)=sum_j Y_j^l,
    G_l=sum_(0<=i<h) q^(i*l).

For K=J this is an actually acquired scalar projection:

1. Acquire s_1,...,s_K from the logarithmic derivative of the reversed F. Its constant coefficient is one, so polynomial differentiation and power-series division cost soft(J+K) with no integer or collision inverse.
2. Acquire q^h and its powers. For l<=K, G_l=(1-q^(hl))/(1-q^l), using guarded unit denominators. Batch certification/inversion costs soft K. Alternatively finite geometric-sum binary doubling computes each G_l in O(log h), division free.
3. Acquire g mod t^K in soft(J+K+log h), with no h-entry input or P_h remainder.
4. Recover E mod t^(K+1) from E'=gE and E(0)=1 in soft K, using fast series exponentiation with certified integers 1,...,K as units. Unit-separated nonzero roots imply J<p for each prime p dividing N, so K=J is admissible. A nonunit integer certificate factors N. One may instead retain the differential equation.

The resulting short scalar jet costs soft(J+log h). Its evaluation at t=1 is not acquired.

## Failure of the actual proposed terminal step

The tempting Padé reconstruction of g from O(J) terms is not initialized. Over characteristic zero with generic q,Y_j, all Jh numbers q^i Y_j are distinct, and

    g(t)=-sum_(i,j) q^i*Y_j/(1-t*q^i*Y_j)

has exactly Jh simple poles, all with nonzero residues. Its reduced denominator therefore has degree Jh. The supplied order/separation assumptions do not force a universal degree-O(J) collapse. Cross-family coincidences may help particular inputs but are not guaranteed. This generic symbolic degree check refutes this particular Padé shortcut; it is not a factoring counterfamily or a general arithmetic lower bound.

Ordinary reconstruction thus needs Theta(Jh) jet entries. Writing those entries already exceeds the target. At that length neither inverses 1-q^l nor integer divisions in integration are justified by the short guard. Division-free geometric doubling remains available, but must be charged. The safe initialized fallback is explicit product computation or the existing baby/giant scalar algorithm.

Direct evaluation of g(1) also fails as a hit-safe initialization: it requires tr(C*(I-q^i*C)^(-1)), and those inverses fail precisely at the native hits. Replacing the inverse with adj(A) removes the formal division but leaves leave-one-factor products unacquired.

## Exterior power and black-box contraction audit

Taking top exterior powers before multiplication gives exactly

    wedge^J A(1)=product_i det(I-q^i*C).

This is an initialized scalar recurrence, but its multiplier det(I-xC) has degree J. Existing scalar baby/giant evaluation costs soft(Js+h/s+J), minimized at soft(J+sqrt(Jh)). It is a valid fallback, not an exponent improvement.

For the original Schur matrix H_(r,c)=a_(h+r-c), a black-box bilinear action is exactly

    u^T H v=[z^(h+J-1)] (P_h(z)/D(z))*U(z)*V(z),
    U(z)=sum_(r<J) u_r*z^(J-1-r),
    V(z)=sum_(c<J) v_c*z^c.

U,V are paid short inputs. The far coefficient of their product with implicit P_h is not paid by ordinary short convolution. Basis choices recover individual far a_n. This does not show every determinant-only algorithm must acquire a far coefficient; it pinpoints the missing oracle in a bilinear/Krylov/adjoint implementation. Each action must be constructed and charged. Differentiation using H inverse is additionally invalid at zero-divisor determinants; the formal t=0 construction above deliberately avoids that error.

## Ledger

| Operation | Paid cost | Conditions | Actual output |
|---|---:|---|---|
| Companion C or C inverse | soft J | unit F(0) for inverse | explicit short operator |
| Trace jet s_1,...,s_J | soft J | constant-one series division | short trace jet |
| Geometric jet G_1,...,G_J | soft(J+log h) | short guarded units, or doubling | short geometric jet |
| E mod t^(J+1) | soft J | certified integers <=J | initial scalar jet |
| Short Padé terminal step | uninitialized | denominator generically degree Jh | no E(1) |
| Long reconstruction input | at least Omega(Jh) output work | long divisions checked or avoided | exceeds target |
| Top-wedge fallback | soft(J+sqrt(Jh)) | polynomial arithmetic, no hit inverse | actual scalar E(1) |
| Restrictions and gcd recovery | existing charge | no target-value inverse | existing recovery only |

At J~m,h~m^2 the acquired terminal algorithm remains soft(m^(3/2)). The short jet does not itself supply a gcd oracle or saturation recovery on restrictions. A fused scalar terminal evaluation avoiding both the Jh-degree rational reconstruction and unpaid far-boundary actions remains open.
