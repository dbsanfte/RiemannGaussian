# A paid rank-two q-Sylvester pencil for the block kernel; differentiation still needs a scalar circuit

2026-10-16. Exact constructive interface, with no nearlinear diagonal or whole-query algorithm claimed. No repository edits or builds.

## A new paid generalized displacement

Let F(t)=P_L(t;q)=sum c_k t^k over Z/N, with every 1-q^r for 1<=r<=L a unit. Supply J distinct unit target nodes with unit pairwise differences, as on the retained source after public offset deduplication. Set B=J, T=floor((L+1)/B), a_n=Bn, X_n=q^(Bn), and

 C_(n,s)=c_(Bn+s), 0<=n<T, 0<=s<B,
 W_(s,j)=z_j^s, M=CW,
 Z=diag(z_j), Q_z=W^(-1)diag(q^s)W.

The operator Q_z is genuinely paid: multiplying a row value vector by Q_z interpolates its unique polynomial of degree<B, scales coefficients by q^s, and reevaluates at the original nodes. Its transpose is also fast. Unit-difference interpolation is valid on this stated actual branch. No assertion that the target set is invariant under q multiplication is needed for a DEGREE<B block polynomial.

Define the two publicly acquired endpoint vectors

 u_n=(1-X_n)c_(Bn),
 v_n=(1-q^(Bn+B))c_(Bn+B),

where c_(L+1)=0 if a complete block ends just past degree L. Then the EXACT generalized Stein/Sylvester pencil is

 M(I-q^L Z)-diag(X_n) M Q_z(I-Z)
       =u*1^T-v*(z_j^B)_j^T.                     (1)

Thus this particular block evaluation matrix has a rank-at-most-two generalized displacement whose operators, generators and fast actions are ALL paid in soft O(J+T+sqrt L) ring work, including common setup. This is not the unproved ordinary commutator generator for the full mixed matrix S.

Proof: set P_n(t)=sum_(s=0)^(B-1)c_(Bn+s)t^s. The finite coefficient recurrence, with no division, gives

 (1-q^L t)P_n(t)-X_n(1-t)P_n(qt)=u_n-v_n t^B.

The interior coefficients cancel. The last coefficient uses (1-q^(Bn+B))c_(Bn+B)=(q^L-q^(Bn+B-1))c_(Bn+B-1), also valid at the terminal zero. Since M is the row-value matrix of these block polynomials, P_n(qz) is exactly represented by right multiplication with Q_z. Evaluation proves (1).

All c_(Bn) and needed c_(Bn+B) are ONE shared selected-coefficient acquisition: O(T) indices within [0,L], plus the declared zero at L+1. They cost soft O(sqrt L+T), not T independent sqrt-L calls. The C and C^T clocks are the frozen block-transform theorem, and W, interpolation and their transposes cost soft O(J) with the stated nodes. Powers of q and z cost the ordinary absorbed logarithmic work. There is no inversion of 1-z_j or 1-q^L z_j: (1) is deliberately a pencil, including when its diagonal factors are nonunits. Memory is soft O(J+T+sqrt L), and bit cost has the usual soft log N factor for polynomial-size index lengths. At J~sqrt L, T~sqrt L all these operations and generators are nearlinear.

## Why the pencil does not yet provide the required diagonal

The desired S includes left evaluation at y_i=z_i^B and the ragged correction. The frozen mixed-matrix proof already pays its two actions and identifies diag S=F(z_i). Equation (1) gives a concrete new generalized displacement, not the ordinary YS-SY=UV^T needed by the existing Trummer extraction with Y=diag(y_i).

The algebraic compatibility issue can be stated precisely. For row-value orientation as above, Q_z Z-q^(-1)ZQ_z has rank at most one: exact q-commutation holds on all input polynomials of degree<=J-2, leaving only the top-degree interpolation boundary. But for Y=Z^B,

 Q_z Y-q^(-B)YQ_z
  =sum_(h=0)^(B-1) q^(-h) Z^h
       (Q_z Z-q^(-1)ZQ_z) Z^(B-1-h).             (2)

This is an explicit B-term boundary sum. No polylog-rank cancellation in (2), nor a fast diagonal theorem for the generalized pencil, has been proved. The B-term formula is an upper-bound representation, not a lower bound on its rank or acquisition cost. At B=J it is not a supplied constant-rank Trummer generator. Choosing Z instead of Y would require a corresponding source-specific root-map treatment on the left interpolation side; that too is unprovided. One cannot replace either operator by the other merely because their matrix-vector actions are fast.

This observation is stronger than saying that target shifting always leaves a finite carrier: the finite BLOCK kernel does have exact interpolation closure. It is weaker than closing the full high-degree F or acquiring its diagonal. A generalized-displacement solver or an exact boundary-rank collapse could still be productive.

## Determinant and Hessian routes: exact sufficient scalar inputs

There are simple exact differentiation identities for S:

 Phi(theta)=det(I+diag(theta)S),
 [partial Phi/partial theta_i]_(theta=0)=S_ii=F(z_i). (3)

A division-free formal scalar circuit for Phi with nearlinear construction/evaluation cost would therefore solve the row acquisition by reverse differentiation at that clock. But an action circuit for S is not such a determinant circuit. Matrix-free approaches that request Theta(J) actions cost soft O(J²) with the current action clock; this is a charge for that approach, not a lower bound on determinant circuits or the structured source.

Likewise x^T S y has mixed Hessian entries S_ij. Reverse differentiation pays its gradients and Hessian-vector actions, which are precisely the already paid matrix actions. It does not by itself return the selected mixed-Hessian diagonal. Turning the action circuit into a diagonal-Hessian routine is an additional algorithmic theorem, not an automatic application of the transposition principle. Dense intermediate entries, a ring extension carrying J independent tags, or J independent directions must be charged if used; none is necessary by theorem for all possible structured algorithms.

No paid determinant deformation, compressed Hessian-diagonal extraction, or bivariate diagonal evaluator beyond (1) was obtained here. The positive output is the explicit rank-two block pencil with paid generalized operators and no scalar-normalizer inversions. The missing result remains simultaneous mixed-diagonal extraction, perhaps via that structure, a compatible boundary theorem or another scalar observable.

## Provenance

The finite recurrence, interpolation closure, pencil, rank-one boundary and power expansion are proved directly here. Prerequisites are the frozen positive block transform, selected-coefficient primitive and mixed-matrix factorization; exact hashes are in manifest.json. The earlier Trummer literature only supplies a conditional ordinary-generator-plus-one-action interface and is not imported as a theorem for this new q-pencil. No field-only fast determinant solver, order oracle, factors, numerical experiments or Lean backend is used.
