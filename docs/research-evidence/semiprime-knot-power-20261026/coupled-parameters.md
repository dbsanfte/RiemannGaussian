# Adjacent reciprocal weights and the finite-color resonance

26 October 2026. This executes a specific way to combine the independent-weight model with a finite-color module. It gives a four-state candidate for each adjacent pair, but no theorem yet transfers the required collision predicate to that candidate. It is not an acquisition improvement.

## Source and conventions

Garoufalidis–Kashaev, *Multivariable Knot Polynomials from Braided Hopf Algebras with Automorphisms*, [published version](https://doi.org/10.4171/PRIMS/62-1-3), Section 7.3, equations (110)–(116), Proposition 7.4, constructs a rank-4n module under

    t_1 t_2 z^n = 1,

where z is the auxiliary braiding parameter. Its stated proposition assumes z is not a root of unity. The argument uses explicit invariant vectors and finite coefficient minors; a modular application must check those minors rather than importing that assumption. Section 8 equation (124b) discusses a relation between the root-of-unity and generic families, with its proof deferred. We do not use it as a theorem. Section 7.2 equation (101) and Table 2 disagree in how they mark the two-Alexander-product assertion; independent-weights.md retains that source issue.

The arithmetic clock remains q=eta^2. Auxiliary z may be assigned q in an explicit finite construction, but this assignment alone does not preserve a knot scalar when z changes from 1 to q.

## Execute the adjacent-pair substitution

For i>=1, the required neighboring factors are

    K(eta^(2i+1)) K(eta^(2i+3)).

Reciprocity K(T)=K(T^-1) permits the exact replacement

    t_1=eta^(2i+1), t_2=eta^(-2i-3).

Then t_1 t_2=q^-1, and the resonance above holds with z=q and n=1. This is a uniform rank-four candidate; it does not require n to grow with i. Without replacing the second argument by its inverse, choosing z=q^-1 instead would require n=2i+2. Thus reciprocity materially improves the representation size of this particular candidate.

The invariant vector is explicit. Choose source parameters q_12=-1 and q_21=-q, so q_12 q_21=q. In the algebra with x_1^2=x_2^2=0, equation (112) gives alpha=t_2 and

    v=x_1 x_2+t_2 x_2 x_1.

Equation (111) now gives

    lambda_R(v tensor x_1)=(1-t_1 t_2 q)(x_1 x_2)x_1=0,
    lambda_R(v tensor x_2)=(t_2-t_2)(x_2 x_1)x_2=0.

These are polynomial identities, valid over the actual composite ring. The candidate span is (1,x_1,x_2,v). The source's generation step from 1 uses 1-t_1 and 1-t_2; both are native certified units because 2i+3 is inside the supplied short-order range. There is no intermediate k with 1<=k<n when n=1, so the higher-generation determinants of Proposition 7.4 do not enter this check. This verifies the finite invariant-vector and generation calculation; it is not a substitute for deriving every specialized braiding, rotated inverse and normalized knot map.

In the source's generic-color parametrization, t_1=1/(z^(n/2) t), t_2=t/z^(n/2), this candidate has

    n=1, z=q, t=eta^(-2i-2).

It therefore points at the first generic-color family, rather than automatically at the decoupled independent Alexander product.

## The exact unpaid bridge

At the decoupled value z=1, the same finite-color resonance requires t_1 t_2=1. Our supplied pair has t_1 t_2=q^-1 and q-1 is a unit. Consequently this pair cannot be held fixed while moving between the independent-product specialization and the finite-color specialization by the cited resonance equation.

A useful new theorem could still show, for an explicitly supplied native knot presentation, that the resulting four-state scalar has the same zero/nonunit predicate as K(t_1)K(t_2), with a legal original-leaf decoder. No such implication follows from the invariant-vector calculation. Equality of the ambient Yang–Baxter relation or the existence of a small module is insufficient. This is a missing identity, not a proof that no such collision-preserving identity exists.

Even a successful pair identity must be composed through a growing number of pairs. It would need either a closed composition law with paid initialization or a determinant algorithm attaining soft(L+sqrt(m)). Pairing once gives only a constant-factor reduction of m. A deformed knot invariant that requires a diagram or data beyond the acquired Alexander/Seifert input must also charge their acquisition.

## Current interpretation

Independent weights and reciprocity jointly supply a concrete, uniformly small two-mode candidate that was absent from the equal-argument Links–Gould specialization. The remaining question is now its exact coupled knot amplitude and a composable acquisition law. No generic-family identification, modular inverse at a collision, or exponent improvement is assumed.
