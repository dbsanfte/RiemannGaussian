# Independent review: coupled adjacent parameters

26 October 2026. Read-only finite algebra review; no experiments or repository edits.

**PASS for the limited positive bridge stated.** This is the separate diagonal Nichols model of GK Section 7.3, not the non-diagonal KM Hecke exterior braiding. The generic-p naturality gap identified in independent-weights-review.md does not invalidate this finite calculation.

For diagonal c(x_i tensor x_j)=q_ij x_j tensor x_i, independent scaling of each x_i satisfies separate sliding as well as simultaneous equivariance. Thus the ambient-morphism issue from KM's exchange term is absent here. The source algebra at generic auxiliary q has alternating-word basis with x_1^2=x_2^2=0; the following small submodule identities can be checked over the integral parameter ring and specialized, rather than invoking the generic-field dimension proposition without its hypotheses.

Reciprocity gives exactly

    K(eta^(2i+1)) K(eta^(2i+3))=K(t_1)K(t_2),
    t_1=eta^(2i+1), t_2=eta^(-2i-3), t_1 t_2=q^-1.

With q_12=-1, q_21=-q, n=1, GK equations (110)–(113) give alpha=t_2 and v=x_1x_2+t_2x_2x_1. Both action coefficients in equation (111) vanish exactly: 1-t_1t_2q=0 and alpha-t_2=0. The displayed invariant-vector claim is therefore polynomial and valid over R.

The rank-four spanning claim also survives the finite specialization. The basis 1,x_1,x_2,v is free because its degree-two vector v has coefficient 1 on the alternating word x_1x_2. The coproduct of v has terms v tensor 1 and 1 tensor v, with all remaining components of degree one, so it lies in this span tensor the ambient algebra. The two generators act on 1 by (1-t_i)x_i. On degree one, the same-letter actions vanish, and GK equations (115),(116) at k=1 give

    lambda_R(x_1 tensor x_2)=v,
    lambda_R(x_2 tensor x_1)=t_1 q v,

because t_1q*t_2=1. Finally v is annihilated by both generators. Hence the span is action-stable, contains the generated module, and is generated from v by its coaction, followed by the two actions on 1 and one action producing v. No intermediate determinant with 1<=k<n exists at n=1. Recovering x_i from those action values requires 1-t_i units, not merely nonzero elements; the report correctly supplies that stronger native condition. It should be read explicitly as requiring positive 2i+1,2i+3 strictly below both local eta orders, which holds for the supplied short native odd-weight range.

The generic parametrization also checks: q^(1/2)=eta, t=eta^(-2i-2), so 1/(eta*t)=t_1 and t/eta=t_2. This identifies the parameter point of the FIRST generic-color family, not its knot scalar with the independent Alexander product. The source's Proposition 7.4 assumes q not a root of unity; the calculation above validates only the displayed finite free span/action/coaction after modular specialization. It does not certify every specialized braiding rotation, rigidity inverse, normalized knot amplitude or generic-family identity.

At auxiliary q=1, the same n=1 resonance demands t_1t_2=1, whereas the held-fixed native pair has product q_arithmetic^-1, with q_arithmetic-1 a unit. Thus this resonance is not a fixed-parameter deformation path from the decoupled Alexander product to the coupled four-state model. The report correctly keeps the missing collision-preserving scalar identity and its acquisition separate. Even an eventual two-factor identity alone only halves the number of factors once; it does not produce a composable near-linear norm algorithm.

Primary check: published GK text, Section 7.3, equations (110)–(116), Proposition 7.4 and its proof; https://arxiv.org/html/2311.11528 . No additional source theorem is needed for the finite calculation above.
