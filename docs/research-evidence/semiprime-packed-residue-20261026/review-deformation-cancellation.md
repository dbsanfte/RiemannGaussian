# Independent review: noncovariant clock differentiation

26 October 2026. Paper-only review of `deformation-cancellation.md`. **PASS; no substantive correction required.** Original beta-coupled bank and its canonical weights remain explicit; no torus-only singleton promise is imported.

The contiguous polynomial identity (1) is exact. Since A_h=-sum e_i and B_h=-sum i*e_i, row differentiation gives A_h(rT)-A_h(T)=e_0-e_h. Clock differentiation at fixed original T correctly contributes BOTH B_h(rT) and A_h(rT) by the chain rule. Its right endpoint contributes -h*e_h, so equation (3)'s signs are correct. The homogeneous identity A_h+(1+s)D_h=h is also exact factorwise.

At a hit I, the delta residues are 1,-1,-I for D_h,A_h,B_h. Hence equation (6) has the displayed positive h endpoint correction. Its interior, I=0 exit and I=h entry cases agree separately. This decomposition really retains the interior count as a correlated clock-Euler difference; it is not an endpoint-only identity and is not rejected by the older covariant-shift cancellation argument.

The tangent ring with epsilon²=delta²=0 legitimately acquires first derivatives and an optional mixed term at constant rank. The starts must remain independent of the formal clock parameter when computing B_h; the report explicitly makes that convention, and separately includes the chain-rule A_h term. The shifted run at the acquired native start rho*T_j computes B_h at that point, rather than silently differentiating the start again. Binary powering in the tangent ring supplies i coefficients without materializing Jh leaves.

At globally zero rows, the additive derivative gamma=hG−T G′ is a global unit because each local row has exactly one clock hit. The ratio beta_j/gamma_j therefore returns -I componentwise with a licensed inverse. Unit rows contribute zero residue. Norm/coordinate classification handles mixed components or returns a factor; no zero mass is inverted. The shared monic engine and fixed-rank coefficients retain the old soft(J+sqrt(Jh)) bound. Counts from scalar flags remain a simpler baseline after those same row values are acquired, as the report notes.

The finite multisection lengths m+1_(a<r0), shifted arguments T*r^a and bases r^b in (7) are correct. The Euler chain rule a*T′partial_T′+b*r′partial_r′ in (8) recovers I=a+bk. The emitted Jb starts and the alternative b+J*ceil(h/b)+J blocking ledger are explicitly charged, with the last block retained. Balancing b near sqrt(Jh) gives the stated baseline, not soft K. No assumption of root-of-unity closure or invertible native collision values occurs.

Thus the report supplies a valid bulk-retaining alternative acquisition target and a complete old-rate implementation. It does not supply the cheaper correlated acquisition needed for an exponent improvement. Its conclusions are scoped to the executed multisection/tangent algorithm, not an arbitrary algorithm lower bound.
