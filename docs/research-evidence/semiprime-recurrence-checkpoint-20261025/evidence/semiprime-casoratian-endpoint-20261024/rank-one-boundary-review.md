# Independent review of the finite rank-one boundary attempt

24 October 2026. PASS. Root reviewed the independently authored report
rank-one-boundary.md at exact SHA256
`8d0d5e13b23cc95835e567bd71bda2d3024c5338bb7e3a0bc3f3020d88e841a7`.
The finite-normalizer source `5aa07471d0d2c514b62eff39c1b5f77eb247632cc15c0907eef82dff32f6bea4`
and transport source `f813dc08c143a108758bd4a286bc601ded2a854b3a5c5bdb4693fc2695fca360`
were read in the preceding pass and their current bytes revalidated.

With M=diag(a)R, choosing v^T=1^T R gives exactly
(M+epsilon*1*v^T)=(diag(a)+epsilon*1*1^T)R. The determinant is
affine in epsilon over any commutative coefficient ring; its first
coefficient is det(R) times the sum of the diagonal cofactors of diag(a).
There is no inversion of a_i, and the chosen short transpose action is
actually available. The block-diagonal version and class-weighted right
vector give the stated A,B. At the unique good zero A is nonzero and
B/A is the coarse label. Additive perturbation of amplitudes is used;
it is not silently identified with native root differentiation.

For full-r windows, insert b_h=a_h+epsilon into the common-product
identity b_t Z_(t+1)(epsilon)=b_(t+r) Z_t(epsilon). Its constant and
linear coefficients are exactly (3). If the endpoints are units,
substitution Z_(t+1)=c_t Z_t gives the lower-left transfer entry
(1-c_t)/a_t, with no missing factor of c_t. The endpoint batch is paid
by the earlier zero-safe MPE algorithm, including artificial endpoint
caveats. A supplied transfer matrix is not a supplied state.

At a unique interior zero, the elementary cofactor sum S_t is nonzero
and Z_t=0; the transfer only rescales S_t by c_t. The cancellation
claim is precisely for this tested normalization. Separate treatment
of deduplicated determinant classes and full-r shift windows avoids
an invalid transfer of class sizes or the original h ordering.

The t=r^2 orbit formula retains the mixed D power. The C=0 state
(1,r) cannot initialize a nonzero multiplicative orbit. Both complete
continuations explicitly pay for the missing long values or the native
reset, at the old soft sqrt(JL) rate. No faster determinant evaluation,
kernel oracle, saturated artificial decoder or generic lower bound is
claimed. This review does not claim the complete factoring goal or
repository preservation validation has been achieved.
