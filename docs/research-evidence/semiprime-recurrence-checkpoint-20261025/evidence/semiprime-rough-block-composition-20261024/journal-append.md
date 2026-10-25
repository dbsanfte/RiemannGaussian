
## 2026-10-24: executed rough block composition and retained scalar contraction

No whole-query exponent gain is proved in this pass. The actual rough
quadratic source, all rows and original norm-leaf recovery are retained.
Three completed attempts acquire their stated inputs and terminal
values, but the best covered query remains soft(J+sqrt(JL))=soft k^1.5,
J=O(k), L=2k^2+2. The required new step is a scalar-only contraction
across shared block starts, with every original restriction and witness
label retained; small width, order guards and a scalar merge alone do
not instantiate that step. The one-sixth/full bit-and-Lean goal stays open.

First execute the bounded angular fibers, each of rank r_d<=16. With
C the companion class of the ACTUAL acquired monic fiber polynomial,
keep the external block start X and form

    R_b(C;X)=prod_(a<b)(C-z^a X) mod F_d(C),
    R_(a+b)(C;X)=R_a(C;X) R_b(C;z^a X) mod F_d(C).

The quotient modulus remains fixed because only X changes. This does
not assert the invalid endomorphism C->zC in a fixed quotient. For
C^2=sC-c, the first doubled state is
R_2=(s-(1+z)X)C+(zX^2-c); taking its determinant gives the acquired
quartic with X^2 coefficient z*s^2+(1+z^2)c and leading term z^2 X^4.
All first states across fibers cost soft J, with no pivot inversions.
The constant companion-coordinate coefficient of X^b is exactly
(-1)^b z^[b(b-1)/2], a UNIT; the fiber determinant has exact degree r_d*b.
This is a retained coefficient of this representation, not a generic
lower bound on another scalar algorithm or an output-size impossibility.

The scalar composition is actually completed. Set H_1(X)=(-1)^J F(X),
F(X)=prod_j(X-V_j), and acquire all coefficients through

    H_(a+b)(X)=H_a(X) H_b(z^a X).

The degree-Jb H_b costs soft(Jb); its L/b actual giant nodes, monic
MPE and clipped final tail give soft(J+Jb+L/b). Choosing b~sqrt(L/J)
returns the old soft(J+sqrt(JL)). The root-side dual pays the actual
J*floor(L/b) shifted target states and gives soft(J+b+JL/b). Neither
computes a second scalar start from one supplied first value for free.
Zero values and repeated targets remain legal under monic arithmetic.
A saturated FINAL NORM leaf is not whole split-side equality: only the
original nonsplit/G_beta consumer then yields a factor or a saturated
original scalar beta leaf. All interval offsets and row labels survive.

The bounded-width norm-last version was also executed. Partition norm
fibers by their cardinality r, interpolate their monic Phi_r(T,U), and
work over A_r=B[T]/G_r(T), whose ACTUAL coefficient rank is m_r. Its
block coefficients and giant evaluations cost
soft(m_r*(r*b+L/b+1)); the final norm uses acquired CRT norm nodes.
Summing and taking b~sqrt L costs soft k^2, because sum m_r=Theta(k).
Taking the norm first is cheap from the already acquired actual roots,
but returns degree J and the old k^1.5 completion. Width sixteen does
not make a growing norm-coordinate algebra constant rank or free input.

Roughness licenses actual small-power changes, but their costs and
comparators were checked. Common positive smooth m with O(log N) bits
preserves whole norm/angular incidence; the changed coupled seed is
actually rescreened. Native j^2 angular powering has an exact integer
square term and carry, but its seed becomes v^(j^2 i), varying by row.
No shared block for those different bases has been acquired for free.

A separate attempt actually roughens scalar beta as well as W. Its
fully factored smooth-killing exponent has soft-k BIT length; the
changed scalar order screen either certifies large orders or factors.
The common-one kernel branch is closed by complementary exponent trees
and simultaneous primary valuations, not a wide short-annihilator
oracle. Rows are reacquired and the changed coupled seed is rescreened.
Now jth powering is injective in EVERY local component. The quotient
1+Y+...+Y^(j-1) is a unit even at Y=1, where it equals the scalar j.
Thus powered/original norm leaves and EVERY restricted product have
exactly the same prime support, including split components and zeros.

The actual carry cancellation yields c_j=(N-a_j j^2+k b_j j)/H and
V_j^j=z^c_j R_j with an explicitly acquired beta/W residual. Removing
c0=floor(N/H) leaves |h_j|<=2k and the comparison

    Q_j=z^[j i-h_j], h_j=c_j-c0.

The row slope and centered carry remain; there is no free Gauss C_j
cocycle for the selected Cayley point. Expanding prod_j(X^j-V_j^j)
has exact degree k*phi(k)/2 and a soft-k^2 full completion. Separate
row-base blocks likewise cost soft(Jb+JL/b), optimized at soft k^2.
Undoing the unit power returns the better original degree-J query.
Inverse tags still retain [(a_star*a-1)P+a_star*ell-ell_star]/H; the
unknown P is not canceled by group injectivity, and the swapped index
is only bounded by O(k^3), not the original O(k^2) horizon.

Primary batching claims were checked with their actual contracts.
The current thin-matrix paper is [Alman--Vassilevska Williams, Truly
Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided
Graphs](https://arxiv.org/abs/2610.06783), v1. Its explicit integer-matrix
input, D<=S^(1/18) and sparse requested outputs are retained. The literal
native leaf matrix has constant inner dimension <=17; the blocked clock
has Theta(L) explicit entries and its coefficient input has Theta(Mb)
slots. The terminal product is not one bilinear output entry. Integer
lifts and constant-many quadratic-coordinate products DO give a valid,
zero-safe modular transfer; the domain is not the decisive obstruction.
Actual input/clock/rank/output costs stop these tested substitutions,
not a generic no-go theorem. The separate implicit tensor-encoding
followup in /tmp/semiprime-implicit-thin-encoding-20261024 is UNFINISHED
and contributes no result or acquisition bound to this packet.

Exact sources/reviews in /tmp/semiprime-rough-block-composition-20261024:
block-composition.md 5752e4192376b7351b3e003bc0dc0a4536b1a7d976de52d175465aaf63c941f2;
review 73c33f62e968a97c6d3cd3d775f9d491e027b52b58d5accf34bfc01dbd00e93f.
block-literature.md 86fd66adb32e7b18cdfaf787d2bde4971c93c0a14941f1ef9df0debaf54b2ee3;
review 542750c63f0e72d7362c26f593787ef774b4157d3bae9e9de6497cd7ed380ae0.
rough-index-cancellation.md 283cb2dd6b39f1c84aa62e488703bc2f68a89e3fda2d6620aa14a59dc5236da0;
review cf9afeef32415820baff4737b43b6f98ef77ca8c05ede1fcb4c87e951ea2b7b5.
All three exact sources have independent PASS reviews. No finite sample
campaign, broad Lean build, commit or push was used. Preserve all earlier
prefixes, 270 frozen entries and concurrent RH work; append preservation
is verified separately by the root validator.
