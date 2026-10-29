# Hybrid audit: knot prefix bit through a cyclic resolvent and Cauchy core

26 October 2026. Read-only source/interface audit and direct finite algebra.
No tests, numerical campaign, executable changes or repository edits.

**Conclusion.** The interfaces really are complementary in one useful
sense: a cyclic model supplies both an acquired scalar norm and, at
rank O(J), an initialized inverse/linear action; the native knot supplies
an acquired degree-J polynomial; the weak consumer needs only a prefix
bit. The strongest immediate Cauchy/Schur handoff was executed below.
It preserves the desired predicate after a paid unit screen, but its
small core requires the native off-grid q-product again. At small cyclic
rank it is not an invertible full-clock intertwiner; at full clock rank
its inverse action is too expensive. This rejects that SPECIFIC hybrid
implementation, not hybrids in general or a future initialized structured
core algorithm.

## 1. Native topology-to-scalar and scalar-to-factor interfaces

Sources: [acquired Seifert/knot and weak consumer](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-knot-advancement-20261025/README.md),
[chosen twist-knot realization](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-knot-pair-20261026/README.md),
and [half-centre reduction](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-knot-prefix-20261025/README.md).
The source interfaces are listed again in Section 7.

After the paid central/unit screens, write the acquired ordinary knot
polynomial as

    K(T)=u*T^(-L)*F(T), F(T)=product_(a=1)^J(T-v_a),

with u a certified unit and each physical clock point z_i=eta*q^i a
unit. Here J=2L=soft k; m=O(k^(3/2)). Sparse integer Seifert data or
binary connected-sum twist data realize this scalar in soft J acquisition.
The complete twist-deformed polynomial is also acquired, but is NOT a
universal zero-preserving substitute for K. We use ordinary K here.

The empty prefix is handled directly. For any nonempty prefix define Q_m(T)=product_(i=1)^m(T-z_i). Up to the explicit
unit u^m*product_i z_i^(-L) and the sign (-1)^(Jm),

    product_(i=1)^m K(z_i) = unit * Res(F,Q_m).         (1)

Unit factors need not be numerically acquired for nonunit/zero predicates.
The existing full-window coverage supplies the promised endpoint. Exact
zero-only prefixes suffice under the old global-zero promise; nonunit
prefixes suffice under the weaker local-collision promise. Binary search
then isolates an actual F(z_i) nonunit. Signed root scans return a proper
gcd or a known short nonzero original exponent relation. A saturated
ADDITIVE matrix or moment zero has no such automatic decoder.

Consequently a new representation may safely replace (1) only if its
prefix bits agree after known unit multipliers, or if it has a separately
proved coverage and leaf decoder. A small descriptor or a fast linear
map alone is not this handoff.

## 2. Paid cyclic interface: scalar norm AND linear action

Take A_ell(T)=T^ell-c with acquired unit c, and the companion cyclic
operator U on R[T]/A_ell. For split F,

    det F(U)=unit_sign*product_a(v_a^ell-c).           (2)

This is the exact auxiliary cyclic norm, acquired in soft J using short
powering and a product tree. Choose c=1 for concrete decoding. Its
proper-gcd or saturated branches are localized to v_a^ell-1, supplying
the explicit nonzero short exponent ell*e_a when v_a=beta^e_a. Central
literal e_a=0 is removed by the existing preparation. Thus (2) is either
a legal terminating factor branch or a certified unit.

On the unit branch, when ell=O(J), the polynomial F mod A_ell and its
inverse mod A_ell can also be acquired in soft(J+ell), with the usual
factor-or-polynomial-gcd interface. A nonzero nonunit Euclidean pivot
returns a proper factor; globally zero coefficients are trimmed. The
resulting inverse is a genuine O(ell)-coefficient linear-action descriptor,
not merely an uncomputed dense inverse. Multiplication by it uses
polynomial multiplication/reduction in soft ell. This is the positive
operator input available to a Frankenstein construction.

It is important which inverse is paid. Although the scalar norm of the
long clock polynomial Q_m(U) is cheap too, its full inverse action is
NOT supplied by knowing that norm. In fact

    det Q_m(U)=unit_sign*product_(i=1)^m(z_i^ell-1),   (3)

one length-m geometric product of base q^ell, costing soft sqrt m.
The paid short-label order screen can certify ord_P(q^ell) and
ord_Q(q^ell)>16H or terminate legally. It then certifies every factor
in (3) a unit: ord(eta^ell)=ord(q^ell), and 0<2i+1<16H. But acquiring
Q_m mod A_ell, or its inverse operator, is a different task. A scalar
norm does not initialize those coefficients.

## 3. Strongest direct handoff: a Cauchy low-rank correction

Temporarily take the SAME degree n=m for the auxiliary polynomial
A_n(T)=T^n-1 and the physical Q_m. Over a splitting algebra let a_r
be the auxiliary roots and form

    C_(r,i)=1/(a_r-z_i).

The preceding order screen makes the cross differences units. Internal
physical differences are short-clock units; A_n is etale since n<P,Q.
Thus this is an invertible Cauchy change of basis on the stated unit
branch. Extension-coordinate or explicit m-by-m matrix acquisition is
NOT free. The construction is used here to derive its exact small-core
input before deciding whether the data can be initialized cheaply.

The exact finite displacement equation is

    D_a*C-C*D_z=1*1^t.

For F of degree J, telescoping gives

    F(D_a)*C-C*F(D_z)
       =sum_(s=1)^J f_s sum_(t=0)^(s-1)
          D_a^(s-1-t)*1*1^t*D_z^t.                   (4)

The right side has rank at most J. Therefore a determinant-lemma
contraction produces a J-dimensional correction multiplying the cheap
cyclic norm (2). This is an actual compatible pair of representations,
not merely naming a low-rank transfer.

One canonical exact J-core, avoiding numerical extension coordinates,
is the multiplication operator on B=R[T]/F

    M=multiplication by Q_m*A_n^(-1) mod F.           (5)

Its determinant is

    det M=Res(F,Q_m)/Res(F,A_n).                      (6)

The denominator is the already acquired and screened unit (2), with
only the known resultant sign convention. Hence det M has EXACTLY the
same zero and nonunit prefix predicates as (1). This handoff correctly
preserves collision zeros: no vanishing F(z_i) has been inverted.

If desired, a paid root-separation screen gives unit-separated native
v_a or a factor/short-annihilator termination. In that branch the
canonical core (5) is diagonalized by evaluation at those roots, with
entries

    Q_m(v_a)/(v_a^n-1).                              (7)

The denominators are initialized units from the cyclic screen. The
numerators are the full off-grid finite q-products. They have not been
computed by the sparse Seifert action, the cyclic scalar norms (2),(3),
or the weak prefix consumer. Acquiring their values jointly at the
existing bound costs soft(J+sqrt(Jm)). Computing Q_m mod F instead is
exactly another initialized form of that same missing geometric-product
remainder. Thus using (5) as an oracle for the prefix consumer is circular
unless a new algorithm supplies its action or determinant without those
values.

No claim is made that every rank-J Schur matrix is literally (5) or has
its eigenvalues. Equation (5) is a concrete canonical core with the right
determinant, and (4) is the finite rank-J Cauchy bridge. Both expose the
same remaining normalization scalar. Numerical matrix elimination at
collisions cannot replace the polynomial identities by dividing F(z_i).

## 4. Why choosing a cheap small cyclic rank does not finish the bridge

For ell=O(J), Section 2 gives a genuinely initialized cyclic inverse
and action. But the Cauchy matrix from ell auxiliary nodes to m physical
nodes is rectangular, rank at most ell. Its rank-one displacement is
still valid; it is NOT an invertible m-dimensional basis change and
cannot yield the determinant equality of the full physical operator.
Completing it requires the missing physical directions and their Schur
normalization. Those are not certified units merely because F(U) is.

For ell=m, the square bridge is algebraically lawful, and norm (2)
stays cheap. Its full polynomial inverse/action descriptor has m
coefficients and the direct initialized construction costs soft m.
The alternative rank-J core returns to (7). This is a concrete time/data
tradeoff for the attempted hybrid, not a lower bound for all implicit
Cauchy or determinant-only algorithms.

Using several cheap small blocks does not change this accounting for
free. Under the actual paid q^ell order guard, each auxiliary orbit has
at most one physical clock point per local component because distinct
z_i have distinct ell-th powers. An auxiliary-orbit union is therefore
not a compressed cover of this interval. Replacing auxiliary rotation
by arithmetic q gives the exact rank-one defect and block closure

    DC-qCD=c*(1-q^ell)*e0*e_(ell-1)^t,
    (xq;q)_ell*g_ell=y^ell*g_0.                      (8)

The coefficient is a unit; its being rank one does not make its Schur
scalar known. The cyclic block normalization in (8) is precisely the
collision-bearing q-product. Keeping it cleared preserves the desired
zeros, but acquiring all native blocks costs
soft(ell+Jm/ell+J), optimized at the existing bound. Dividing it away
would remove useful zeros and may invert a nonunit.

## 5. Can the cheap Bethe/moment alphabet initialize the core instead?

This is the natural second handoff, not assumed impossible. The reviewed
joint packet initializes O(J) moments in soft(J+sqrt m), and the entire
small epsilon core of the engineered TQ pencil in soft J. They provide
real extra data, unlike an unexpanded long diagram.

Their exact scalar contracts, however, differ from (5). Small Hankel
minors sum over J-element subsets of physical nodes. The full-support
norm is the size-m moment determinant, or the short dual determinant
whose rows contain Q_m(v_a). The TQ pencil obeys

    det M_epsilon=unit*product_(i=2)^m F(z_i)
                         *C(epsilon)*T_J(epsilon).

Its spectral normalization by the inverse bidiagonal F-diagonal block
divides out exactly the original product. Consequently replacing the
cyclic Schur input by the acquired moments or T_J coefficients has no
proved determinant identity with a known UNIT correction. One cannot
transfer just their small size and retain the scalar predicate. The
precise missing additional theorem would identify (5), or its prefix
nonunit bit, from that acquired alphabet without an F(z_i) inverse.

## 6. What survives, and what would make this a successful hybrid

The following composition is fully legitimate:

    acquired native F and knot
      -> paid cyclic norm/unit and short-label decoder
      -> explicit Cauchy rank-J bridge
      -> predicate-equivalent quotient core (5)
      -> existing prefix consumer, IF its bits are acquired.

The first, second and final consumer stages are paid. The core entry/
action stage is not acquired within soft(J+sqrt m); it retains (7).
Both cyclic marginal scalars can be cheap without their cross-norm
being known. Merely changing the requested output to one bit does not
supply the missing core initialization.

This audit gives a specific next target rather than a universal no-go:
a determinant-unit test for (5) initialized by the existing cyclic
resolvent and moment/TQ data, with collision-safe arithmetic and its
finite prefix dependence proved. A new formula of that kind really
would be a Frankenstein hybrid, not a renaming. The current machinery
does not contain that formula. No claim is made that every equivalent
zero predicate must compute the full norm value.

All scalar prefixes use the same finite physical interval, with the
original omitted origin/central labels preserved. They do not introduce
periodic completion or discard clock endpoints. Any auxiliary saturated
zero is decoded only when its explicitly factored short labels have
been localized; an arbitrary Schur or additive moment zero is not
silently sent to the original-annihilator extractor. T_ext is charged
once on a terminating branch, never called polylogarithmic.

## 7. Exact source interfaces

Local authoritative reports (read in this audit):

- `/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-knot-advancement-20261025/README.md`, Sections 1-2: acquired sparse Seifert realization and scalar-prefix consumer.
- `/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-knot-pair-20261026/README.md`: binary twist-knot realization and the distinct scalar-normalization scope.
- `/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-knot-collective-20261026/quantum-torus.md`, Sections 2-4,7: initialized cyclic norm, paid order screen, one-physical-point-per-orbit statement, exact defective native closure and cost.
- `/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-knot-joint-20261026/bispectral-string.md`, Sections 2-5 and addendum: acquired moments, exact short dual rows, and normalization of the TQ core.
- `/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-knot-colourcontraction-20261026/common-character.md`, Sections 2-3: actual finite domains and q-carry source maps; a character normal form is not an acquired interval-union norm.

Primary source context, with no additional theorem imported:

- Kashaev, *Quantum Dilogarithm as a 6j-Symbol*, Sections 1.1-1.2 and finite-product constraints: https://arxiv.org/pdf/hep-th/9411147 . The cyclic representation uses an auxiliary root, not the arithmetic q.
- Ishibashi, *Cyclic quantum Teichmuller theory*: https://doi.org/10.1007/s00220-026-05604-6 ; its phase correction is https://arxiv.org/abs/2610.23572 . Valid cyclic phase multipliers are units; native block normalizers need not be.
- Claeys et al., *An eigenvalue-based method and determinant representations for general integrable XXZ Richardson-Gaudin models*, Sections IV.1-IV.3: https://arxiv.org/html/1501.05827 . Its normalization variables are genuine input; short transfer ratios do not initialize every raw Cauchy/resolvent entry.

Equations (1)-(8) above are finite polynomial, resultant or displacement
identities, derived directly rather than imported from analytic knot or
Bethe-state hypotheses.
