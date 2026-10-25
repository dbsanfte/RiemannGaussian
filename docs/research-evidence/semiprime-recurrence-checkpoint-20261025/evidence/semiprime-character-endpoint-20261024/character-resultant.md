# Character endpoint: square cancellation with paid auxiliary-support removal

24 October 2026. Scratch research only: no repository changes, numerical examples or backend work. The character-only output is sufficient but was already identified in the earlier character packets. This pass executes its interaction with the new q-hook-normalized Sylvester chain. No soft-m complete restricted detector is obtained. A positive refinement is acquired: the first two auxiliary-pivot degeneracies can be completely processed in soft m, rather than forcing immediate fallback when their scalar norms saturate. Later mixed pivot support remains unacquired, and the covered complete-query cost remains soft m^(3/2).

## Prior work and exact requested output

Read the tail of repository AGENTS.md and the reports `semiprime-character-aggregate-20261022/reports/reciprocity-observable.md`, `semiprime-composite-character-20261022/README.md`, and the current tensor packet `/tmp/semiprime-tensor-norm-20261024`. The old reciprocity report already identifies ternary Jacobi outputs, Boolean unit masks and adaptive subset queries as sufficient interfaces. Its known-zero-root warning, explicit-numerator requirement and positive deficit-count alternative are not new results here.

Let R=Z/N, N=PQ odd squarefree, q a prepared unit with all short differences 1-q^k certified units, F the explicit monic native target polynomial of degree J, and

    E(I,T)=product_(i in I) product_(j in T)(q^i-Y_j).

For public row/interval restrictions define U(I,T)=Jacobi(E(I,T),N)^2. Exactly U=1 for a unit product and U=0 for a nonunit product. Multiplicativity includes zeros. A restriction-stable soft-m evaluator of U would suffice: bisect a known-nonunit row/interval rectangle, paying logarithmic queries, until an original scalar leaf is retained. Proper gcds factor; saturated original leaves use the existing bounded original-beta decoder. The unrestricted U=0 supplied by coverage identifies no child. The target here is an evaluator, not this previously established interface.

For K=R[Y]/P(Y), P=B_t=product_(b<t)(Y-Q^b), Q=q^s, define

    C_K(a)=Jacobi(Norm_(K/R)(a),N),  U_K(a)=C_K(a)^2.

The grid differences are units, so K is publicly split as R^t. Proof-side CRT gives U_K(a)=1 iff every a(Q^b) is a unit in R. This definition does not provide Norm or its character at unit cost. No finite-field Euler exponent or hidden characteristic is an algorithm input.

## Relevant primary sources and their actual contracts

S. J. Patterson, *Note on a paper of J. Hoffstein*, Glasgow Math. J. 49 (2007), 243–255, p.244, gives the finite-field power-residue symbol as the character of a leading-coefficient-normalized resultant, and derives polynomial reciprocity by exchanging the two resultant arguments. He notes the corresponding Euclidean algorithm. The domain is F_q[X] with known field and character; this is an identity/Euclidean method on actual polynomial arguments, not an implicit tensor-norm acquisition theorem. [Primary PDF](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/97CF33036BA21B922A880C134B7F67EA/S0017089507003540a.pdf/note-on-a-paper-of-j-hoffstein.pdf), DOI [10.1017/S0017089507003540](https://doi.org/10.1017/S0017089507003540). Cached `sources/patterson-2007.pdf`, SHA256 `789082e8b99dbf97612bbc2e494ee37f237cc54a2a5ff70b5084e33f7cb04824`.

Mohammadali Asadi, Alexander Brandt and Marc Moreno Maza, *Computational schemes for subresultant chains*, CASC 2021, explicitly study acquiring only requested subresultants/nominal coefficients. Their field half-GCD framework has O(M(n)log n) field-operation cost; their consecutive-subresultant extension retains that scale. It takes supplied coefficient vectors and requires actual polynomial operations. Its integral-domain/partial-division discussion does not justify arbitrary division in the split composite K. Applying an O(soft n) coefficient-operation routine to acquired K-vectors still costs soft(nt) base-ring work; requesting only a resultant or nominal coefficients removes output but does not make those operations scalar. [Primary author PDF](https://www.bpaslib.org/media/ComputationalSchemesForSubresultants-CASC2021.pdf). Cached `sources/subresultants-CASC2021.pdf`, SHA256 `d22d1b2b5c33d2c3f14631fd28b50fe57fe88800a71800bc629cf5071e2ebf0a`.

Hsu's *On polynomial reciprocity law*, JNT 101 (2003), 13–31, [publisher page](https://www.sciencedirect.com/science/article/pii/S0022314X03000209), confirms a resultant relation and reciprocity laws. Only its abstract/metadata were inspected here; no extra complexity theorem is attributed to its unavailable full text. The known sparse-integer-symbol lead from the old report is not silently used for factored geometric products.

## Tangible cancellation test: the square multiplier and its zero support

Take the balanced acquired tensor input s=J=n>=3, t=floor(L/n), with the genuine short tail separately paid. Normalize B(X)=Y^-n F(XY), which is monic, and write

    C=A_n-B,  c=lc(C), d=next(C), h=c*b_(n-1)-d,
    D=c²B-(cX+h)C,  deg_X D<=n-2.

The whole first D is acquired as six Laurent exponents per coefficient in soft n, as proved in the tensor report. On the generic degree profile deg C=n-1, deg D=n-2, the exact polynomial resultant identity is

    Res_X(C,D)=(-1)^n*c^(2n-4) Res_X(A_n,B).          (1)

One proof uses the ordinary remainder D/c² on the unit-c branch. Since C=A_n-B, exchanging A_n and B first gives Res(A_n,B)=(-1)^(n²)Res(B,C)=(-1)^n Res(B,C). The Euclidean remainder update gives Res(B,C)=c² Res(C,D/c²), while scaling that remainder by c² contributes c^(2(n-1)). Clearing gives (1), including its (-1)^n sign. The sign is a unit, so it disappears only after squaring the Jacobi symbol below. Universality extends the fixed-degree Sylvester polynomial identity before specialization. At degree-drop specializations use the same padded fixed-degree resultant polynomials; an actual-degree update must separately account for its degree change. No nonunit inverse is being performed by (1).

For n>=3 the multiplier is a POSITIVE EVEN power. Thus its unit character phase is removable, but its zero support is not:

    U_K(Res(C,D))=U_K(c) * U_K(Res(A_n,B)).          (2)

If U_K(c)=1, this is the desired support-preserving cancellation. If U_K(c)=0, the left side is zero regardless of the original resultant's unit status; (2) cannot be divided by a Boolean zero. The same issue occurs when an even normalization exponent is erased in a later Schur/Bareiss character recurrence. This is an exact trace of where this particular cancellation loses information, not a lower bound for character evaluation. For n=2 the exponent in (1) is zero, so that specific obstruction is absent; the small-degree query is already within the paid soft-m direct/blocking case.

The formal q-hook constants Delta_k are certified scalar units, so their own squared characters are indeed 1 and can be deleted. They certify p_k(0), not p_k(Y^-1) in K. Reversed p_k have unit leading coefficient, but that permits polynomial exact division before reduction, not erasure of their endpoint zeros. For instance p_1 is the already acquired c; its formal unit boundary did not establish U_K(c)=1. Polynomial reciprocity needs the actual exchanged remainder or its support; formal boundary symbols do not supply it.

## Positive refinement: remove the first two exceptional supports in soft m

The failure in (2) can be repaired at the first two stages without assuming generic pivots and without treating their zeros as original target hits. The following is an actual initialized branch, including saturated cases.

Write the top coefficients A_k,B_k as in the tensor report. Then c=P1(Y)/Y with

    P1(Y)=A1*Y-B1,

and the next fraction-free leading numerator, after multiplying by Y^4, is the acquired P2 of degree four:

    P2=(A2²-A1*A3)Y^4+B1*(A3-A1*A2)Y³
       +(B2*A1²+B1²*A2-2*A2*B2)Y²
       +A1*(B3-B1*B2)Y+(B2²-B1*B3).

A1 is a unit. The leading coefficient of P2 is the certified q-hook unit

    q²*(1-q^(n-1))*(1-q^n)²*(1-q^(n+1))
       /[(1-q)*(1-q²)²*(1-q³)].

All six input coefficients and these polynomials cost soft n to acquire. Their root bounds therefore hold in BOTH hidden fields, without any F-genericity assumption.

For each of P1 and P2 perform this procedure on the currently retained public outer-node list:

1. Acquire all polynomial values on those nodes by MPE (constant degree here, so soft t suffices), and compute each gcd with N. Every proper gcd is an immediate factor. Individual gcds are important: a single product gcd could saturate from different local zeros.
2. If no proper gcd occurs, each retained value is either a unit or ZERO MODULO N. Hence its zero-node list is now exact and PUBLIC. There are at most deg(P_i) such nodes, because the node differences and leading coefficient are units locally. If local supports differed, some individual gcd would have been proper instead.
3. At every such global zero node y_b, directly acquire the ORIGINAL inner slice

       e_b=product_(a<n) F(q^a*y_b).

   This is a short n-point geometric MPE plus multiplication, costing soft(n+J)=soft n per node. Inspect nonunit values and descend the acquired original F/root product tree as needed. A proper scalar gcd factors; a saturated ORIGINAL leaf invokes the existing native bounded-beta decoder. An auxiliary zero by itself never invokes that decoder.
4. If the original slice is a unit, retain its actual scalar factor e_b and remove the public outer node from the remaining modulus P. Monic exact division by the known factor Y-y_b is legal, with soft t total work for these constantly many removals. The residual CRT algebra still has pairwise unit node differences. On it the processed pivot is now a unit, as every retained pivot value was explicitly certified unit.

Across BOTH stages at most 1+4 nodes are removed. Even if a node was already removed, it is simply omitted from the next scan. Thus all guards, every degree-drop support case, original-slice evaluation, removal and optional scalar inversion/interpolation cost soft(n+t)=soft m. Small t can instead use a bounded number of direct original slices. If an entire retained algebra disappears, the already acquired original slice factors are the complete answer for that rectangle.

This strictly strengthens the old first-two-pivot experiment's “saturated auxiliary norm -> immediate fallback” policy: global auxiliary degeneracies can be safely discharged at the original object at this price. On the remaining algebra both first pivots are genuinely invertible; ordinary updates and the unit square cancellations are licensed there. The retained scalar factor multiplies its eventual result. No all-row table and no unguarded coefficient-ring inverse is used. This construction also works for a restricted interval's known start scaling and its actual row polynomial; each restricted query pays its own acquired coefficients and tail. No simultaneous free evaluation of every restriction is claimed.

## What remains to acquire after those two stages

This repair does not finish the endpoint. For the full formal chain, p_k has public degree at most k² in Z, and its reversed endpoint polynomial can have k² degree with unit leading coefficient. Given its ACTUAL acquired polynomial or values, the same support-removal procedure is valid and admits at most min(t,k²) exceptional nodes at that stage. But p_k's mixed coefficients and its values have not been acquired in soft m collectively. Inspecting all t entries at n stages costs soft(nt); acquiring an original n-long slice at each of up to t removed nodes also costs soft(nt). These are ledgers for this implementation, not general lower bounds or assertions that every native stage attains those bounds.

The character phase can avoid multiplying some already acquired unit norm factors. It has not supplied the missing mixed coefficients of additive Schur updates, their endpoint zero sets, or the required restriction decisions. Taking all even exponents modulo two before these zero guards changes the function being computed. Running the explicit polynomial Jacobi/half-GCD algorithm over each known grid coordinate is initialized but again pays the t factor. Running over K without component handling assumes incompatible degree profiles away; the two-stage cleanup above demonstrates how to handle the initial cases at actual cost rather than assuming them away.

A complete safe algorithm is now: execute these two cleanup stages, stop if an original witness/factor is found; otherwise keep the acquired unit slice factors and try a new paid mixed-pivot routine, or fall back to the original restriction-stable scalar product query. The latter can simply reacquire the whole original rectangle, so no division by an unknown removed value is necessary. Its cost remains soft(J+sqrt(JL)), or soft m^(3/2) here, plus soft m initialization. All original row/index metadata and the decoder horizon are retained.

The focused positive continuation is to acquire the support of ALL remaining mixed pivot polynomials with total paid scalar work soft m, or to prove a covered constant-size pivot set whose actual zeros force an original hit after the paid cleanup. The inspected primary reciprocity and subresultant sources do not supply either theorem. This is an applicability conclusion for the stated contracts, not an absence claim about all algorithms. No new deficit-sum result, full norm bypass, covered character detector, improved whole-input exponent, hidden field/order oracle, or backend lemma is asserted.
