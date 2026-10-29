# Lawful geometric Alexander blocks: explicit initialized polynomial evaluator

26 October 2026. Scratch only. This executes one ordinary-exterior/diagonal-Nichols block, with an integral initialization and all collision factors retained. It does not establish a new whole-prefix exponent. The concrete output is a degree-b q-factorial polynomial evaluable simultaneously at all native roots; binary fusion of its short description still produces b coefficients. No generic KM independent-scaling construction is used.

## 1. Lawful input and the scalar to contract

Use the independent two-state Alexander models at the ordinary exterior point. Their tensor product, with meridian weights t_0,...,t_(b-1), has reduced scalar product_i K(t_i). Independent scaling slides separately through the super flip, so the ambient-morphism issue in the generic KM Hecke model does not arise. The exterior state rank is 2^b, but we will not acquire that state space.

Primary context: Garoufalidis–Kashaev, *Multivariable knot polynomials from braided Hopf algebras with automorphisms*, https://doi.org/10.4171/PRIMS/62-1-3, Sections 3 and 7, https://arxiv.org/html/2311.11528. Their diagonal generator braiding permits independent weights. Their equation (101) states the two-weight Alexander product, but the published summary table marks this same equality with a question mark; our chosen normalized tensor model has its own factorization proof and does not rely on resolving that discrepancy. The higher-rank construction here is the ordinary super exterior tensor product, not an asserted identification with an arbitrary higher-rank GK invariant.

We can use the acquired native factorization directly:

    K(t)=product_(j=1)^L [(v_j-t)(v_j-t^-1)/(v_j-1)^2].       (1)

Every v_j and v_j-1 is a unit following the central screens. Factors and repeated v_j are retained with multiplicity. Equivalently the jth factor is 1+c_j(t+t^-1-2), c_j=-v_j/(v_j-1)^2. This matches the proposed connected sum of genus-one twist factors; the polynomial calculation below does not need a particular topological diagram or an integer-lift twist convention. Acquiring v_j and c_j is soft O(L), including batch inverses when the screens have certified units.

## 2. Executed block identity, with no eigenvalue extension

Fix a block t_i=z q^i, 0<=i<b, where z is any acquired unit. For the native odd-weight prefix use z=eta^3*q^s with 0<=s and s+b<=m; it need not be a bare integer q-power. Take 1<=b<=m inside the supplied short-order range (and handle b=0 directly as the empty product). Define the single polynomial

    Q_b(Y)=product_(i=0)^(b-1) (1-q^i Y).

For each v, direct multiplication gives the finite identity

    product_(i=0)^(b-1) [(v-zq^i)(v-z^-1 q^-i)/(v-1)^2]
      = (-v/z)^b q^(-b(b-1)/2)
        Q_b(z/v) Q_b(zv)/(v-1)^(2b).                       (2)

The second product is obtained from

    v-z^-1 q^-i = -z^-1 q^-i(1-zv q^i).

Thus the full block is exactly

    product_(i=0)^(b-1) K(zq^i)
      = U_(b,z) product_j Q_b(z/v_j) Q_b(zv_j),            (3)

    U_(b,z)=(-1)^(Lb) z^(-Lb) q^(-L b(b-1)/2)
             (product_j v_j)^b / (product_j(v_j-1))^(2b).

U is an explicitly initialized unit. It costs soft O(L+log b) to obtain it from root products and powering. Equations (2),(3) require neither roots of a quadratic in c_j nor an auxiliary root of unity. They are finite Laurent identities over the actual composite ring. In particular, a collision factor is never inverted, and global zero and nonunit status are preserved exactly.

Initialization of Q_b is also explicit. In the supplied order range, 1-q^r is a unit for 1<=r<=b. Its coefficients are

    [Y^r]Q_b(Y)=(-1)^r q^(r(r-1)/2) [b choose r]_q,

and can be acquired consecutively from A_0=1 by

    A_(r+1)=-A_r q^r (1-q^(b-r))/(1-q^(r+1)).              (4)

Batch inversion makes the b denominators cost soft O(b); all are certified units from the local-order hypothesis. Alternatively a product tree builds Q_b without division. Formal q-series or infinite products are unnecessary. The degree is exactly b because the leading coefficient is the unit (-1)^b q^(b(b-1)/2).

Evaluate Q_b at the 2L points zv_j and z/v_j by monic subproduct trees, allowing coincident points, in soft O(b+L) ring operations. Multiply the evaluations and U. This is an initialized scalar evaluator for a lawful block, avoiding 2^b states and avoiding b separate full-polynomial evaluations. Its acquisition is soft O(b+L), not soft O(L+sqrt b). For b=O(L), a single block costs soft O(L), but it contains only b of the required M arguments.

Using nonoverlapping blocks and reusing Q_b gives the transparent bound

    soft O(b + (M/b)(L+b)) = soft O(b+ML/b+M),

including evaluating each shifted point list. That bound cannot improve the existing soft O(L+sqrt(LM)) whole-product evaluator. Treating the repeatedly shifted evaluations as free would be exactly the unpaid block contraction. The ordinary exterior block is therefore real, initialized, and useful as an interface, but not the desired new whole-family algorithm.

## 3. Concrete binary fusion and why its small descriptor does not initialize the scalar

The lawful binary composition is

    Q_(a+b)(Y)=Q_a(Y) Q_b(q^a Y),
    Q_(2a)(Y)=Q_a(Y) Q_a(q^a Y).                           (5)

The descriptor (q,b) has logarithmic size, and q^a is obtained by powering. Expanding (5) gives soft O(b) total polynomial work. Keeping it unexpanded instead makes evaluating Q_(2a)(Y) call Q_a at TWO different arguments. Repeated doubling has b leaves; ordinary scalar binary powering is inapplicable because the shifted argument changes. This is an exact accounting of this attempted fusion, not a general lower bound on all possible evaluators.

For the associated one-particle diagonal mode D=diag(1,q,...,q^(b-1)), the standard Krylov basis 1,D1,...,D^(b-1)1 has Vandermonde determinant product_(i<j)(q^j-q^i), a unit in our short order range. Therefore this particular cyclic one-particle compression has rank b over R: its companion characteristic polynomial is Q_b up to a unit/reversal, rather than a constant-order recurrence supplied by the tensor factorization. This checks the proposed determinant implementation specifically; it is not a prohibition on a zero-only algorithm using additional native arithmetic.

## 4. What skew Howe and satellites add to this block

Grant, *A generators and relations description of a representation category of U_q(gl(1|1))*, AGT16(2016),509–539, https://doi.org/10.2140/agt.2016.16.509, primary PDF https://msp.org/agt/2016/16-1/agt-v16-n1-p12-p.pdf, constructs a diagrammatic category generated by exterior powers and its skew-Howe braiding. This reorganizes a specified colored representation; it does not supply an initialized evaluation of (3) from the geometric alphabet without its Q_b coefficient/evaluation work. In particular, one exterior-power color is not a theorem identifying that colored scalar with a product of b independently specified Alexander values. We do not import generic-field projectors into R where their denominators may fail.

The already-audited Cimasoni splice formula, https://www.unige.ch/~cimasoni/splice.pdf, Theorem3.1 and connected-sum Corollary3.5, gives a genuine multivariable keychain encoding of the same independent product, but its b leaves explicitly carry b colors. Harper's parallel-cabling formula https://arxiv.org/abs/1911.00646 fuses colors into their product and hence one companion evaluation, not (3). Neither identity replaces the shifted pair of Q_a evaluations in (5) by a single initialized scalar. These are source-specific statements, not a blanket assertion about satellite compression.

## 5. Result and focused remaining target

We have a legal higher-rank ordinary-exterior block and exact all-native-root scalar evaluator (3),(4), with paid soft O(L+b) acquisition and an explicit unit boundary. This also works with the newly proposed binary twist-knot input without expanding crossings. It gives a clean test interface for a genuinely new contraction: accelerate the simultaneous shifted evaluations of this one Q_b at the acquired reciprocal native points, or derive a native-specific zero-equivalent replacement. Neither independent Cartan legality, binary knot twists, nor the cited skew-Howe/cabling identities currently pay that further step. No new factoring bound, numerical campaign, or repository edit is claimed.
