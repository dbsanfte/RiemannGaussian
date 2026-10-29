# Even paired residues: singleton blocks and an executed lowering identity

26 October 2026. Paper derivations, scratch only. The complete factoring bound remains soft K^(5/4). The new useful interface is a simultaneous constant-pole readout on O(sqrt K) paired blocks; it is not acquired at soft K here.

## 1. Original-bank partition, including contents and axes

Use the ORIGINAL deterministic weighted Gauss bank: one row for each unit j modulo K=2*3^e, with the same deterministic Gauss choice for j and K-j. Put n=3^ceil(e/2), L=K/(2n). At a correct nonsplit-factor bin every hit has j=R modulo n. This is the all-content theorem in [pure-weighted-common-tag.md](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-fused-readout-20261026/pure-weighted-common-tag.md), not a primitive-only assertion.

For each unordered colour pair take a=min(j,K-j), and put it in block floor(a/n). Thus 0<=block<L. For each unit square u modulo n, each block contains exactly one pair with j²=u modulo n. Indeed the two residue offsets r and n-r have opposite parity; since n is odd precisely one gives an odd representative in that block. Neither endpoint is a unit. Equivalently two distinct representatives in one block cannot have equal residues, and opposite residues would have sum (2*block+1)n, which is odd whereas their sum is even.

Consequently every block has at most ONE good-field hit: all hits have the same square tag u*=R² modulo n, and opposite orientations cannot both hit because 2R is a unit modulo n. Each block has phi(n)/2 pairs, and the entire partition is acquired in soft K by direct integer bucketing. No Hensel enumeration or sorting is required. This does NOT apply to a completed catalogue with multiple rows of the same colour.

## 2. Unit amplitudes now suffice; empty blocks still matter

Let rho=q^-1, with the actual shifted row variable z_j and clock 0<=i<h, so leaves are 1-z_j*rho^i. Set

 c_i=(-1)^i rho^(i(i+1)/2) [h-1 choose i]_rho,
 kappa=(rho;rho)_(h-1).

The exact finite partial-fraction identity is

 sum_(i=0)^(h-1) c_i/(1-z*rho^i)=kappa/(z;rho)_h.                 (1)

It follows either by partial fractions at the h distinct poles or the finite q-binomial theorem. The c_i are implicit unit formulas, not an acquired length-h list; emitting all of them costs O(h). All c_i and kappa are global units: their factorial factors use only the actually screened short differences. No unknown order is computed.

Regulate every leaf by +delta. Then

 sum_i c_i/(1-z*rho^i+delta)
   =kappa*(1+delta)^(h-1)/product_i(1-z*rho^i+delta).             (2)

Sum (2) over the rows in a block, and also after multiplication by the canonical INTEGER tag w_j=[j²]_n. Let V and U be the delta^-1 Laurent coefficients. At the good field an empty block has (V,U)=(0,0); a nonempty block has (V,U)=(A,A*u*) with A nonzero. This follows from singleton support and unit c_I, without a cofactor normalization or an unknown Hasse degree. The sign-paired sum of two inverse row products has at most a simple pole globally, even if the other component has two hits. An inverse of the paired product itself can have pole order two there; it is a different readout.

Norm(V) gives a proper factor, certifies V a unit, or permits declining that block. A unit V yields the correct square tag at the good field; its two public square roots modulo n feed the already proved soft-K factor consumer. A correct bin has a nonempty block. Only the first successful unit block PER BIN needs a factor-consumer call. A wrong-bin failure declines that bin and processing continues to later bins; this is not global termination. An arbitrary subresultant ratio cannot replace this readout: unless it is also certified zero on EMPTY blocks, its first unit denominator need not identify a true tag.

## 3. All short rational inputs and short moments are paid

For each block acquire

 r_b(X)=sum_(j in b) 1/(1-z_j X),
 s_b(X)=sum_(j in b) w_j/(1-z_j X).

Product-tree rational addition acquires all their numerators and denominators in soft K. Repeated row roots are legal, and no Vandermonde division or F' inverse is needed. Each denominator has degree phi(n)=Theta(sqrt K). The shared linear functional in (1) has moments

 mu_t=sum_i c_i rho^(it)=(rho^(t+1);rho)_(h-1),
 mu_(t+1)/mu_t=(1-rho^(h+t))/(1-rho^(t+1)).                   (3)

Acquire mu_0 by the scalar q-factorial engine in soft sqrt(h), then O(sqrt K) moments by (3). Only O(sqrt K) common moments are materialized. Their denominator and numerator exponents are covered uniformly by the inherited short-order screens: with d=phi(n*)<=K/3 and h<=8K^(3/2)+9, one has h+d<16K² for K>=16 (in particular every prepared K>=54). Thus total rational inputs and this short common moment vector cost soft K; the length-h c_i array remains implicit.

However applying these short moments to a rational function is NOT finite polynomial quadrature. Expanding its denominator gives an infinite series; an exact finite-clock pole is precisely where evaluation of that series cannot replace (2). A degree-Theta(sqrt K) Padé approximation matching these moments is not an identity for the rational inputs at the supplied row parameters. This report supplies no such substitution. The concrete remaining primitive is: compute the two negative Laurent coefficients in (2), jointly for this O(sqrt K)-block collection, from these acquired rational inputs and the finite q-binomial functional. A method must retain zero on empty blocks.

## 4. Execute an AW lowering candidate without discarding its scalar

For P_h(c,x)=(cx,c/x;rho)_h, direct multiplication of the two shared length-(h-1) strings proves

 P_h(c,rho^(1/2)x)-P_h(c,rho^(-1/2)x)
 =c*rho^(-1/2)*(1-rho^h)*(x-x^-1)*P_(h-1)(c*rho^(1/2),x).   (4)

The acquired square root rho^(1/2)=pi^(-H/2) is legal. With regulated leaves, the right side gains exactly the factor (1+delta), and P is replaced throughout by product_i[(1+delta)-cx*rho^i][(1+delta)-c/x*rho^i]. This is a division-free polynomial identity, valid over the actual composite algebra, including zero factors.

Equation (4) is an exact finite divided-difference lowering rule. To obtain the original P_(h-1)(c,x), its left side needs P_h(c*rho^(-1/2),rho^(+/-1/2)x). These are the products on (cx,c/x*rho^-1) and (cx*rho^-1,c/x), respectively. Both contain the original long common product P_(h-1)(c,x), differing only in two endpoint factors. Thus lowering does not initialize this product or its pole. Iterating (4) computes ordinary polynomial coefficients of growing degree, or requires these unacquired neighbouring long values. The varying native centres c_j cannot be replaced by a common AW parameter. This is a scoped failure of this particular initialized lowering attempt, not an exclusion of other AW/summation algorithms.

The older Ismail–Stanton connection/fringe identity is credited in [primitive-asymmetry.md](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-primitive-pair-20261026/primitive-asymmetry.md), source equation (2.4): https://www-users.cse.umn.edu/~stant001/PAPERS/AndrewsFormFinal.pdf . Equation (4) above is proved directly; no physical knot normalization or unavailable orthogonality integral is imported.

## 5. Honest completed algorithm and exact outstanding handoff

The existing shared division-free row-value engine obtains ALL row products in soft K^(5/4). Norm and coordinate classification either factors or certifies every row value globally zero/global unit, using the nonsplit component. Hence ordinary hit flags already acquire the whole-bin count/squared-tag pair at that cost. The block construction does not improve this baseline.

Alternatively the same engine over a constant-rank jet algebra acquires (2)'s simple-pole coefficients with constant overhead: at a globally zero row the first derivative is a global unit because each local row clock has at most one hit. No growing Hasse precision or root separation is required. This is an initialized finite-depth method, but still soft K^(5/4).

The new block theorem removes cancellation and unknown normalization from the prospective faster readout: arbitrary UNIT clock amplitudes are acceptable, while sign symmetry, nonprimitive coverage and axes are retained. What remains is simultaneous rational finite-Lambert pole evaluation, not a further decoder or tag acquisition. Short moments and AW lowering have been explicitly executed above; neither yet contracts those block poles in soft K.
