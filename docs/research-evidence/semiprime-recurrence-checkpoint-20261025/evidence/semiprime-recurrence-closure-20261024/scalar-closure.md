# Scalar q-Pochhammer closure: transported half-GCD inputs and an executed binary norm forest

24 October 2026. Scratch only; no repository changes, numerical examples or backend work. This pass executes the binary/remainder idea with the CORRECT varying quotient modulus, and closes its scalar norm recurrence exactly. The scalar recurrence is genuine, but acquiring its bottom-block messages at the desired clock remains unproved. A fully initialized completion costs soft(L+J); a transposed cut gives the already available soft(J+sqrt(JL)) bound with full original recovery. Neither is claimed as a new query exponent.

Read the terminal Toda report and the earlier scalar tensor/resultant audits. Their q-hook boundary, additive-minor norms, q-holonomic degree-J cost and fixed-quotient scaling defect are credited, not republished as new theorems. The present state changes the quotient ideal when it shifts. It retains the FULL original covered F/grid source and every original row/index label, rather than replacing it by an unproved small family.

## Primary search and exact applicable scope

Michael Monagan, *Probabilistic Algorithms for Computing Resultants*, ISSAC 2005, [primary author PDF](https://www.cecm.sfu.ca/~monaganm/papers/resultant.pdf), Algorithms PRES/MRES, makes modular bivariate INTEGER-resultant reconstruction output-sensitive in actual height/degree/content, with random auxiliary primes/evaluation checks. It receives explicit polynomial coefficients and computes their specialized univariate resultants. It does not state a deterministic scalar modular norm bound for an implicit long geometric polynomial. A small final residue modulo N does not supply its specialized input vectors or an early-termination certificate. Cached `sources/monagan-resultant.pdf`, SHA256 `94498929a8fdb2dd76fdee3de43b1be19f5c010e2fc39f83ad24cf7a1c39f60c`.

Emiris–Pan, *Improved algorithms for computing determinants and resultants*, J. Complexity 21 (2005), 43–71, [primary publisher page](https://www.sciencedirect.com/science/article/pii/S0885064X04000226), DOI [10.1016/j.jco.2004.03.003](https://doi.org/10.1016/j.jco.2004.03.003), advertises randomized output-sensitive bit bounds. Its [institutional report](https://academicworks.cuny.edu/gc_cs_tr/220/) was located, but full PDF retrieval returned HTTP403. Only the primary abstract/metadata are used; no uninspected theorem is promoted to the required deterministic soft-k routine.

The already inspected Asadi–Brandt–Moreno Maza *Computational schemes for subresultant chains* ([primary PDF](https://www.bpaslib.org/media/ComputationalSchemesForSubresultants-CASC2021.pdf)) permits requests for selected/nominal subresultants at the field half-GCD scale. It still requires actual coefficient operations. Its small-output option does not supply an implicit initial remainder, nor arbitrary split-ring pivot divisions. The previously checked Bostan–Yurkevich theorem still has its degree parameter; no claim is made that its fixed-degree sqrt-L headline changes when J grows. No new applicable scalar theorem was obtained from these targeted checks; this is not a claim about every algorithm in the literature.

## 1. Actual input and scalar resultant convention

Let R=Z/N for N=PQ, distinct odd primes. The supplied q is a unit with local orders>16k². Let L<=2k²+2, and let F be the acquired monic degree-J native target polynomial, with its acquired roots Y_j and original labels; J=O(k). The root metadata is genuinely available in the original source, not obtained by factoring a generic polynomial over R. Node and target differences have their inherited guards, while cross differences may vanish.

Put

    P_b(X)=product_(i=0)^(b-1)(X-q^i),
    F_v(X)=q^(-vJ)*F(q^v X),
    R_b(v)=P_b mod F_v, deg R_b(v)<J,
    S_b(v)=Res_X(F_v,P_b).

All F_v are MONIC. q-powers and the short coefficients are acquired; a degree-J F_v vector costs soft J to expand. Since F_v is monic,

    S_b(v)=Res(F_v,R_b(v))

is an exact ring identity, even at zeros. If R_b(v) is actually supplied, its scalar norm can be acquired by monic MPE at the known roots q^-v Y_j, then multiplication, in soft J. No Euclidean division by its possibly nonunit leading coefficient is necessary. This avoids assuming a common field-like subresultant degree profile across P,Q.

The requested original scalar is

    E_L=product_(i<L)F(q^i)=(-1)^(JL)*S_L(0).      (1)

## 2. Binary remaindering really closes when its modulus moves

For positive a,b the actual q-Pochhammer identity is

    P_(a+b)(X)=P_a(X)*q^(ab)*P_b(q^-a X).

The crucial ideal identity is

    F_(v+a)(q^-a X)=q^(-aJ)*F_v(X).

Therefore scaling a remainder modulo F_(v+a), rather than modulo the SAME F_v, is legitimate. It gives the executed update

    R_(a+b)(v)=q^(ab)*R_a(v)
                   *R_b(v+a)(q^-a X) mod F_v.    (2)

All reductions are ordinary MONIC divisions and all scaling factors are known units. This is an isomorphism between DIFFERENT quotient presentations; it is not the false assertion that q-scaling is a multiplicative endomorphism of one fixed quotient. No multiplication quotient is discarded.

Taking scalar norms in (2) also closes exactly:

    S_(a+b)(v)=q^(abJ)*S_a(v)*S_b(v+a).           (3)

To verify the second factor without a field assumption, evaluate at q^-v Y_j: its shifted argument q^-(v+a)Y_j runs precisely over the roots of F_(v+a). This proves (3) as a polynomial identity, including zeros. The scalar merge is purely multiplicative and introduces no new additive norm term.

This is a positive exact closure, but its state includes the varying parameter v. The right child is a DIFFERENT scalar endpoint. Equation (3) cannot be applied from only one already supplied S_a(v). The base S_1(v)=product_j(q^-vY_j-1)=(-1)^J*q^(-vJ)*F(q^v) is acquired from an actual F-value, not a constant-one startup for every v.

## 3. Fully initialized binary forest and its actual cost

Choose balanced child lengths (equal for dyadic blocks). For small blocks b<J, P_b has degree<J and is the common remainder polynomial independent of v. Acquire the O(log L) distinct short block polynomials by monic product trees or the guarded q-binomial coefficient formula, costing soft J across these short sizes. No target value is inverted.

Once block sizes reach J, each required state is an actual degree-<J vector. At block size b>=J there are O(L/b) starts. Acquire their F_v coefficients, transport the right state, multiply and reduce as in (2), each costing soft J. Thus this level costs soft(J*L/b). Summing the geometrically decreasing state counts gives soft L, with soft-J short startup and logarithmic overhead. Arbitrary L uses its real short last block. At the root R_L(0) is acquired, and (1) is obtained by the supplied-root MPE norm.

This is a complete inversion-free algorithm costing soft(L+J), with all data acquired. At L~k² it is soft k². Maintaining only scalar S states makes merges cheaper, but the same initial family of actual base/block scalar values still has to be acquired. This fact does not rule out a new simultaneous scalar algorithm; it identifies exactly which message acquisition this binary implementation has not compressed.

## 4. Executed transposed cut: scalar messages without all remainder vectors

Exploit the original known roots rather than run a separate half-GCD for every block. Choose b, put t=floor(L/b), and keep the actual remainder tail. Acquire the ONE explicit P_b of degree b in soft b, together with its factor product tree. For every j and block a=0,...,t-1 acquire

    Z_(j,a)=q^(-ba)*Y_j

by one known multiplier q^-b and actual power walks. There are J*t labeled points; their acquisition costs soft(Jt), not soft J. Evaluate P_b at all of them by MONIC multipoint evaluation, costing soft(b+Jt), even if points coincide locally. No inverse of a difference between these mixed points is used.

The complete full-block scalar is the explicitly verified expression

    E_(bt)=(-1)^(Jbt)*q^[J*b²*t*(t-1)/2]
                   *product_(j,a)P_b(Z_(j,a)).    (4)

Indeed every original factor q^(ba+i)-Y_j equals -q^(ba)*(Z_(j,a)-q^i). This proves the sign and scale in (4) without numerical division. The last r=L-bt<b original seeds are ordinary monic MPE of F, costing soft(J+b).

Thus the actual scalar-only completion costs

    soft(J+b+J*L/b),

optimized at b about sqrt(JL), clipped to [1,L], yielding soft(J+sqrt(JL)). This is the ROOT-SIDE/transposed form of the known blocking bound, not a newly improved exponent. At the sixth-root scale its explicit short polynomial and mixed-point list each have size about k^(3/2). They are not silently priced as the smaller input k.

If one instead chooses b~k so all initial short polynomials fit soft k, there are t~k shifted scalar messages, and the explicit mixed list has size Jt~k². Computing only their product by a new batched resultant would be the original short-input tensor contraction, not an already supplied consequence of (3) or of half-GCD output selection.

## 5. Nonunit cases, restrictions and original recovery

The value formulas and both completions remain valid at every hit. In the transposed cut, scan individual gcds of P_b(Z_(j,a)). A proper gcd factors N. If one saturates, descend P_b's acquired product tree at that fixed point. The sum of degrees along the descent is O(b), within the stated budget; a proper gcd factors, and a saturated leaf gives the ACTUAL original equality Y_j=q^(ba+i). All row/start labels were retained. The known unit scale in (4) does not change gcds.

Alternatively the already paid one-row geometric locator can handle that bounded block. A saturated original leaf uses its original bounded-beta decoder. Tail hits descend the retained F product tree at that actual seed. Auxiliary remainder leading coefficients are not passed to that decoder, and no subresultant-pivot inverse is performed at a nonunit.

For row subsets, use their actual acquired root/coefficients and degree. For a seed interval starting at u, replace the input target list by q^-u Y_j and retain u in its labels; the known scalar q-scale is charged, and final indices are u+ba+i in the original retained horizon. Empty products and bounded dimensions use direct evaluation. Thus all recovery and restriction capability is real, not inferred from an unrestricted known-zero norm alone.

## 6. Native bounded-chain test, with the correct scope

Could the native exponents make the shifted scalar messages coincide cheaply? With Y_j=beta^(N+delta_j), delta_j in [-3H,H], H=k², consider a proposed GLOBAL q relation Y_j=q^r Y_h with |r|<=L<=2H+2. It gives

    beta^[delta_j-delta_h-Hr]=1 modulo N.

The absolute exponent is at most 4H+HL<256H², below the prepared global beta order. Hence it is zero AS AN INTEGER. Thus delta_j-delta_h=Hr, and the acquired residues delta modulo H classify all such bounded-displacement relations. Sorting them costs soft J. Each class has at most FIVE distinct integer offsets, so any shortcut using just these certified bounded chains retains at least J/5 starting classes.

This is NOT a bound on a full global q-orbit: very large shifts modulo an unknown group order could connect additional roots. Nor is it a statement about one hidden local field, whose orders can be smaller than the global bound. No free discovery, safe long exponent or short endpoint evaluation for those unbounded shifts has been supplied. This scoped test rules out a power saving from the particular small integer-chain grouping; it is not a general lower bound or a new counterfamily.

## 7. Scalar-only half-GCD/continued-fraction contract and stopping point

The resultant objective needs only Norm(R_L(0)), not every vector in the forest. Half-GCD or a continued-fraction/nominal-subresultant routine may indeed omit many OUTPUT coefficients. Its initial large-degree division still requires an ACTUAL P_L mod F (or equivalent accessed operations), and its subsequent scalar pivot depends on the actual mixed remainder coefficients. A short leading q-binomial prefix does not provide that initial remainder merely because only one scalar is finally requested. This is an input/operation statement about these implementations, not a theorem excluding a specialized implicit remainder algorithm.

The exact scalar recurrence (3) shows a promising distinct positive contract: acquire all bottom-block S_b(v) needed by one dyadic merge tree, or directly their scalar product, from the shared q-scaled F data without expanding either b+J*L/b or Jb+L/b data. Every unit/zero case and interval restriction must be retained. With b~sqrt L, the three short inputs already fit soft k, but that simultaneous nonlinear scalar contraction is still the unpaid operation. Calling it an output-sensitive resultant, a compact continued fraction or a scalar norm does not instantiate it.

Delivered: lawful quotient transport, a closed scalar norm merge with actual initialization, a zero-safe complete binary algorithm and a fully executed transposed scalar cut with exact signs, costs and recovery. The covered source never changed. No deterministic soft(J+sqrt L) scalar endpoint theorem was established by the inspected primary results, and no improvement over the existing soft(J+sqrt(JL)) guaranteed query is claimed.
