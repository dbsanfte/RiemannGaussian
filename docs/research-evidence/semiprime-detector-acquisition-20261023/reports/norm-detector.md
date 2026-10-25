# Full quadratic orbit norm: guarded evaluator interface and unresolved specialization

2026-10-23. Scratch only. All 234 frozen entries and all repository files are unchanged.

## Verdict

**No new soft-O(r) detector or full-product evaluator has been acquired.** The skew representation below is an exact short descriptor, not a source-algebra evaluation algorithm. The useful constructive reduction is a guarded rational-evaluator interface: a pointwise zero-preserving output in a rank-soft-r row algebra would suffice, even without outputting the full product or its moments. Its denominators and its final local recovery can be paid explicitly. The missing operation is evaluation of the full moving-fiber orbit norm, rather than formation of another prefix.

## 1. Source interface and nonzero leaves

Use the latest all-input source with G=soft-O(r) public rows v and legally acquired units rho_v, beta0 satisfying

    rho_v^(a_v)=beta0,
    M=r^4,
    K_(v,c,sigma)=a_v c^2+B_v c+C_v N-M sigma,
    1<=c<r, sigma in I=[a,b], |I|=O(r).

Each C_v is a nonzero signed integer; all coefficients have O(log N) bits. The rho_v have odd local orders greater than 16r^2. Define actual row clocks

    W_v=rho_v^(C_v N), V_v=rho_v^(B_v), Q_v=rho_v^M.

The normalized leaf is

    1-beta0^(c^2) W_v V_v^c Q_v^(-sigma)=1-rho_v^(K_(v,c,sigma)).   (1)

This preserves the root-normalized source exactly, including canonical coefficient carries and signed seed endpoints. It does not substitute a common Q for different rows. Sharing rho_a among rows with the same leading coefficient a is compatible with (1), but no cross-a rank-r W relation is asserted.

The actual fiber has more structure than arbitrary row data: at a fixed a, the allowed C values are a clipped AP of step r, W_v is a GP of ratio rho_a^(rN), Q_v is the one shared Q_a, and V_v is the canonical cubic square-root clock on that AP with its centering carry. The detector subproblem below is required only on these supplied source fibers. Replacing this condition by arbitrary interpolated W,V,Q would be a stronger problem, and is not needed for factoring.

For the latest centered-B source with |a_v|<r/16, |B_v|<=M/2 and |sigma|<=4r, the public condition N>5r^5 makes every K nonzero, because

    |a_v c^2+B_v c-M sigma|<5r^5<|C_v N|.

If r<=2ceil(N^(1/6)), failure N<=5r^5 bounds N by 5120^6: writing t=N^(1/6)>=1 gives r<=4t and t<=5*4^5. Thus ordinary finite-range factoring is an admissible explicit fallback. This removes public-zero denominators from the large-input detector interface; it is not itself a new query advance. The older one-row-per-s AP family can alternatively peel its O(log N) exceptional rows by the direct one-row procedure below. That row-count argument is not transferred to the larger explicit (a,C) catalog.

## 2. A complete one-row recovery algorithm

For one specified row v, all c-targets

    T_c=rho_v^(a_v c^2+B_v c+C_v N)

and seed points Q_v^sigma are acquired in soft-O(r) bit work. Build the degree-(r-1) monic target polynomial and evaluate it at the O(r) seed points by ordinary monic product/remainder trees. Negative endpoints use the known unit inverse. Repeated points cause no difficulty.

A nonunit aggregate is localized to a seed and then a c by the product tree. A proper leaf gcd factors N. A saturated individual leaf supplies the explicit nonzero logarithmic-bit exponent K from (1), so the already paid unconditional unbalanced annihilator decoder applies to rho_v. This one call terminates the factoring path. A NoHit result certifies that every leaf in the specified row is a unit.

For the old AP row with its single public zero (c0,sigma0), split off c0, test all other targets against the full interval, and test c0 against the interval with sigma0 omitted. At most two seed subintervals arise. This costs soft-O(r), preserves all nontrivial leaves, and makes it legitimate to remove the entire checked row afterward. It is not the invalid deletion of an unqueried whole row.

In the detector compiler below this one-row algorithm is used only after one row has already been localized. Its cost is therefore soft-O(r) once, rather than G calls costing soft-O(rG).

## 3. The guarded rational-evaluator compiler

Construct a split row algebra A of rank G over R=Z/NZ with the exact values W_v,V_v,Q_v as elements. For example, interpolate them at distinct small integer metadata nodes. Nodes can be partitioned into blocks of at most r^2; all their differences are units because P,Q>16r^2. Fast product trees and interpolation cost soft-O(G) bits with the usual log N factors, and the full coefficient carries are retained in the values. This construction is row metadata, not query acquisition.

Suppose a proposed algorithm has all the following properties.

1. It uses soft-O(1) arithmetic operations in A, and soft-O(r) scalar input work. Monomial exponents have O(log N) bits; their binary powers add only logarithmic factors.
2. Each inverted expression is certified as a unit monomial times a product of soft-O(1) binomials of the form

       D=1-beta0^e W^i V^j Q^k.

   Across the entire algorithm there are soft-O(1) such guard types, and for every retained row their explicit integers

       J_v=a_v e+i C_v N+j B_v+kM

   are nonzero and have O(log N) bits. This certificate is checked; arbitrary complicated denominator expressions are not silently called units.
3. It outputs Y in A whose reduction in each local field, row by row, obeys

       Y_v=0  iff  product_(c,sigma)(1-rho_v^(K_(v,c,sigma)))=0.    (2)

   Exact product equality is sufficient but unnecessary. In particular a proved quotient by the checked unit factors is acceptable.

Then this algorithm gives a legal soft-O(r) factoring detector for the source.

Proof and ledger: evaluate each guard at all G supplied rows and scan its gcds. A proper gcd ends with a factor. A saturated guard at row v gives rho_v^(J_v)=1 modulo N, with the explicit nonzero short J_v, and the inherited decoder ends with a factor. On the surviving path every guard is a unit in every local row, so all rational operations are legal and any cancellation by these guards preserves local zero support. Batch inversion and interpolation implement each A operation in soft-O(G) bit work. With G=soft-O(r), this remains soft-O(r), including all guard scans.

Evaluate the final Y at all metadata nodes. Source coverage and (2) ensure at least one nonunit row value. A proper gcd factors immediately. Otherwise select one row whose value is saturated and run the acquired one-row algorithm from section 2. Condition (2) guarantees that it contains a nonunit source leaf; its direct localization and annihilator recovery cost soft-O(r). No short-annihilator claim is made for the arbitrary arithmetic expression Y_v itself.

This compiler explains exactly how a rational/continued-fraction or transfer-matrix construction can use cancellation safely. It is not a theorem that such a construction exists. In particular the adjacent-window ratio does not satisfy (2), because common local zero factors can disappear. Its cancelled denominator is not one of the acquired short binomial guards.

For one rank-G polynomial representation, arithmetic costs soft-O(G log N) bits and storage soft-O(G log N) bits. Conservative row-clock powering/guard evaluation costs soft-O(G(log N)^2). The compiler's total is soft-O(r), not soft-O(r^2), precisely because the number of algebra operations and guard types is restricted to soft-O(1). An algorithm taking r operations in A has not met this interface.

## 4. Exact full-product word in two skew shifts

Let D=R[W^(+-1),V^(+-1),Q^(+-1)]. Define commuting automorphisms

    Phi(W)=beta0 W V, Phi(V)=beta0^2 V, Phi(Q)=Q,
    Psi(W)=Q^(-1) W, Psi(V)=V, Psi(Q)=Q.

Introduce invertible skew shifts S,T with Sd=Phi(d)S, Td=Psi(d)T and ST=TS. For any integer c and sigma,

    Phi^c Psi^sigma(1-W)
      =1-beta0^(c^2) W V^c Q^(-sigma).                         (3)

These identities hold in the Laurent difference algebra before any row specialization. They use only unit clock inverses.

Let ell=b-a+1, c0=1 and n=r-1. Form the balanced skew word

    E=((1-W Q^(-a)) T)^ell T^(-ell),
    C=S^c0 E S^(-c0),
    H=(C S)^n S^(-n).                                          (4)

Both E and H actually lie in the commutative coefficient ring D. Directly expanding the skew multiplication proves

    E=product_(sigma=a)^b (1-W Q^(-sigma)),
    H=product_(c=c0)^(c0+n-1) product_(sigma=a)^b
          (1-beta0^(c^2) W V^c Q^(-sigma)).                     (5)

Thus substituting the exact row clocks into H and taking the ordinary fiber norm over A gives the **full detector product**, not a trace prefix. The operator input has constant support, and (4) has an O(log r)-gate formal noncommutative powering description. No seed polynomial is separately acquired for every a: Q remains a coefficient variable, which is essential for the new multi-a source.

However, a short formal word is only a descriptor. Evaluating S,T requires evaluating a coefficient function at shifted fibers; the supplied quotient row algebra stores only its values at the original fiber. The operation “specialize (4) and norm” has not been assigned a soft-O(r) algorithm. Treating S,T as ordinary matrices in the existing A, or taking a reduced norm and cancelling their determinants, would assume the missing transport/evaluation step. No such computation is licensed here.

## 5. What the q/Weyl norm literature supplies, and what remains

The finite-order setting of [Caruso–Le Borgne, *A new faster algorithm for factoring skew polynomials over finite fields*](https://xavier.caruso.ovh/papers/publis/fastfactor.pdf) starts with a supplied finite-field automorphism of known finite order and constructs reduced norms over its invariant center. Its degree/order costs and its coefficient field are part of the input. This does not supply the moving-fiber specialization in (4): our original row fiber is not an invariant coefficient field for Phi and Psi, and their abstract monomial actions do not make a paid small representation on it.

The concrete new algebraic subproblem is therefore:

> Given the actual rank-soft-r source fiber of (W,V,Q), retaining its fixed-a AP/GP and canonical-cubic-carry structure, the two constant-support monomial shifts above, and n,ell=O(r) in binary, evaluate the fiberwise zero support of the coefficient-ring word H in (4), using soft-O(1) row-algebra operations with checked short-binomial guards, or return an equivalent scalar norm/nonunit locator with the same bit bound.

This asks for a quotient-only or support-preserving moving-fiber skew norm. It does not ask for r^2 moments, does not assume a degree-two relation for the canonical cubic V clock, and does not expand all a-dependent seed polynomials. A solution satisfying section 3 would directly complete the source detector and its recovery ledger.

I did not obtain that evaluator. Standard scalar resultants or arithmetic over A still require acquiring H modulo the row polynomial (or a comparably uncontracted state); ordinary power projection only returns additive data. The exact noncommutative descriptor and the guarded compiler are not being counted as an improvement of the acquisition bound or as a factorization theorem.
