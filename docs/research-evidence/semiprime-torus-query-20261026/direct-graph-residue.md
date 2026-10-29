# Direct selected graph residues and a finite rank-one reset

26 October 2026. Focused paper-only continuation of exotic-forms.md and the gated row-value interface. No repository edits, code, tests or numerical campaign. The graph residue defined here is explicit; it is not asserted equal to another proposed quantity C whose definition is still pending.

**Outcome.** Two scalar adjugate contractions of the Bass reversal pencil give the tag at a unique good pole, without forming an adjugate or correction matrix as OUTPUT. A better finite q-binomial reset turns this into two fixed-parameter rank-one determinant values, exactly equal to the value-only gated pair up to a paid unit. This removes G' from that representation, but does not acquire its selected determinant values below the old K^(5/4) bill. Constant update rank is not constant matrix dimension.

## 1. Direct Bass scalar pencil

Work inside ONE ORIGINAL symmetric singleton block. Its d_b=J_b*h physical leaf masses are a_ji=1-T_j*rho^i. The actual signed-clock normalization and canonical weights w_j=[j²]_n are retained. At the correct field either no mass vanishes or exactly one does. The latter is the promised good block; repeated roots elsewhere do not change that promise.

Use the arc incidence K,L and reversal matrix from exotic-forms.md. Deform reverse weights to rho^i/(1+delta), put R(delta)=I+Jrev(delta), and let U be diagonal on vertex space: U_jj=w_j on row vertices, U_ii=0 on clock vertices. Define the scalar pencil

    D_U(s,delta)=det(R(delta)-s*K*U*L(delta)).

Finite determinant reduction gives

    D_U(s,delta)=(1+delta)^(-d_b)
       product_j [G_delta(T_j)+s*w_j*(-T_j*d_T G_delta(T_j))],
    G_delta(T)=product_(i<h)(1+delta-T*rho^i).           (1)

Proof: L R^{-1}K has left-left diagonal -sum_i w_ji/(1+delta-w_ji), and the source is supported on left vertices. The determinant factor is therefore a product of those diagonal row factors. Multiplying clears the apparent collision denominators, so (1) is a formal identity even at the hit.

At its sole good leaf, let A be the product of all other leaf masses. Then

    D_U(0,0)=0, d_delta D_U(0,0)=A,
    d_s D_U(0,0)=A*w_hit.                            (2)

The extra (1+delta)^(-d_b) contributes nothing to the first delta derivative when the constant determinant is zero. Equivalently these are the scalar contractions Tr(adj(R(0))*R'(0)) and -Tr(adj(R(0))*KUL(0)). The ratio is correct without asking for the full adjugate as an output.

This is a viable selected-scalar interface. It does not supply those contractions algorithmically: explicit (1) still requires G_delta and its T derivative. The empty-block constant gate is mandatory, exactly as for the current row-value perturbation. A nonzero derivative alone does not identify a hit.

If instead U=I on ALL vertices, the unweighted source derivative doubles A at a sole hit. Its full tensor description is the previously derived pair of rank-one-perturbed diagonal factors. That tensor core does not give a new source normalization: its first coupling coefficient is the same finite pole trace. Taking the Bass determinant at nonzero coupling can cancel the pole with its correction; no cheap value at that coupling has been proved to retain the selected coefficient.

## 2. Better source: finite barycentric reset eliminates the clock cofactor

Let n0=h-1, f=(rho;rho)_(h-1), and

    c_i=(-1)^i*rho^{i(i+1)/2}*[h-1 choose i]_rho.

The exact finite Lambert identity, after multiplication by its denominator, is

    sum_i c_i*product_(k!=i)(1-T*rho^k)=f.             (3)

This is an identity of finite polynomials in T. All coefficients c_i and f are units under the actual short q screen. The single scalar f can be acquired in soft sqrt h; an h-entry c_i array is NOT declared acquired in soft K merely by writing this formula.

Let D=diag(a_ji) on the leaf-mode space, let 1 be its all-ones column, and define reset rows

    v_(j,i)=c_i/f, v^w_(j,i)=w_j*c_i/f.

For all s, the rank-one determinant identity, valid polynomially even when D is singular, gives

    det(D+s*1*v^t)=P+s*d1,
    det(D+s*1*(v^w)^t)=P+s*dw,                       (4)

where

    A_j=G_h(T_j), P=product_j A_j,
    d1=sum_j product_(l!=j)A_l,
    dw=sum_j w_j*product_(l!=j)A_l.

Indeed the adjugate of a diagonal matrix is diagonal, and (3) sums its entries along the clock of each row. NO clock derivative or unknown hit index appears. The degree in s is exactly at most ONE because this is a SINGLE GLOBAL rank-one update on the block, not a separate reset multiplied per leaf.

After the P zero gate, the two FIXED scalar determinant values at s=1 are exactly (d1,dw). A good hit gives (Arow,Arow*w_hit), Arow=product of OTHER ROW values, which is nonzero at that field. Thus (4) is a genuine finite direct-scalar rewrite of the newest gated pair. It preserves the canonical public weight and the same singleton-block validator, including empty blocks. It does not claim equality to the exact Lambert amplitude c_I, and does not need such equality.

The reset/determinant-lemma mechanism has prior credit: the frozen [coefficient-forms combinatorial expressions](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-coefficient-forms-20261026/combinatorial-expressions.md) already executes diagonal rank-one updates/one-defect partition functions, and the older three-state reset encodings retain their credit. The additional concrete source choice here is (3), proving that the physical-clock cofactor sums to the paid scalar f and hence yields exactly the current ROW-value gate. No novel generic rank-one determinant theorem is claimed.

## 3. Actual initialization and executed cost

The masses are the actual acquired T_j and rho powers; the reset is separable in row and clock indices. Its concise description is legitimate, but explicitly emitting it takes h clock coefficients, and the diagonal/arc space still has J_b*h entries. Neither separability nor update rank one turns that into a constant-rank algebra computation.

There is a complete symbolic execution without materializing those matrices: acquire ALL A_j=G_h(T_j) jointly by the division-free geometric engine, in soft(K+sqrt(Kh)). Multiply (A_j,1,w_j) triples over each block in B[delta,epsilon]/(delta²,delta*epsilon,epsilon²). This costs soft K and gives P,d1,dw; (4) then supplies the two selected determinants exactly. It needs neither G_h' nor a c_i array nor numerical inverses of collision factors. The f-normalized reset is used to PROVE (4), while this implementation avoids generating it. Total remains soft K^(5/4).

The current paid q-binomial action can apply the clock source to a supplied coefficient vector, but does not evaluate all the singular row reciprocals needed by a Sherman–Morrison contraction. That contraction would ask for v^t D^{-1}1, whose terms are exactly the finite Lambert sums and whose inverse is undefined at the desired zero. Its componentwise Laurent meaning is correct; its extraction remains an additional operation. Applying the matrix determinant lemma on that singular locus is lawful only in its polynomial/adjugate version (4), not by inverting D.

## 4. Zero and nonunit branches

First classify P using norm and coordinates: proper gcd factors; unit norm means skip; saturated norm requires coordinate tests before calling P globally zero. On that branch classify d1: proper norm gcd factors, unit norm permits dw/d1, saturated norm may be declined. At a correct-bin singleton its good value is nonzero, so it cannot be lost to the latter decline. Any accepted correct-bin block therefore gives the correct squared tag; select at most one per bin before the bounded scalar/two-root/HH validator. Wrong-bin failures remain bounded and do not suppress coverage.

An arbitrary additive zero of one selected determinant is not a short torus relation. The new two-coordinate annihilator consumer applies only after an actual labelled multiplicative leaf is acquired. No correction determinant or reset source is assigned that decoder merely by vanishing.

## Outcome

The direct Bass adjugate pencil (1)–(2) is exact but retains clock derivatives. The improved finite reset (3)–(4) gives two SINGLE-USE scalar determinant values with the desired ratio and no clock-cofactor normalization. Its initialized completion is precisely the value-only gated query, not a faster solution. A new method evaluating just those two structured rank-one determinant values, with their zero gate and no expanded leaf space, would constitute actual progress. This report establishes the finite equivalence and cost, not that missing method or a general barrier theorem.
