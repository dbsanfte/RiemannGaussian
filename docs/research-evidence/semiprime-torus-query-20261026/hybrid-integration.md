# What can now be folded into the hybrid

26 October 2026. This is a paper proof and algorithm interface, not a Lean theorem or a completed fast factoring implementation. The target remains deterministic all-semiprime soft O(N^(1/6)) bit complexity. Write K~N^(1/6), H=K², J=Theta(K), h=O(K^(3/2)). The current route still pays soft O(K^(5/4)) for acquisition.

## 1. Keep two compatible branches, with their own promises

The frozen pure weighted construction supplies one original Gauss row per unit colour j, in each public factor-size bin. Its coefficients a,b,ell and the centered physical window are retained. The preceding packet supplies a complete torus-annihilator consumer and complete projected norm-one point preparation. These are the ingredients being combined, not newly assumed oracles.

**Branch A: original coupled roots and a squared colour.** Keep pi=beta W, barpi=beta/W and the actual short-unit screen. This branch retains the stronger good-field order and therefore the exact common squared tag and singleton block partition. The new value-only gate below replaces exact Lambert amplitudes by another sufficient readout.

**Branch B: torus-only roots and an arbitrary nonliteral collision.** Reacquire q0=W^H, actually screen its short differences, and use the same weighted row coefficients with roots W^(ell-a-bN). Its witness exponent is -(R+1)(a+bS), nonzero. Here arbitrary modular aliases are useful because the torus decoder consumes them. Discard literal-zero rows using the short-gap proof. This branch does not inherit the original tag or singleton promise. It can discard multiplicities, union integer supports and fold signs because it needs only a localized nonzero annihilator.

Both branches have paid setup and recovery. Run cheap guarded branches first and the inherited shared product engine as fallback. There is no claim that one branch's weaker order retains the other's tags.

## 2. A value-only gated readout for the original singleton blocks

Let C_b be one original symmetric block, and let

    A_j=G_h(T_j), G_h(z)=product_(0<=i<h)(1-z*rho^i),
    w_j=the canonical integer [j²]_n, n=3^ceil(e/2).

Use two formal perturbations applied to the ROW VALUES, not to individual clock leaves:

    D_b(delta,epsilon)=product_(j in C_b)(A_j+delta+epsilon*w_j).
    d0=D_b(0,0), d1=[delta]D_b, dw=[epsilon]D_b.

At the good nonsplit field, an empty block has d0!=0. A block containing its unique hit j* has

    d0=0, d1=product_(j!=j*)A_j !=0, dw=d1*[R²]_n.

The explicit d0 gate prevents an empty block's derivative ratio from being mistaken for a tag. Classify Norm(d0): a proper gcd factors, a unit skips the block, and a saturated norm requires the usual coordinate gcds before declaring d0 globally zero. On the global-zero branch, a proper gcd of Norm(d1) factors and a unit norm licenses dw/d1. A saturated derivative may be declined. In a correct bin the unique-hit block has d1 nonzero at the nonsplit prime, so it cannot be lost to that last decline. Every accepted correct-bin block has the same squared tag. Use the existing scalar-coordinate scan, two square roots modulo n and restricted HH consumer, with at most one candidate menu per bin. Wrong-bin failure advances to the next bin.

This is valid even if the split components have several hits or different vanishing rows. Such degeneracy either exposes a proper factor or affects only an unpromised branch. No arbitrary element with zero norm is identified with a global zero.

Once A_j are acquired, the full readout is just multiplication of triples:

    (a,b,c)*(d,e,f)=(ad, ae+bd, af+cd),
    product_j(A_j,1,w_j)=(d0,d1,dw).

This is arithmetic in B[delta,epsilon]/(delta²,delta*epsilon,epsilon²), of constant rank. The total extra work is soft O(K), division-free even at zero divisors. Unlike the exact Lambert implementation, it needs neither G_h' nor the q-binomial weights nor their kappa normalization. This removes auxiliary acquisition; it does not shorten the long value computation. It is not numerically equal to the Lambert pair and is not claimed to be.

## 3. A short labelled resultant, with the long input charged

Public integer labels give a repeated-root-safe elimination interface. Put

    F_b(X)=product_(j in C_b)(X-j),
    Y_b(j)=T_j, W_b(j)=w_j.

Every nonzero difference j-j' has absolute value below K<P,Q and is a unit. Consequently all F_b,Y_b,W_b can be acquired by fast product trees and interpolation in total soft O(K), regardless of collisions among T_j. This PUBLIC METADATA ALGEBRA is credited to the [23 October guarded detector](../semiprime-detector-acquisition-20261023/reports/norm-detector.md), section 3; it is not a new generic construction.

The exact row-value identity is

    D_b(delta,epsilon)
      =Res_X(F_b, G_h(Y_b) mod F_b + delta + epsilon*W_b).

The monic convention leaves no missing sign or leading coefficient. A matrix version uses the multiplication operator M of G_h(Y_b) in B[X]/F_b:

    d0=det M, d1=Tr(adj M),
    dw=Tr(adj M * multiplication_by(W_b)).

At the promised singleton, the good-component adjugate has rank one and its marked/unmarked ratio is the tag. The missing quantity is still G_h(Y_b) mod F_b, whose values are exactly the long row products. An explicit dense matrix costs too much; neither a resultant symbol nor its short modulus computes that input. The inherited joint value engine supplies it at soft O(K^(5/4)); separate block engines are worse. The positive change is the gated constant-depth output interface, not a new resultant algorithm.

## 4. A support-only compiler for the torus branch

The torus branch permits a different target. For retained labels

    E_(j,i)=ell_j-a_j-b_j*N-H*i !=0,

any actual local W^E=1 can terminate through a proper norm gcd or the paid global torus-annihilator transfer. Thus:

* Exact duplicate labels and E versus -E need be tested only once.
* Extra tested nonzero short integer exponents are harmless: any extra hit also decodes. A supercover must still contain a native witness or have a separate coverage proof.
* A rational cancellation algorithm may test a small number of explicit binomial guards 1-W^E per acquired row. If such a guard is nonunit it yields a factor through its label; otherwise it can be inverted. O(polylog N) such guard types across O(K) rows cost soft O(K).

This last point reuses the old guarded-evaluator compiler with the newly complete torus decoder. It does not permit inverting an arbitrary additive zero or a whole unacquired product. A guard whose literal integer exponent is zero must be dealt with before specialization. A short formal noncommutative word still needs a paid evaluation algorithm on the actual row algebra.

For the executed literal-support contraction, write each start r_j=s_j+H*c_j, group by s_j and union [c_j-M0,c_j+M0]. Inversion folding further identifies s and H-s with the reflected interval; self phases are handled explicitly in torus-query.md. Let S be the exact cardinality after these operations. It is computed from O(K) endpoints, without enumerating S exponents. The variable-window engine costs soft O(K+sqrt S), including localization. Metadata for every bin is acquired first; qualifying cheap bins are tried before any expensive fallback. If a correct bin has S=soft O(K²), this is a complete soft-O(K) branch. A universal bound of that kind has not been proved, and the structural experiment does not suggest it for literal unions alone.

## 5. What the other domains contribute

The graph construction identifies the desired pole with a vertex-diagonal trace and gives a rank-one tensor core. The supercharacter construction compresses the full product to a short determinant and identifies its entries as a shifted recurrence band. Their input dependencies are explicit: the graph diagonal still contains the singular Cauchy sum, while the supercharacter band still needs G_h modulo its short denominator. Neither can yet be bolted in as a paid fast acquisition primitive.

A shared short Padé approximation acquires the regular polynomial part cheaply. Its exact error retains the entire normalized residue whenever the approximant is regular at the hit. This locates the missing signal; it is not a lower bound for every possible selected-residue algorithm.

The useful next task is consequently narrower than full product evaluation: acquire either the guarded singleton readout of Branch A, or a zero-support contraction of the common scalar Lucas streams in Branch B, jointly in soft O(K). Both now have a complete downstream consumer. Their current acquisition cost remains soft O(K^(5/4)); the all-input sixth-root proof is open.
