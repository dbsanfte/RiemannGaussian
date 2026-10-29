# Executed three-state twist-skein recovery and its block correction

26 October 2026. Scratch symbolic derivation; no finite sample campaign, backend expansion or repository edits. **Positive finite identity:** each original adjacent Alexander pair is exactly recovered from three fixed twist-skein scalar states with coefficients requiring only certified unit division. **Whole-query result:** the recovered state does not close in three channels under block composition; the explicit next correction is retained below. No improved complete native collision query is proved.

Read the current `twist-lift.md`, `block-contraction.md`, their reviews, and the rank-four normalization/scalar audits. Their acquired twist list, scalar family and initialized q-factorial blocks are prior results. The shifted Q_(2b) descriptor is not used as new progress.

## 1. Preserve the actual chosen native knot and ordinary variables

Use the explicit connected sum of negative twist knots T_(-s_j), 1≤j≤L, from the paid lift. Here s_j is a supplied positive O(log N)-bit integer with s_j=−c_j modulo N; c_j=−v_j/(v_j−1)² and v_j,v_j−1 are units. Each s_j is therefore a unit modulo N. Its ordinary Alexander factor is

    Delta_(T_-s)(T)=1−s(T+T^(-1)−2).

For disjoint adjacent pairs, index h=0,...,n−1 and set

    a_h=eta³*q^(2h), b_h=eta^(−5)*q^(−2h),
    u=a_h*b_h=q^(-1), B_h=(a_h−1)(b_h−1).

Thus Delta(a_h)Delta(b_h) is exactly the original pair at eta^(4h+3),eta^(4h+5), using ordinary reciprocity for the second argument. An odd final factor is evaluated separately. Every a_h,b_h and u is a native unit. Their nonzero short exponent differences from 1 are units within the original clock/order guard, so each B_h is a unit. No argument is an auxiliary root of unity.

The exact target for one twist factor is the already derived quadratic

    P_s(B)=1−s*delta+s*alpha*B+s²*beta*B²,
    delta=(u−1)²/u, alpha=1+u^(-1), beta=u^(-1).       (1)

The whole desired prefix is the product of P_(s_j)(B_h), over both indices, with the final unpaired factor if present. These are original Alexander factors, not substituted coupled LG values.

Primary source for the fixed twist states: Kohli, *The Links–Gould invariant as a classical generalization of the Alexander polynomial?*, Proposition 2.18 (negative twists), https://arxiv.org/pdf/2505.08296 , originally Experimental Mathematics 27 (2018),251–264. The source's mirror/Ishii convention is the one explicitly fixed in `twist-lift.md`; this report uses its algebraic negative-twist formula consistently, rather than importing the earlier raw R³ trefoil convention.

## 2. Actual constant-number skein-state recovery

Let F_s(B)=LG(T_-s;a,b) in that convention. The paid formula is

    F_s(B)=1+alpha*A_s(u)*B+beta*H_s(u)*B²,
    A_s=Σ_(r=0)^(s−1)u^r,
    H_s=A_s+2Σ_(r=1)^(s−1)Σ_(j=0)^(r−1)u^j.

Take only the three **fixed** states F_0=1,F_1,F_2. Since A_1=H_1=1 and A_2=1+u,H_2=u+3,

    D_1:=F_1−1=alpha*B+beta*B²,
    D_2:=F_2−1=alpha*(u+1)*B+beta*(u+3)*B².

These form an acquired basis together with 1: their two-by-two coefficient determinant is 2(u+1)/u², a certified unit because u has odd local order. Explicit inversion gives

    B=[(u+3)D_1−D_2]/(2alpha),
    B²=[D_2−(u+1)D_1]/(2beta).

More usefully, after substituting the target coefficients all alpha/beta denominators cancel. Define

    w_1(s)=[s(u+3)−s²(u+1)]/2,
    w_2(s)=(s²−s)/2.

Then the exact new recovery identity is

    P_s(B)=1−s*delta+w_1(s)D_1(B)+w_2(s)D_2(B).       (2)

The coefficient of B on the right is alpha*s because w_1+(u+1)w_2=s. Its coefficient of B² is beta*s² because w_1+(u+3)w_2=s². This proves (2) as a finite polynomial identity, not a knot-limit argument or interpolation at sampled inputs. It is valid at every collision, including zero divisors. Its implementation divides only by 2 and u, both certified units; it need not divide by alpha or any target value.

All w_1(s_j),w_2(s_j) and constant terms cost O(L) ring operations. The three states are fixed binary-encoded twist knots, so no large twist diagram or unknown topology is acquired. For a single supplied pair h, (2) can be evaluated across all j in O(L), giving the original pair product exactly with original labels. This is a genuine constant-state **local** recovery, not yet a complete prefix algorithm.

## 3. Execute block composition, retaining the first new channel

The three-state recovery does not commute with taking connected sums as a scalar linear map. Multiplying (2) for different j generates mixed products D_1 D_2 with different root-dependent weights. One must not replace that product by a constant-number linear combination of the corresponding whole-knot F_1/F_2 evaluations. Collecting all those mixed terms into R[B] is possible in softly O(L) by a product tree, but simply yields the already known degree-2L original pair polynomial. No scalar query is acquired by that coefficient collection alone.

There is a sharper, explicit check on **clock-block** composition. Keep the twist label s symbolic and write

    P_s(B_h)=1+s*l_h+s²*r_h,
    l_h=−delta+alpha*B_h, r_h=beta*B_h².

For two disjoint neighboring pair positions the exact transfer is

    P_s(B_h)P_s(B_(h+1))
      =1+s(l_h+l_(h+1))
         +s²(r_h+r_(h+1)+l_h*l_(h+1))
         +s³(l_h*r_(h+1)+r_h*l_(h+1))
         +s⁴*r_h*r_(h+1).                            (3)

The last coefficient is B_h²*B_(h+1)²/u², a certified native **unit**. Thus the two additional s³,s⁴ channels cannot both be identically discarded. This is an executed native composition, not a generic degree-count assertion: it identifies the exact quartic term and certifies it does not vanish on the continuing branch. It does not prove that an arbitrary different zero-only representation cannot compress it.

A lawful finite state algebra is available. Acquire the monic polynomial C(S)=∏_j(S−s_j) in softly O(L), and work in A=R[S]/C(S). The initialized block state starts at 1 and is multiplied by 1+S*l_h+S²*r_h. Its norm to R is exactly the original product over the s_j, with multiplicities, because this is a polynomial resultant identity. No CRT separation of s_j and no inverse of their possibly nonunit differences is used. Equation (3) describes its first two steps. This algebra becomes rank L rather than remaining the fixed three-state coefficient space; the scalar norm/readout still has to be computed.

This gives an exact composable law with all channels and all starts paid, but not a shorter acquired scalar. Direct advancement costs softly O(L*n), while the already paid geometric-product continuation costs softly O(L+sqrt(Lm)). Reconstructing degree-2b block coefficients in S and evaluating them at the s_j costs softly O(L+b) for one block, consistent with the prior block interface; repeating those readouts does not meet softly O(L+sqrt m). No shifted Q_(2b) descriptor or implicit tensor expansion is counted here.

## 4. Finite deformation/jet alternative, also executed at its startup

At u=1 the source twist formula becomes

    F_s(B;1)=1+2sB+s²B²=(1+sB)².

For the entire connected sum,

    F_C(B;1)=H(B)², H(B)=∏_j(1+s_j B), H(0)=1.

Since 2 is a unit, the unique constant-one formal square root recovers H through degree L in softly O(L) by Newton series arithmetic. Ordinary K(T)=H(−(T+T^(-1)−2)). This is a legal shared classical specialization, but H is already acquired from the native root list; it does not initialize the long orbit product for free. Polarizing H to its two distinct arguments recovers the target pair, not an already evaluated prefix.

For a finite jet u=1+epsilon, the exact coefficient formulas are

    [epsilon^r] A_s(1+epsilon)=binom(s,r+1),
    [epsilon^r] H_s(1+epsilon)
       =2 binom(s,r+2)+binom(s,r+1).                   (4)

They follow directly from (u−1)H_s=(u+1)A_s−2s. For example the first coefficients are A_s=s+binom(s,2)epsilon+..., H_s=s²+s(s−1)(2s−1)epsilon/6+.... Denominators in binomial acquisition can be avoided by integer binomial arithmetic; for a jet of order O(L) the needed small factorials are also native units asymptotically.

A fixed-order jet is therefore acquired and composable in a constant-rank nilpotent algebra per scalar input. However evaluating epsilon=u−1=q^(-1)−1 is not a homomorphism out of a truncated jet ring: epsilon is nilpotent there, whereas the native u−1 is a unit. The jet theorem licenses the classical specialization and derivatives, not its readout at the nonnilpotent native deformation. Replacing that readout by the explicit local recovery (2) restores the clock-block correction (3). No singular factor is divided and no convergence/analytic assumption is used to hide this boundary.

Primary skein-scope check: Garoufalidis et al., *Skein theory for the Links–Gould polynomial*, arXiv:2505.19251v4 / JLMS (2026), https://arxiv.org/html/2505.19251v4 , Remark 1.16, explicitly warns that its reduction relation degenerates at the Alexander specializations. Its effective skein uniqueness theorem is not an initialized nearlinear arithmetic algorithm at those parameters. This source supports the caution about moving specialization through a skein reduction; the concrete identities (2)–(4) are directly derived above.

## 5. Outcome and narrow next bottleneck

The successful finite recovery (2) removes the mixed LG correction **locally** using three fixed twist-skein states, with no unlicensed pivots and no claim that a deformed invariant itself has the original zero predicate. Its clock composition (3) then exposes the exact higher channel that must be retained. The natural quotient-state/norm law is initialized and valid over the composite ring, but its scalar contraction remains the old native orbit query.

A useful next theorem would evaluate the norm of that rank-L state under the special coefficients l_h,r_h in (3) without advancing through all h or reacquiring a growing polynomial for each block. It must retain the unit-leading quartic correction and its successors, or supply a different zero-equivalent invariant using actual native arithmetic. The constant-number skein recovery and finite jet examined here do not give that theorem. The complete guaranteed cost remains softly O(L+sqrt(Lm)); no factoring record or soft-k prefix algorithm is established.
