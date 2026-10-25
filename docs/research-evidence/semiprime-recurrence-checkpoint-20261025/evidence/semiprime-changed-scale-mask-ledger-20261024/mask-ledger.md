# Changed-scale tensor acquisition ledger

24 October 2026. Scratch only. Let ell=h=Theta(k^(3/2)), J=soft k, so the target budget is soft ell^(2/3), while the existing complete query costs soft ell^(5/6). No full native tensor query is acquired here.

Use the proved algorithms and actual primary layout recorded in `/tmp/semiprime-implicit-thin-encoding-20261024/all-mask-sharing.md` and `working.md`. In particular both vectors in P_ell(y)=u(y)^t C v(y) change with the native target y.

## What the changed scale really purchases

For D=4^m approximately ell^delta, H=ceil((ell+1)/D), put alpha=log_4(6)=1.29248125036. The existing joint transform acquires all 6^m inner left masks for ONE supplied outer combination in

    soft(sqrt ell+H+D+6^m)
       =soft ell^max(1/2,1-delta,alpha delta).

Thus the balanced delta=1/2 cost ell^(alpha/2)=ell^0.64624062518 DOES fit the new ell^(2/3) budget. This statement is valid and includes all its returned masks.

The best unbalanced width is instead

    delta*=1/(1+alpha)=0.43620858397,
    nu=alpha/(1+alpha)=0.56379141603.

Widths restricted to powers of four alter only constant factors. All H-dimensional outer vectors and D-dimensional intermediate vectors are acquired. For p explicitly supplied outer combinations, reusing coefficient preprocessing gives

    soft(sqrt ell+p ell^nu).

Consequently the target budget funds p<=soft ell^(2/3-nu)=soft ell^0.10287525064 combinations by this algorithm. To beat the existing ell^(5/6) query it suffices that p<ell^(5/6-nu)=ell^0.26954191730, with a fixed exponent margin. Neither bound has been established for the actual native leaf/outer union.

Generating the p outer vectors from digit masks costs soft(pH), already included. Their active-Q descriptions, grid assignments and target-dependent sums are NOT free: any cost to enumerate or construct those combinations must be added. A count of p unlabeled placeholders is insufficient.

## A paid partial-mask transform

For one acquired D-vector a=C^t u and a supplied set of t wanted inner mask strings, prune the radix-four-to-six transform by the trie of those strings. At depth s retain at most min(6^s,t) prefixes; each carries a remaining array of length 4^(m-s). The actual array work is bounded by

    sum_(s=0)^m min(6^s,t)4^(m-s)
       =O(D t^gamma), gamma=1-log_6(4)=0.22629438553,

for 1<=t<=6^m. The two geometric tails meet at s approximately log_6 t. Build the trie in soft(mt), included because D t^gamma>=t in this range. Each operation is an addition/sign change; no mask value or target is inverted. This supplies the actual requested mask outputs, including zeros, rather than assigning an oracle cost to a description.

For p outer combinations with at most t masks each, an executable bound is therefore

    soft(sqrt ell+p(H+D t^gamma)+description_cost).

Write p=ell^pi and t=ell^theta. Optimizing the width gives delta=(1-gamma theta)/2 and per-combination exponent (1+gamma theta)/2, when theta<=alpha/(1+alpha), exactly the condition t<=6^m at this optimizer. The target-budget sufficient condition is

    pi+gamma theta/2<=1/6,

and beating the old complete query requires pi+gamma theta/2<1/3. These are conditional executable union bounds, not established native union counts. When t=6^m they recover nu and the preceding all-inner-mask ledger.

The native direct choice p=J=ell^(2/3), even with one desired inner mask per outer vector, costs at least the displayed algorithm's ell^(7/6) term after optimizing width. All-inner transforms per native outer vector cost ell^(2/3+nu). These costs are worse than the old complete query. This is a cost of those explicit reductions, not a lower bound on shared implicit native evaluation.

## Why the literal full primary encoding still fails

Use different letters for the primary tensor depth: s=19m, D=4^m, A=binom(19m,m), K0=floor(sqrt A), N0=3^(18m). For the coefficient matrix R_rows=ceil((ell+1)/D), the unchanged full phase writes

    E=ceil(R_rows/(K0 N0))*10^(19m)
      >=(ell+1)*10^(19m)/(K0 N0 D).

The source's exact inequality 10^(19m)>K0 N0 D holds for every m>=1, so E>ell+1. That literal output acquisition does not fit ell^(2/3), and cannot beat ell^(5/6), regardless of the changed relationship between ell and k. Taking m bounded does not fix this: the number of coefficient bands then grows linearly with ell.

For scale orientation only, Stirling's formula gives log_2 A=5.65197272947m+O(log m), log_2(K0 N0 D)=33.35531137771m+O(log m), while log_2(10^(19m))=63.11663380286m. If one full coefficient band is approximately filled, the unmodified phase is about ell^1.89225137455 up to subpower factors. The exact E>ell inequality above is sufficient and does not rely on this approximation.

Even fixing one active Q and asking for ALL distinct left mask descriptions includes 6^m inner choices and 4^(18m) outer singleton/sum choices, rather than merely 6^m. The latter four are the three row selectors and the P0 sum; repeated Pij labels have already been merged. Their full tensor transform has 6^m4^(18m) output slots. This is another explicit family acquisition, not the wanted-leaf union. Zero padding and repeated scalar values may permit pruning; no generic distinct-values lower bound is asserted.

## Native output problem remains present

The primary wanted-entry reduction of the unfolded coefficient matrix returns partial values A[r,j], whose literal final contraction needs HJ outputs. Since H=ell^(1-delta), J=ell^(2/3), this count is ell^(5/3-delta). For any genuine sub-ell width D (delta<1), it exceeds the ell^(2/3) target; at the optimized delta* it also exceeds the old ell^(5/6) query. This counts the actual partial-output reduction only.

Folding first to ask for J diagonal entries makes the left input itself depend on y_j: X[j,d]=sum_r c_(Dr+d)y_j^(Dr). Its leaf masks require target-dependent outer combinations. The one-outer all-inner transform and the pruned variant above do not acquire that native collection or the corresponding right outer sums. A single-active-Q restriction cannot stand in for the full batching tensor: as the working report proves, it collapses to the four ordinary singleton products per inner digit.

Therefore the new scale DOES pay all inner masks for one outer combination, and the optimized/partial-mask ledgers quantify how many more it can pay. These initial ledgers concern arbitrary supplied coefficient-row outer vectors; the stronger factorized fixed-Q case below supersedes them in its stated scope. The supplied reductions still do not pay the full native paired-output union or establish any whole-query improvement below soft k^(5/4).

## Reviewed stronger fixed-Q primitive and its exact scope

Reviewed `/tmp/semiprime-thin-fixed-q-joint-20261024-36wtj7ic/joint.md`: its mixed-radix rebalancing argument is valid. Fix ONE actual Q block, shifted by n0 divisible by B0=D*N0, and ONE outer coefficient-row mask factorized across its ternary digits. For D<sqrt(ell+1), choose a mixed-radix digit cut D0=D*3^r between sqrt(ell+1) and 3sqrt(ell+1), when B0 reaches that threshold. Its digit-boundary construction guarantees D0 divides B0 and n0. Split the outer coefficient index as rho=t+(D0/D)s and its mask as u_low(t)u_high(s).

At the global balanced coefficient reshape, acquire a0=C_D0^t u_high, explicitly placing the shifted high vector at n0/D0 and zero elsewhere. The acquired matrix action costs soft sqrt ell, including the high-vector description, row-start data and partial last row. Fold

    a[d]=sum_(t<D0/D) u_low(t)*a0[D*t+d]

in O(D0) operations, then apply the joint inner digit transform. This returns all inner masks at cost

    soft(sqrt ell+6^m).

If B0<sqrt(ell+1), acquire the whole smaller block, perform its literal weighted fold and apply the same transform. Original coefficient padding handles every clipped position. All weights may be zero or nonunits; no weight or final mask value is inverted. The preprocessing inverses are exactly the existing q-prefix denominators through ell. A fixed single parameter x weighting coefficients by x^n also factors across this cut and is permitted, with its powers and phase acquired in the same bound. Different x parameters are not supplied for free.

The pruned-inner transform above combines with the same fold to give soft(sqrt ell+D*t^gamma) for t explicitly described inner masks of this one factorized outer mask. At the actual thin dimension D<=J^(1/18)=ell^(1/27), even all 6^m masks contribute at most ell^(alpha/27), approximately ell^0.04787; the sqrt ell term dominates. Thus p actual fixed-Q/factorized-coefficient-mask descriptions admit the literal bound soft(p*sqrt ell+description_cost), and up to soft ell^(1/6) such descriptions fit the target budget. This is stronger than the arbitrary-outer-vector ledger, and thin D does not force ell/D work in this special case.

Crucially, the diagonal-folded native input has

    X[i,d]=sum_rho c_(D*rho+d) y_i^(D*rho).

An outer tensor mask on TARGET indices i therefore produces

    sum_i omega_i X[i,d]
       =sum_rho c_(D*rho+d) mu_rho,
    mu_rho=sum_i omega_i (y_i^D)^rho.

The vector mu is a sum of target powers, not a digit-factorized coefficient-row mask. The reviewed mixed-radix primitive cannot be invoked on this mu by calling omega a factorized target mask: its factorization concerns a different index. Executing it separately for every participating target gives a valid potential J-call cost, not a free joint acquisition. For J=ell^(2/3), even J separate soft-sqrt-ell calls cost soft ell^(7/6). A new shared acquisition would be needed to improve that count.

The full active-Q union, actual Q-dependent assignments, target-dependent right outer sums, and the paired terminal outputs remain unacquired within the sufficient budget. The stronger fixed-Q primitive changes the local ledger; it supplies no whole-query gain.

Attribution correction: the genuine Cauchy diagonalizer discussed in the preceding scratch is a repackaging of `/tmp/semiprime-paired-contraction-20261024/paired-pencil.md` Sections4/5, not a fresh advance. No frozen/shared file or numerical campaign was changed.
