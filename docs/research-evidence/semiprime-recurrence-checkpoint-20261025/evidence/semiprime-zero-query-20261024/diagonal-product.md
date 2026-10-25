# Matched-label diagonal selection: an exact algebra and its paid completion

24 October 2026. Scratch only. This constructs a diagonal selector that REALLY retains the original matched labels, rather than another ordinary determinant of the paired matrix. A border over the acquired label algebra gives exactly the desired scalar product, including at zeros. Its literal completion costs soft K*sqrt(b), worse than the retained soft sqrt(Kb) query. A dual-number cycle filter and a constant-term perturbation are tested as alternatives; their low auxiliary precision does not acquire their required diagonal input. The remaining operation is identified as a specific implicit modular composition/middle product, not a generic algorithmic impossibility.

## 1. Actual source, target and earlier failure kept separate

Use `/tmp/semiprime-paired-contraction-20261024/paired-product.md`, final SHA256 `6417d39410c9bc9d58acba925933afde1c2db38c2dfe94e05c959cb9db0febea`, independently reviewed at SHA256 `607b23a6ffadb545150fd1001b62328282d06885a191a383b43530833be317c7`. Its full stacked determinant is uniformly unit on the prepared native square windows and loses the desired diagonal. That replacement is NOT used below.

The acquired coefficient action is from `/tmp/semiprime-implicit-thin-encoding-20261024/all-mask-sharing.md`, SHA256 `5f79d577ff7fddf72a6e3670d5bca3b7ff2ef72557f137553d388b9fea9c0f31`, review `131aa98fb6f09ce933d20dddb35045ab5ac3b555e233fabcb15f43413d6eaa02`. It supplies the ACTUAL q-Pochhammer matrix C, fast C/C^t actions and its generators in soft(H+D), with all q-prefix starts and unit inverses paid.

Work in the acquired constant-rank quadratic ring B over R=Z/N. Native q is a unit and every1-q^r for1<=r<=Ccap=16k² is certified unit. Put b=L=2k²+2, choose H,D~sqrt b with H=ceil((b+1)/D), and

    P_b(Y)=product_(i=0)^(b-1)(1-q^iY)=sum c_nY^n,
    C[rho,r]=c_(D*rho+r), with zero padding beyond b,
    G(X,Y)=sum_(rho,r)C[rho,r]X^rho Y^r.

There are K=Theta(k) ACTUAL unit arguments y_j=V_j^(-1), with original row metadata. Execute the already paid factor-or-target-separation procedure: either factor N or retain exactly deduplicated, unit-separated targets. The same property holds for y_j. No additional local field or target-logarithm oracle is supplied.

The desired B scalar is

    Delta=product_(j=1)^K P_b(y_j)
         =product_j [u(y_j)^t C v(y_j)],
    u(y)=(1,y^D,...,y^[D(H-1)]),
    v(y)=(1,y,...,y^(D-1)).                        (1)

Its final quadratic norm, with the known unit product_j V_j^b restored, is the original covered query. All ORIGINAL indices are0<=i<b. A nonunit ORIGINAL norm leaf has the existing nonsplit-field/G_beta factor-or-bounded-scalar-witness consumer. No auxiliary determinant or selector coefficient is assigned that consumer.

## 2. An acquired matched-label algebra, not a guessed projection

Acquire the ACTUAL native point polynomial

    F(T)=product_(j=1)^K(T-y_j), E=B[T]/F(T).

Its coefficient vector and product tree cost soft K. Unit target differences certify every F'(y_j) as a unit. Acquire those values by monic MPE and their inverses by explicit fixed-rank unit arithmetic. The CRT idempotents

    e_j(T)=[F(T)/(T-y_j)]/F'(y_j) modF

have a shared product/complement circuit with soft-K acquired constants. All K dense degree-K idempotent coefficient arrays are NOT acquired for free. Their evaluation identities e_j(y_h)=delta_jh prove E=product_j B, a finite etale rank-K B algebra. The original row label is precisely its jth component, on BOTH local sides.

One can express the actual diagonal-selector idempotent in E tensor E compactly. Let

    B_F(T,S)=[F(T)-F(S)]/(T-S),
    R_F(S)=(F'(S))^(-1) modF(S),
    Pi(T,S)=B_F(T,S)R_F(S) mod(F(T),F(S)).          (2)

B_F is a POLYNOMIAL divided difference, computed by a two-output Horner circuit in O(K) gates; T-S is never inverted. R_F is acquired by interpolation of the actual unit values1/F'(y_j), costing soft K. At native pairs Pi(y_i,y_j) is1 for i=j and0 otherwise, so

    Pi²=Pi, (T-S)Pi=0, Pi=sum_j e_j(T)e_j(S).

These are exact ring identities, including over the composite base; they follow from the acquired CRT, not from a proof-only hidden-field algorithm. The diagonal ideal Pi*(E tensor E) is isomorphic to E. Thus (2) is a real matched-label selector, rather than row/column weights that leave every permutation cycle unchanged.

The storage distinction is essential: the tensor algebra has rank K² if expanded. Its diagonal ideal has rank K. A compact circuit for Pi is not a constant-rank representation of multiplication by an arbitrary bivariate kernel on that ideal.

## 3. A determinant that computes the CORRECT scalar, executed to completion

Write theta=T modF. The kernel restricted by Pi is exactly

    Pi*G(T^D,S)  <->  G(theta^D,theta)=P_b(theta) in E.  (3)

Define actual E-valued vectors u(theta),v(theta) as in (1). A SINGLE border over E is

    M_E=[[I_H, C*v(theta)], [u(theta)^t,0]].         (4)

Its Schur complement is -u(theta)^t C v(theta), so

    det_E M_E=-P_b(theta),
    Norm_(E/B)(det_E M_E)=(-1)^K Delta.             (5)

This is the desired diagonal product up to a known sign. Unlike the earlier stacked B-valued border, cross-label cycles cannot occur: CRT splits (4) into the K one-border matrices, one at each original y_j. Equivalently orthogonal idempotents multiply to zero between different labels. Equation (5) remains true if a selected diagonal is zero or a zero divisor; it never uses its inverse. The final quadratic norm removes the sign because Norm_(B/R)(-1)=1.

Here is a COMPLETE acquisition algorithm for (4)--(5), with its actual cost.

1. Compute theta^D modulo monic F by binary powering and acquire the successive u(theta) powers. Acquire v(theta) by its actual powers as well. Literal coefficient-vector arithmetic costs soft(K(H+D)); sparse small powers may be cheaper, but no such extra promise is needed for this bound.
2. Apply the existing fast C action over the coefficient algebra E, then form the E dot product with u(theta). The precomputed q-grid coefficients and inverses lie in B and are reused; no new nonunit E inverse is requested. An actual E operation costs soft K B work. Thus the action and dot product cost soft(K(H+D)), not soft(H+D).
3. The resulting degree<K polynomial h(theta)=P_b(theta) is actually acquired. Evaluate its representative at all known y_j by monic MPE and multiply, cost soft K. This is an executable E norm using supplied roots, not a generic factoring or resultant oracle. Take the final quadratic norm and restore the explicit unit V phases, at soft K extra cost.

For H,D~sqrt b and K~k, b~k², this correctly computes the whole scalar in soft K*sqrt b=soft k². Every point-algebra coordinate and every output used by the norm is paid. Proper gcds factor. Saturated products are localized with actual row and seed labels before invoking the original norm-leaf consumer. No operation on the selector itself is a factor witness.

Thus exact label selection is possible with a LINEAR-rank label algebra, not only with an exponential exterior construction. The rank-K cost is part of this initialized completion; it has not supplied a soft-k norm algorithm. It is an upper-cost ledger for this implementation, not a claim that scalar-only evaluation must expand h.

## 4. Test a genuinely small auxiliary perturbation

A constant-precision selector looks more promising at first. Let A be the conceptual K-by-K paired matrix A_ij=G(y_i^D,y_j), with its fast actions available. Over dual numbers B[epsilon]/epsilon² define

    A_epsilon[ii]=A_ii,
    A_epsilon[ij]=epsilon*A_ij for i!=j.           (6)

The determinant expansion gives EXACTLY

    det A_epsilon=product_i A_ii.                 (7)

Every nonidentity permutation moves at least two labels, so its term contains epsilon² and vanishes. This works even when an A_ii is nonunit; it does not divide by a diagonal or require a simple root. For K=2 the removed term is exactly epsilon² A_12 A_21. Auxiliary coefficient rank two and precision epsilon² really suffice algebraically.

The missing acquisition is precise. Equation (6) has action

    A_epsilon*x=epsilon*A*x+(1-epsilon)*diag(A)*x.

The first term uses the acquired fast A action, while the second requires the desired diagonal map. The mask has entries1 on the diagonal and epsilon off it; reducing that mask modulo epsilon gives I_K. It is not a rank-two row/column mask: any low-rank mask factorization would reduce to a factorization of I_K. This is a statement about this explicit mask, not a lower bound on all diagonal algorithms.

No procedure here constructs (6) from the Cauchy generators at soft(H+D+K). One can construct it after acquiring the K native diagonal values by the old query, or implement its matched labels in the rank-K algebra of Section2. Those are actual completions, but they do not make (7) a free scalar extraction. The low nilpotent precision alone has not provided the matrix's constant coefficient.

A related one-variable constant-term selector has entries z^[(i-j)²]A_ij. Its determinant's constant coefficient is again the desired product: the total exponent is nonnegative and zero only for the identity permutation. Precision one would suffice for that coefficient. But the matrix's constant coefficient is itself diag(A), the same unacquired map. Conversely a separable weight z^(a_i-b_j) assigns every permutation the SAME exponent sum_i a_i-sum_j b_j and cannot select the identity. These exact calculations exclude two tempting unpaid initialization shortcuts; they are not claims about all possible perturbations.

An exterior determinant without label projectors antisymmetrizes over every permutation, the already failed ordinary scalar. A commuting square-zero-variable product instead gives a permanent, still containing all matched and unmatched cycles, with a literal2^K subset coefficient algebra. Neither is used as an initialized soft-k selector in this report.

## 5. The exact modular-composition and middle-product instance

The fixed-algebra computation (3) identifies a sharper constructive target than “compute the diagonal somehow.” The ACTUAL native instance is

    h(T)=G(T^D modF(T),T) modF(T), degree h<K,      (8)

where F is the acquired monic native point polynomial of degree K. G has bidegrees H-1,D-1, but its H*D~b coefficient table is NOT supplied as dense input; it is given by the acquired q-binomial generators and nearlinear C/C^t actions. The inner polynomial T^D modF and every constant of F are actual data. This is implicit bivariate modular evaluation, or equivalently the remainder P_b(T) modF.

A conventional modular-composition or polynomial-multiplication theorem receiving all coefficients of G has already paid order b input, and an ordinary univariate outer polynomial would first need the same long reduction. Such a theorem cannot be called with H+D input cost merely because C has a fast action. The additional promise required is an algorithm for (8), or only its E norm/zero support, that USES this structured coefficient action directly and preserves the original target labels. No such algorithm is assumed here.

For a concrete transposed/middle-product view, let ell_s extract coefficient T^s of a remainder modulo F. Then

    h_s=sum_(rho,r) C[rho,r]*H_s[rho,r],
    H_s[rho,r]=ell_s(T^(D*rho+r) modF).            (9)

Each H_s is the reshaping of an ACTUAL order-K linear-recurrence sequence from the multiplication-by-theta algebra. Its native-root representation is

    H_s=sum_j e_(j,s)*u(y_j)*v(y_j)^t,

where e_(j,s)=[T^s]e_j(T). One such weight vector is acquired in soft K by transposed interpolation; it is not a proof-only field value. Fast C/C^t actions contract a supplied separable term, but no acquired operation in this report simultaneously contracts the K paired terms of (9) at soft(H+D+K). There is no minimal-rank or minimal-order lower-bound assertion in that observation.

One could equally formulate (9) as consecutive middle coefficients of P_b times the rational recurrence series determined by F. That is the previously exposed long-remainder boundary, now with the exact native structured action specified. A new fast middle-product/composition algorithm for THIS implicit input would be a genuine solution; the label selector and dual-number identities do not implement it themselves.

## 6. Retain the cheaper complete query and its original witness

The known completion still improves on Section3. Choose a real baby length a, acquire P_a(Y)=product_(i<a)(1-q^iY), and write b=ra+d. Acquire every labelled point y_j*q^(ag),0<=g<r, then monic MPE of this ONE degree-a polynomial. Compute the actual clipped tail at q^(ar)y_j and multiply only within its original j. This gives every P_b(y_j), or their product, in

    soft(K+a+Kb/a)=soft(K+sqrt(Kb))

at the optimized a~sqrt(Kb), clipped to[1,b]. All short coefficients, mixed starts, outputs and tail indices are paid. For K~k,b~k² it is the retained soft k^1.5 bound.

A nonunit actual block norm is localized with j,g retained. Descent in its acquired baby factor tree fixes an ORIGINAL index ag+i in[0,b). Proper gcds factor; saturation is an ORIGINAL NORM leaf, not whole split equality, and invokes the nonsplit/G_beta consumer to factor or recover the original bounded scalar beta witness. Different hit labels at the two primes are separated during descent. Neither selector coefficients nor auxiliary cycle terms get that decoder. The same implementation rebuilds actual row subsets and retains seed offsets on every restriction.

## Costs and scoped outcome

| Executed object | Paid work, usual log/bit factors suppressed | Exact support/value scope |
|---|---:|---|
| Native F, derivative inverses, CRT/diagonal-selector circuit | soft K | actual matched labels, no hidden roots |
| Label algebra E and constant-rank base arithmetic | rank K over B | rank must be paid if operations are expanded |
| Correct E-valued border and final E norm | soft K(H+D) | actual desired diagonal product, zero safe |
| Dual-number identity selector | rank-two coefficients, algebraic precision2 | matrix constant-diagonal acquisition NOT supplied |
| Constant-term squared-label selector | algebraic precision1 for constant coefficient | same missing diagonal map |
| Implicit modular evaluation (8) at desired soft clock | NOT acquired | exact new scalar/remainder contraction needed |
| Original baby/giant query with all labels/recovery | soft(K+sqrt(Kb)) | best retained completed query |

This attempt selects the identity permutation correctly rather than repeating the uniformly-unit full determinant. Its actual initialized finite-etale completion is overbudget, and the two small-precision identities have an explicit missing input map. A different structured scalar-only norm or simultaneous modular-composition algorithm could still improve the clock. No whole-query exponent gain, generic determinant/recurrence impossibility, or unproved transfer of a coefficient circuit into a terminal evaluator is claimed.
