# Working followup: a large-period joint seed recurrence

24 October 2026. Scratch, explicitly NOT a completed faster query. This is outside the frozen ideal packet. It executes norm/angular interpolation for one actual seed block and prices the whole-family continuation. Large supplied torus order proves a useful exact leading coefficient and a local bounded-hit relation; neither acquires the missing long contraction.

## Acquired input and the extra order information

Read `/tmp/semiprime-quadratic-ideal-20261024/torus-order-supplier.md`, SHA256 `1f3033cc85c1b6798a188daa7b7c32d702b87d2cb3401e3e1f1afe6cb3a4e9bc`, and its predecessor aligned quadratic constructor. The supplier either factors or acquires a norm-one W whose BOTH local orders, including those of v=W^H, are odd and exceed C=16H, H=k². The changed coupled seed z=(beta W)^H is ACTUALLY rescreened. All original rows, scalar beta margins and same-leaf recovery remain paid; L=2H+2 and J<=k.

Set

    t=Norm(z)=beta^(2H) in R,
    v=W^H in B,
    n_j=beta^(2E_j), u_j=W^T_j,
    E_j=N+delta_j,
    T_j=ell_j+chi_D(j)(N+a_j).

Every n_j and u_j is acquired in soft k: signed binary exponents have O(log N) bits and B has constant rank. Distinct integer norm labels delta have unit-separated n_j by the original beta margin. Let M be their actual count. Under the controlled public modulus refinement M is Theta(k) and each norm fiber has at most16 rows; the argument below does not require that refinement and charges J raw rows.

At either local prime, n_j=t^i is equivalent to beta^E_j=beta^(Hi), because beta has odd order. Consequently the simultaneous conditions

    n_j=t^i, u_j=v^i                               (1)

are exactly the original WHOLE local equality V_j=z^i. The angular condition in (1) is not automatic from its norm condition. Conversely, the scalar norm condition already has its own original-beta factor/witness consumer; adding the angle changes which common incidences are sought, not the validity of that existing overcover.

At the unknown nonsplit prime p*, the orders of beta^H and v divide p*-1 and p*+1 and are odd, so they are coprime. The same is true of ord(t) and ord(v), both >C. The joint trajectory (t^i,v^i) therefore has period equal to their product, >C². No numerical period or p* is acquired. This statement does not transfer to a split coordinate or give coprimality of orders at DIFFERENT primes.

## 1. Execute an actual short joint-block ideal

Choose a paid block length b<=L. Since 2L<C on the continuing branch, all differences t^a-t^c for 0<=a<c<b are certified units. Acquire by monic product tree and unit-safe interpolation

    B_b(T)=product_(a=0)^(b-1)(T-t^a),
    C_b(T) in B[T], degree<b,
    C_b(t^a)=v^a for every 0<=a<b.                 (2)

All powers, coefficients and denominators cost soft b. This is an EXACT initialized graph ideal of the b joint seed points:

    (B_b(T), Y-C_b(T)) over B.                    (3)

The first coordinate T is scalar, but evaluating (3) takes place in the explicit constant-rank algebra B. This avoids treating the trajectory as four unconstrained recurrence starts. In particular b~k gives a genuine soft-k short-block representation, with all starts supplied.

The large-order information prevents a hidden collapse of this specific graph polynomial. Put n=b-1. Its leading coefficient is exactly

    lc(C_b)= product_(r=0)^(n-1)(v-t^r)
             / product_(r=0)^(n-1)(t^n-t^r).      (4)

Proof: the leading interpolation coefficient is a polynomial of degree n in the formal value parameter v. It vanishes at v=t^r for r<n, because then the data equal the degree-r monomial T^r. Its coefficient of v^n is the reciprocal last-node Vandermonde product. This proves (4) as a ring identity wherever the already certified node differences are units; no division by v-t^r is made.

The denominator in (4) is an actual scalar unit. At p*, the numerator has no zero factor: v!=1 by the supplier, while v=t^r for 1<=r<n would imply, on taking norms, t^(2r)=1, impossible since 2r<C. Therefore lc(C_b) is nonzero at p*, and C_b has EXACT degree b-1 there.

This has a paid factor-or-unit version over R. Acquire the numerator as the short scalar polynomial product_(r<n)(X-t^r) evaluated at the supplied v; compute its explicit rank-two norm and gcd. A nonunit norm is nonzero at p*, so it gives a PROPER factor, never a saturated obstruction. Otherwise the leading coefficient is a unit in B. The total cost is soft b. Thus the actual graph representation has degree b-1, with a certified unit leading coefficient or an immediate factor; a desired lower-degree interpolation is not merely missing a genericity proof in this particular representation.

This does NOT rule out a different low-total-degree ideal, implicit product circuit, or nonautonomous recurrence. It identifies the actual coefficient retained by the attempted graph compression.

## 2. Whole interval continuation: the states are actually acquired and counted

Write L=rb+d, 0<=d<b. For giant block g, acquire the shifted native target state

    T_(j,g)=n_j*t^(-bg) in R,
    Y_(j,g)=u_j*v^(-bg) in B.                      (5)

It matches a short joint seed node (t^a,v^a) exactly when the ORIGINAL row j hits at i=bg+a. No unknown order or division by an index is used. Geometric walks acquire all states in (5), but there are J*r of them. Equal norm labels can share the first coordinate; their angular comparisons still retain their actual rows. All labels, giant starts and the final d-length block are charged.

Monic multipoint evaluation of B_b and C_b at the actual scalar T states costs soft(b+M*r), with each B coefficient treated at constant rank. Comparing the actual angular Y values costs soft(J*r). The shorter last block costs soft(J+b), and its indices are clipped inside [0,L). Thus this fully initialized joint-state evaluation costs

    soft(J+b+J*L/b).                              (6)

At b~sqrt L~k the short ideal fits soft k but the state list costs soft k². Optimizing (6) uses b~sqrt(JL), giving the old soft(J+sqrt(JL)), at worst soft k^(3/2). This execution has not acquired a soft(J+b+r) contraction of the implicit state list.

Single-state common support is safe. Compute the scalar B_b(T) and Norm(C_b(T)-Y) at the SAME state. At a prime where B_b(T)=0, its unique local short exponent a gives C_b(T)=v^a; both v^a and Y are norm one. The supplier's norm-one lemma makes zero difference norm equivalent to WHOLE angular equality even on a split side. Therefore a gcd of N with these TWO same-state values detects exactly a joint local block hit. A proper gcd factors. At saturation, descend B_b's acquired root tree with the same angular condition. Different local a labels yield a proper factor; a saturated leaf fixes the same original a globally, and norm-one zero then gives the whole equality at both primes. The original i=bg+a and row label are recovered, so the retained beta consumer applies.

Computing products of the two tests separately and then taking their gcd is NOT that procedure: their zeros could occur at different states or indices. No such cross-index contraction has been performed in (6). The scalar norm-only overcover can already return a factor or original witness and remains the better established whole-query interface.

## 3. Exact bounded relations supplied by the larger period

These are useful proof-side restrictions, not acquisition algorithms.

For chi(j)=+1, V_j=A^E_j with A=beta W and z=A^H. At p*, the RAW beta and W orders are odd, coprime and both>C, so ord(A)>C² as well. Two bounded hits (j,i),(h,l) from this colour imply

    ord(A) divides delta_j-delta_h-H(i-l).

For i,l<L the absolute value is at most4H+H(L-1)<C². Therefore

    delta_j-Hi=delta_h-Hl AS INTEGERS.             (7)

All such hits on the nonsplit side occupy at most five possible adjacent integer index values, because the deltas have width4H. Equation (7) does not locate that unknown interval, does not show that the colour has a hit there, and is not a bound on split-side zeros. Its possible multiplicative order is not an acquired integer boundary value.

For chi=-1, T_j=E_j-2(N+a_j). Comparing two hits gives, with K=delta_j-delta_h-H(i-l),

    ord(beta) divides K,
    ord(W) divides K-2(a_j-a_h) at p*.             (8)

For the same a, (8) and the large coprime product again force K=0 in the bounded range. For different a, it is a near-diagonal CRT relation with a small angular offset; the two orders and its CRT residue are unknown. Enumerating offsets or describing the unique bounded solution class for each offset does not acquire the associated field collision or its index. The short-block algorithm (2)--(6) pays exactly for the actual target states instead of treating (7)--(8) as initialized recurrences.

## 4. The precise unpaid primitive and scope

All inputs to the joint short ideal, native target states, and first recurrence data are genuinely acquired in soft k. The remaining nonlinear operation is a RESTRICTED common-incidence/product contraction against the implicit family (5), with both coordinates tied to the same row and index, costing soft(J+b+r) instead of explicitly J*r. It must either compute a valid scalar/support witness or factor/discard restrictions with the retained original labels. A target/seed field order, a proof of no small aliases, or a low-output headline is not this operation.

One could equivalently interpolate bounded-width angular fiber polynomials over the acquired norm labels and test them at (t^i,v^i). With the controlled modulus those coefficient arrays really fit soft k, but a common-index long test still has to be executed. This note does not assume one. It also does not project W by N+1: large orders before that projection would not certify survival, and a saturated auxiliary torus annihilator is not an original beta leaf.

| Actual acquisition | Base-ring/bit work with usual logarithmic factors | Delivered quantity |
|---|---:|---|
| Supplied beta, W, changed coupled-seed screen | soft k | both odd local margins and original consumer |
| All norm/angular native labels n_j,u_j | soft k | actual scalar/rank-two targets |
| Short powers, B_b and C_b including every coefficient | soft b | exact joint seed graph |
| Leading coefficient (4) and its norm gcd | soft b | proper factor or exact degree b-1 with unit leading coefficient |
| All r giant starts and J*r shifted target states | soft(r+J*r) | actual row/block labels, no implicit-state oracle |
| Monic evaluation plus all angular comparisons and tail | soft(J+b+J*L/b) | actual same-index incidence/controller |
| Bound (7) or (8) | proof-side only | no acquired period, index, or long scalar value |

No completed uniform speedup has emerged from this attempt. The positive paid object is the exact short joint-trajectory ideal with its explicit, unit-certified leading coefficient and original-index consumer. The larger nonsplit period proves (7)--(8), but the actual whole-family continuation retains (6). The guaranteed query remains soft(J+sqrt(JL)); the one-sixth terminal target is still open.
