# Execute the adjacent q-product Wronskians before anchor emission

26 October 2026. Focused paper calculation, scratch only. Ordinary clock differentiation permits exact early cancellation; it removes the selected signal too. The noncovariant Wronskian preserves that signal as the logarithmic derivative of the EXACT shared finite gcd. Its initialized remaining cost is unchanged. This is a scoped calculation, not a general barrier.

## 1. Factor the adjacent products first

Treat T,r,s as independent parameters, and put

 A=1+s-T, B=1+s-T*r^h,
 K(T;r,s)=prod_(i=1)^(h-1)(1+s-T*r^i),
 P=G_h(T;r,s)=A*K,   Q=G_h(rT;r,s)=B*K.

K is the symbolic shared product; if endpoint factors are units it is the common collision support. Its degree is h-1, so its formula is not an acquired coefficient array or remainder. All calculations below hold after clearing denominators, including when K vanishes.

Let D=r*partial_r at fixed T,s. The FULL q-Wronskian is

 W_full=P*D(Q)-Q*D(P)=-h*A*T*r^h*K².                (1)

This cancellation happens BEFORE any numerical anchor is emitted: all D(K) terms cancel by the determinant. The normalized ratio Q/P=B/A is already an acquired endpoint function. Its logarithmic q derivative, W_full/(P Q)=-h*T*r^h/B, therefore has only the endpoint residue. Thus (1) is a genuinely cheap symbolic contraction of a correlated derivative, but not of the desired coefficient.

## 2. Keep the noncovariant derivative that carries the interior

The derivative needed in deformation-cancellation.md holds the FIRST argument of G fixed when taking r partial_r. For Q=G(rT;r,s), the chain rule says

 B_partial(Q)=D(Q)-T*partial_T(Q).

Consequently the relevant noncovariant Wronskian is

 W_partial=P*[D(Q)-T*partial_T(Q)]-Q*D(P)
   =A*T*r^h*(1-h)*K² - A*B*T*K*partial_T(K).        (2)

In particular

 W_partial/(P Q)=(1-h)*T*r^h/B-T*K_T/K.             (3)

This is a full product-level derivation before singular specialization; it does not assume that log derivatives or nonunit ratios are numerical inputs. At r=rho,s=delta the right side's interior residue is exactly the count in K: at a hit T*rho^i=1 with 1<=i<h, Res(T*K_T/K)=-1. Canonical row weighting gives M1 or the packed C. The finite endpoint term in (3) is the one already tracked in the contiguous identity.

The distinction between (1) and (2) is essential. Replacing the noncovariant derivative by the derivative of the composed polynomial Q makes the missing T*partial_T(Q) term disappear and falsely suggests that endpoint contraction retains the desired count. Equation (2) explicitly locates the retained signal.

## 3. Execute the remaining gcd/log-derivative target

One can symbolically cancel the shared K in Q/P without computing it. That loses its collision multiplicity. Recovering its logarithmic residue in (3), instead of the full K, is still an admissible smaller output, and is not proved to require the full product by this argument.

The existing complete execution is explicit: K is the length-(h-1) q-product with start rho*T_j. Acquire its values and regulator/row tangent derivatives at the original J starts by the shared monic baby/giant engine. With baby width b this emits b baby factors and J*ceil((h-1)/b) anchors, with a fixed-rank tangent algebra. Its bill is

 soft(J+b+J*(h-1)/b)=soft(J+sqrt(Jh)).

Classifying the row values gives ordinary hit flags; the derivative route computes the exact log-residue at globally zero rows using its unit first regulator derivative. Every failed inversion is norm/coordinate-classified. Only ACTUAL endpoint leaves get a two-coordinate annihilator decoder. All weighted sums and endpoint corrections are soft J thereafter. The algorithm removes one clock position, not a power of h.

Equivalently, Euclid of the two EXPLICIT long products P,Q returns the known symbolic K. To use a fast half-GCD or modular short-row computation numerically would require the actual K remainder, or an algorithm supplying ONLY its selected log-residue. The low-degree ratio B/A supplies neither: it forgets the common factor. Thus this particular early-cancellation algorithm leaves a precise operation, not a hidden full-polynomial requirement asserted as a general fact.

A useful future contraction could bypass K and evaluate only the weighted singular coefficient of T*K_T/K in (3) jointly over the native starts. The Wronskian calculation identifies that source with all signs, endpoints and initialization, but does not acquire it in soft K. It is not a proof against a transposed or nonlinear selected-scalar algorithm.

## 4. Independent Ward-cavity review

Read ward-cavity-contraction.md in full. PASS: the regulated source covariance and Schur complement are exact; the normalizer is a certified unit. Opposite replicas give +delta²/(delta²-a²), whose constant coefficient is precisely the original hit weight; their finite paired-product prefactors are correct. The singleton reset solve and effective kappa/RHS are correct under BOTH unit-pivot hypotheses. Certified regular-cavity deletion is lawful, while a macroscopic cavity certificate is correctly charged. The report does not assign arbitrary additive zeros the torus decoder or claim an improved factoring exponent.
