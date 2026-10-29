# Joint finite Lambert poles: six domains, two executed contractions

26 October 2026. Scratch paper investigation; no repository edits or numerical campaign. Result: two explicit contractions below retain a long singular remainder. Neither improves the complete soft K^(5/4) baseline. The singleton block promise does remove normalization and growing pole precision, which is retained throughout.

## 1. Actual input and desired output

Use the ORIGINAL paired bank and its direct blocks b=floor(min(j,K-j)/n), n=3^ceil(e/2), K=2*3^e. There are L=K/(2n)=Theta(sqrt K) blocks, each degree d=phi(n)=Theta(sqrt K), total J=phi(K). At the correct nonsplit bin each block has at most ONE leaf hit; at least one block hits. The weight w_j is the canonical integer [j²]_n, constant on each sign pair. No primitive-only coverage promise is substituted.

Let x_i=rho^i, 0<=i<h, h=O(K^(3/2)), and c_i=(-1)^i rho^(i(i+1)/2)[h-1 choose i]_rho. These are implicit unit formulas, not an acquired h-entry list. The acquired block rational inputs are

 r_b(X)=sum_(j in b)1/(1-T_j X),   s_b(X)=sum_(j in b)w_j/(1-T_j X).

All numerators/denominators together cost soft K, without separating T_j. We want coefficients delta^-1 of sum_i c_i r_b(x_i/(1+delta))/(1+delta), and the analogous s_b expression. Empty blocks MUST give zero at the good field. A unit pair then supplies the square tag; select at most one unit block PER BIN and continue after a wrong-bin rejection.

## 2. Counted catalogue: six mathematical domains

These are exact distinct bridges, not six new discoveries. Their old credit is explicit.

1. **Finite q-series / Lambert partial fractions.** With kappa=(rho;rho)_(h-1),
   sum_i c_i/(1-z x_i)=kappa/(z;rho)_h.
   This converts a clock sum to inverse row products. The regulated expression is kappa(1+delta)^(h-1)/prod_i(1-z x_i+delta). This is the already frozen polar-reciprocity bridge; no normalization is needed on singleton blocks.
2. **Orthogonal polynomials / rational quadrature.** Define the finite functional Lambda(p)=sum_i c_i p(x_i). Its moments are mu_t=(rho^(t+1);rho)_(h-1). A degree-d Padé denominator corresponds, when the needed Hankel pivots are units, to formal orthogonality for Lambda. The exact error identity in §3 is valid even without positive measure or orthogonality. This tests whether a shared short quadrature really evaluates the rational block inputs.
3. **Algebraic geometry / local duality.** Put W(X)=prod_i(X-x_i). The exact Cauchy transform is C(z)=Lambda(1/(z-X))=kappa*z^(h-1)/W(z). The desired regulated row function is T_j^-1*C((1+delta)/T_j); its delta residue is c_I at a hit, because the linear change z-x_I=delta/T_j cancels this prefactor. Thus the same target is a sum of pullbacks of a global rational differential. Intersection with the clock divisor is retained; a residue theorem alone does not acquire that intersection.
4. **Structured linear algebra / finite algebra traces.** In A=B[X]/W with companion M_X, Lambda(p)=trace(D p(M_X)), where D acts diagonally by c_i in the split basis. Hence r_b is a weighted resolvent trace. This is an exact h-dimensional description. Alternatively each short block denominator gives a d-dimensional companion but the outer function is the same unacquired Cauchy transform. The rank-one displacement input previously paid does not itself evaluate this nonlinear rational functional.
5. **Symbolic recurrences / simultaneous modular remainders.** The vector of inverse row products and derivatives is obtained from the finite q-factorial modulo the product of the block denominators (degree J), followed by a remainder tree. This is a complete joint route and leads to §4's soft(J+sqrt(Jh)) bound. Singleton gcd degree at the good field does not shorten the required initial modular factorial remainder by itself.
6. **Askey–Wilson divided differences / spectral lowering.** Each sign pair is P_h(c,x)=(cx,c/x;rho)_h and satisfies
   P_h(c,rho^½x)-P_h(c,rho^-½x)=c*rho^-½(1-rho^h)(x-x^-1)P_(h-1)(c*rho^½,x).
   This is division-free and its regulated version gains (1+delta). It changes centre as well as spectral coordinate; retaining the original centre leaves the same long common factor. This executed identity is in even-recurrence.md, not a fresh contraction theorem. Native c varies with the Gauss coefficients.

The finite-Lambert and AW links are credited to the frozen [even-acquisition packet](../semiprime-even-acquisition-20261026/) and its primary finite identities. The trace/companion and local-duality formulas here are elementary derived identities, not imported algorithmic guarantees.

## 3. Execute shared short Padé/quadrature, retaining its exact error

Acquire mu_0 in soft sqrt h, and O(d) moments via mu_(t+1)=mu_t(1-rho^(h+t))/(1-rho^(t+1)); short differences are screened. Let Q be ANY acquired polynomial of degree d, and define

 P(z)=Lambda((Q(z)-Q(X))/(z-X)).

P is obtained from these short moments in soft d by convolution. Then EXACTLY

 C(z)=P(z)/Q(z)+Lambda(Q(X)/(z-X))/Q(z).                       (A)

This is a finite polynomial identity after clearing Q; no Hankel pivot is needed for its validity. A formal Gaussian/Padé choice of Q can cancel many Laurent coefficients at infinity, but does not remove the second term as a rational function.

The rational quadrature candidate executes as follows: acquire Q,P, evaluate T_j^-1*P(z_j(delta))/Q(z_j(delta)) with z_j(delta)=(1+delta)/T_j by monic MPE and fixed-depth jets, and sum weighted block residues. The exact error pullback is T_j^-1*Lambda(Q(X)/(z_j(delta)-X))/Q(z_j(delta)). This costs soft K if Q has degree O(d), provided any required inversions pass norm/coordinate tests. But if Q(1/T_j) is a unit at a hit component, P/Q is REGULAR there and its residue is zero. The normalized error pullback then has precisely the full native delta residue c_I: C has residue c_I at x_I, the variable change contributes T_j, and the prefactor T_j^-1 cancels it; the polynomial part is regular. Thus the inexpensive approximation can omit the entire required signal, not merely an unimportant scalar normalizer.

To justify discarding the error on the actual bank, one would need a new native support theorem: every clock hit in every relevant block lies among roots of the chosen Q, with correct residues. No such theorem follows from matching moments or singleton support. This is a necessary condition for THIS quadrature substitution, not a claimed unattained native counterexample and not a lower bound for arbitrary rational quadrature algorithms. A globally exact C(z) requires all h simple poles since every c_i is a unit; the actual-bank task only asks a much smaller selected singular readout.

If a Padé construction introduces Hankel pivots, a proper norm gcd may terminate. A saturated/nonunit pivot cannot be silently inverted; a field-only normal-index theorem is not a composite-ring initialization. The direct error calculation (A) bypasses that issue and still exposes the retained singular data.

Primary context read: Allen–Chui–Madych–Narcowich–Smith, *Padé approximation and orthogonal polynomials*, Bull. Austral. Math. Soc. 10 (1974), 263–270, https://doi.org/10.1017/S0004972700040879 ; primary PDF https://www.cambridge.org/core/services/aop-cambridge-core/content/view/A56674619ABE0C4A0641B6815FB44B29/S0004972700040879a.pdf/pade_approximation_and_orthogonal_polynomials.pdf . Their Stieltjes positivity setting is NOT assumed for this finite modular functional. Equation (A) is proved directly above.

## 4. Execute simultaneous short-denominator reduction

Let D_b(X)=prod_(j in b)(1-T_j X), and D=prod_b D_b, degree J. Constant terms are units; equivalently reverse to monic factors. Acquire the modular factorial G_h(X)=prod_i(1-rho^i X) modulo the monic root polynomial and the first derivative by the inherited division-free baby/giant engine. With block length a the actual work is soft(J*a+h/a+J); balancing gives soft(J+sqrt(Jh)), i.e. K^(5/4). A remainder tree sends the resulting values/first jets to every row/block in soft J, regardless of repeated roots.

Norm/coordinate classification factors or makes every row value globally zero/global unit, using the nonsplit field. On a globally zero row the derivative is a unit because each local row has only one clock hit. Its residue c_I is acquired by kappa/(-T_j G_h'(T_j)); sum it and w_j*c_I by blocks. This is a fully initialized algorithm with the required empty-block zeros. It uses no unknown clock index, no increasing Hasse precision, and no source-to-knot normalization.

Running this engine independently on degree-d blocks costs L*sqrt(dh)=K^(3/2); the joint product tree is essential. The singleton good gcd degree (zero or one) does not supply its subresultant: a fast half-gcd requires the actual modular remainder of the long factorial, or an alternative exact structured input for that step. This specifies the missing handoff rather than asserting that the gcd needs a full norm for every possible algorithm.

Modern polynomial-remainder source checked: Dumas–Grenet, *Fast in-place accumulation*, arXiv:2302.13600v7 (6 November 2025), JSC 134 (2026) 102523, https://arxiv.org/abs/2302.13600v7 . Its input is an actual supplied numerator polynomial and divisor; improved accumulation/storage does not generate the implicit q-factorial numerator or its selected singular remainder. No theorem from that paper is used to promise a new time bound here.

## 5. Exact next sufficient statistic

The two concrete executions isolate a smaller useful primitive: a simultaneous **selected singular remainder** of the finite Cauchy transform C(z), on O(sqrt K) rational block domains of total degree K, with guaranteed empty-domain zero and at most one good pole per domain. A short Padé polynomial part is already paid; its error term carries the full missing signal. The old modular factorial engine acquires that signal at K^(5/4). A nearlinear method for these selected errors, rather than their whole rational functions or all h coefficients, would complete the current consumer.

Neither an arbitrary failed inversion nor an additive zero is automatically a torus annihilator. Existing global torus decoders apply only when the failed expression is proved to be a nonzero short native torus label; they cannot legalize deleting the error in (A) or inverting a saturated Hankel pivot. No such hidden order or label supplier is assumed.
