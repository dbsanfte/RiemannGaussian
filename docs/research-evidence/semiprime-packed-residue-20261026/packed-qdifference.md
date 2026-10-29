# Packed symmetric coefficient: consumer audit and finite q-residue execution

26 October 2026. Scratch only. The exact coefficient audited here is the one in the authoritative [six-domain README §§1–2,9](../semiprime-six-domain-acquisition-20261026/README.md), not a generic or unspecified scalar. No soft-K acquisition algorithm is established.

## 1. Independent packed-consumer audit: PASS

Let K=2*3^e, n=3^ceil(e/2), D0=3^floor(e/2), L=K/2=n*D0. Use the ORIGINAL beta-coupled weighted bank, exactly one row per unit j, not the raw torus-only bank or a completed catalogue. At the correct nonsplit bin all hit colours j equal R modulo n. Of the K/n=2D0 lifts of that residue modulo K, exactly D0 are odd, all units. Each row has at most one hit. Thus 1<=d<=D0, including multiplicities and axes.

For canonical u=[R²]_n and weights L+[j²]_n, the actual residue C is the scalar c=dL+du at the good field. Since 0<du<=D0(n-1)<L, floor(c/L)=d and (c-dL)/d=u. The interval 0<c<M=(D0+1)L is below BOTH primes: D0<=sqrt(K/2) and e>=3 give M<4H<16H<P,Q. Thus no good-field wraparound occurs. The word canonical is essential; the rational expression j² in the native algebra would not supply this integer packing.

Write acquired C=c0+c1*tau. The good nonsplit reduction has c1=0. A proper gcd(c1,N) factors; gcd one can only reject a wrong-bin attempt; gcd N makes C globally scalar. This argument remains valid even if the other prime splits, since divisibility of the coordinates at the nonsplit field is the needed input.

If canonical c0<M, both c0,c<R and their good congruence forces equality. Otherwise a monic blocked product over a=0,...,b²-1, b=ceil(sqrt M), contains a=c. Its padding is safe: b²<=4M<16H<P,Q. A proper gcd factors; inspect only one saturated block (at most b leaves). A saturated difference c0-a implies c0=a as canonical integers, and a,c<R implies a=c. Invalid padding candidates in a wrong bin are rejected by the count/divisibility/unit-square checks. A correct bin cannot be rejected. Processing O(log N) bins and continuing after wrong-bin failures retains soft K recovery.

The blocked modular search costs soft sqrt M=soft K^(3/4), including all block gcds and inspection of one block. The two Hensel roots of a valid unit square modulo n, complements when needed, and inherited restricted-HH consumer cost soft K. This is a sound single-output consumer. It does not acquire C, and it does not prove a query-speed improvement.

## 2. Primary q-discrete-residue contract actually checked

Chen–Singer, *Residues and Telescopers for Rational Functions*, arXiv:1203.4200v1, https://arxiv.org/html/1203.4200 , §§2.3 and 4.1.3, treats characteristic-zero fields and q not a root of unity. Their q-residues group partial fractions by whole multiplicative q-orbits; vanishing characterizes rational q-summability. This is an existence/reduction contract, not an algorithm for this finite modular clock window. The published version is *Adv. Appl. Math.* 49 (2012), 111–133, DOI 10.1016/j.aam.2012.04.003.

Arreche–Sitaula, arXiv:2503.15636v1 (19 March 2025), https://arxiv.org/html/2503.15636v1 , §§1–2, supplies factorization-avoiding residue algorithms for the ADDITIVE shift x->x+1 over a computable characteristic-zero field, with a denominator-autodispersion black box. Their discussion identifies q analogues as a further context, not a ready-made nearlinear finite modular window evaluator. We do not import their field or orbit oracles into B.

The following finite equations are proved directly and therefore survive actual modular specialization. They do not rely on either source's characteristic-zero hypotheses.

## 3. Execute a finite endpoint telescoper on the packed input

Acquire the short weighted rational function

 F(Z)=sum_j (L+[j²]_n)/(1-T_j Z)

by product-tree rational addition, total soft K, allowing repeated T_j. Set

 S_h(Z)=sum_(i=0)^(h-1) F(rho^i Z).

Then EXACTLY

 S_h(rho Z)-S_h(Z)=F(rho^h Z)-F(Z).                    (1)

The endpoint right side has degree at most 2J and is acquired in soft K. The required original additive regulator is the normalized pullback

 A_h(delta)=(1+delta)^-1*S_h((1+delta)^-1),
 C=[delta^-1] A_h(delta).                              (2)

In particular no unwanted multiplicative T_j or regulator weight is introduced.

Here is an actual initialized formal-series solution to (1). Acquire f_m=sum_j w_j T_j^m for O(K) initial m by weighted product-tree power-series expansion. Its coefficients are

 [Z^m]S_h(Z)=f_m*sum_(i=0)^(h-1)rho^(im).

For 1<=m<=O(K) inside the short screen the second factor equals (1-rho^(hm))/(1-rho^m); the numerator is acquired by binary powering, denominator screened. At m=0 it is h. Thus O(K) initial coefficients, endpoint rational data, and the exact q-difference equation are genuinely acquired in soft K. No full h clock array is emitted.

This initialization does NOT yet give (2). Solving for all rational coefficients can require the full long support, while a selected singular solution need not. The unfinished operation is advancing this particular initialized q-difference equation to the principal part of (2), without producing all of S_h. A method exploiting the native T_j to do only that would be a real advance. Equation (1) alone is not such a method, and no generic impossibility follows from it.

## 4. Native reason whole-orbit residue reduction loses the finite selector

At the nonsplit prime R, Frobenius gives barpi=pi^R. The actual normalized row root is therefore

 T_j=pi^(H*M0+ell_j+R*(a_j+b_j*N)).

The pi order is odd and K-rough, hence coprime to H. Consequently q=pi^H generates the SAME local cyclic subgroup as pi. EVERY acquired T_j lies in the q-orbit of 1 at the good field, not only the roots hit inside the finite clock 0<=i<h. This is an exact native statement; it does not acquire the inverse of H modulo the unknown order or any discrete logarithm.

For a simple source w/(1-TZ), its pole beta=T^-1 has ordinary residue -w*beta. In multiplicative discrete-residue normalization, shifting that pole by rho^k divides its ordinary residue by rho^k, so a whole-orbit invariant counts its weight regardless of the clock position. Thus whole-orbit membership/reduction on this native input cannot distinguish a finite-window hit from an outside-window pole. The selector missing from that PARTICULAR source reduction is the unknown finite orbit position, not the tag or a scalar normalization. This is not a lower bound against direct selected-residue algorithms.

The endpoints in (1) are essential: they describe the boundary of the finite window, not a license to replace the window by the whole q-orbit. Computing their ordinary q-residue classes loses that boundary. An efficient finite-orbit-position reducer preserving these endpoints could still solve the problem, but no such initialized algorithm is supplied by the cited results.

## 5. Specialization and residue extraction do not commute generically

A tempting creative-telescoping shortcut is to take a residue in delta over B(Z) and then specialize Z. That loses the wanted singular fibre: for 1/(delta+1-Z), the formal delta^-1 coefficient over a generic parameter field is zero, but after Z=1 it is one. Our target is exactly such a singular specialization. A telescoper may be useful if it transports the singular-fibre data or a valid local certificate; a generic regular solution and its zero residue do not initialize that data.

This concrete caution explains why the acquired short moments in §3 and a parameter telescoper are not already C. It does not claim they can never be combined with another arithmetic measurement. Composite inversions must still be norm/coordinate-classified; saturated additive pivot expressions are not automatically actual short torus annihilators.

## Outcome

The packed single-coefficient consumer passes, with genuinely weaker output requirements than a full norm or a whole resolvent. A finite endpoint q-telescoper, all its O(K) short starts and the native whole-orbit structure have been executed explicitly. The unresolved readout is the singular specialization (2) with its finite orbit-position boundary. The inherited row-value engine still completes the original family at soft K^(5/4); no sixth-rate acquisition theorem is claimed.
