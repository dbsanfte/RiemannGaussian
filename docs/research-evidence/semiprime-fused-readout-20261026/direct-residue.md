# Direct simple-pole readout: short weighted sectors

26 October 2026. Scratch derivation; no implementation, numerical campaign or repository changes. **A weaker uniform short-clock acquisition target is proved; it is not acquired in soft K.** The existing complete weighted factor query remains soft K^(5/4). This report does not improve that factor bound.

Inputs actually read: frozen `semiprime-direct-contraction-20261026/singular-solve.md` and the authoritative frozen [hybrid-handoff.md §5](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-axis-supplier-20261026/hybrid-handoff.md), especially its short weighted-sector contract. All torus preparation, correct-bin weighted Gauss coverage, exact-integer provenance and restricted-HH consumer are inherited contracts, not supplied anew here.

## 1. Remove unknown Hasse depth without lengthening the clock

Use the prepared torus algebra B=(Z/N)[tau]/(tau²-D), with D and 2 units. The already executed coupled order screen certifies every 1-q^t, 0<|t|<=16H, a unit; otherwise preparation has already returned a factor. The weighted family in each public size bin has J_total=O(K) rows and clock length h=O(K^(3/2))<16H. Its correct bin has a nonsplit good prime R, exact-integer provenance, and at least one hit. Retain original signed sectors, actual canonical phases, deletions and axes; none is completed or replaced by an uncoloured rectangle.

Partition nonaxis rows by g=gcd(a,K)=gcd(b,K). Here g<=sqrt K by the Gauss product bound. Write n_g=K/g and w_j=[j]_(n_g). The inherited valuation proof says EVERY good-field hit in this sector has w_j=r=[R]_(n_g). It does not require a unique hit. For a sector define the two rational functions

    S_0(delta)=sum_(j,i) 1/(1-y_j*q^(-i)+delta),
    S_w(delta)=sum_(j,i) w_j/(1-y_j*q^(-i)+delta),
    V=[delta^0](delta*S_0), U=[delta^0](delta*S_w).       (1)

These are formal Laurent coefficients, not instructions to invert mixed nonunit constants. Because B is a product of finite fields, each summand is either regular at zero or exactly delta^(-1). Every row has at most one hit in the clock at EVERY field component by the paid order guard. Thus (1) exists globally, with pole order at most ONE regardless of the number d of hits. At the good field,

    V=d, U=d*r,  1<=d<=J_sector<=J_total<R.              (2)

Consequently d is nonzero and U/V=r there. Unlike the leading slice of a product, (1) has no unknown multiplicative amplitude and needs no precision d or search for d. The simple-pole residue counts multiplicities of repeated rows correctly.

No root separation is needed: use the direct product B^J of the acquired row list. Do NOT replace it without qualification by B[X]/F when F has repeated roots: the latter has nilpotents and its resolvent can have higher-order poles. Direct sums or the scalar sums (1) avoid that error. If desired, the row rational function is represented by

    F(Z)=prod_j(Z-y_j), N_w(Z)=sum_j w_j*F(Z)/(Z-y_j).

Both are acquired by a product tree with weighted numerator combination in soft J, including repeated roots, with no F′ division. This short rational representation does not evaluate its long clock sum.

Axes retain their separate provenance. The shortest torus axis rows (±K,0),(0,±K) have the inherited exact phases forcing R=j mod K at any good hit. Apply (1) with full tag modulus K. This is not a tag interpretation of arbitrary scalar-axis aliases.

## 2. Fully paid consumer if all sector pairs are supplied

For each supplied pair, compute gcd(N,Norm(V)). A proper divisor terminates. If the gcd is N, skip the pair; that cannot discard a good sector with d>0 because its good-field value is nonzero. Otherwise V is a genuine unit in B and is inverted by its unit norm. Write U/V=A+B*tau. A proper gcd(N,B) factors; gcd 1 rejects the pair; gcd N leaves a global scalar A. Scan 0<=r<n_g using gcd(N,A-r), retaining unit tags only. A proper gcd factors; a global zero supplies a bounded residue candidate. On a correct-bin nonempty sector the scan either factors or supplies the actual nonsplit-factor residue.

The total scan cost over sectors and bins is soft K since sum_(g|K) K/g<=K(1+log K). Lift a returned residue modulo K/g to its g possibilities modulo K. Across bins the palette size is bounded by O(log N)*(1+sqrt K*tau(K)); the axis adds a constant number of candidates per bin. Uniform tau(K)<=C_epsilon K^epsilon, epsilon=1/12, and absorption of log N into K^(1/12), give S<=C K^(2/3) with a fixed constant (and deduplication can only help). Complement every unit candidate by N/r modulo K so the smaller-factor convention causes no loss.

The restricted HH consumer at n=K and r_HH=ceil(16 C K/S), increasing fixed constants if necessary, costs soft K. Its order premise uses the prepared SCALAR beta: beta^(n²)=beta^H has both local orders>16H. It does not use a torus order as a scalar order, nor infer any new order preparation. Wrong bins/sectors generate only checked factors, bounded candidates or failure. At least one actual sector or axis is covered by the inherited complete weighted family. Thus acquisition of ALL pairs (1) in total soft K would suffice uniformly; no uniqueness, root separation or variable Hasse depth is required.

This improves the output specification, not an already available factorer: one useful selected row was already enough, and the old complete nonunit query already factors at soft K^(5/4).

## 3. Execute a finite residue algorithm and account for it

Here is a completely initialized baseline that does not form any Hasse jets. Acquire all row values

    G_h(y_j), G_h(T)=prod_(i<h)(1-q^(-i)T)

by the existing shared geometric-product engine, in soft(J+sqrt(Jh)) for each acquired row family. Norm/coordinate classification then either returns a proper factor or classifies every surviving value as globally zero or globally unit. In the no-factor case assign a 0/1 hit flag per row, sum flags and weighted flags in each sector, and obtain EXACT (1). Repeated rows are simply counted again. No root derivative inverse is needed. Over bins this retains the inherited soft K^(5/4) bound. Saturated known row labels use only the already licensed decoder; any T_ext call remains once-only on a terminating branch and is not relabelled polylogarithmic.

The rational-block attempt can be executed equally explicitly. Partition the clock into b-step blocks and, for each block, form its denominator product and numerator of its logarithmic derivative. Extracting the block's first Laurent residue requires determining which components of that denominator vanish: it is the block hit idempotent. Distinct blocks have disjoint hit supports at each row, so residues ADD exactly; no inclusion-exclusion or unit quotient is needed. However there are ceil(h/b) blocks, and general monic remainder/gcd or simultaneous row evaluation of degree-b data costs soft(J+b) per block after acquisition. This gives soft((J+b)h/b), not a soft-K algorithm. It is a specific finite route, with no uninitialized inverse hidden in the notation. The shared-product baseline is better.

In particular, the pole-order-one property permits addition of residues but does not license Newton inversion at a mixed zero-divisor constant. Knowing that a block residue is an idempotent does not supply that idempotent. This failure concerns this explicit block-residue route; it is not a general lower bound.

## 4. Paid q-antiderivative and rational-summation source scope

The frozen report explicitly acquires the Gekhtman–Kasman core

    T_h(F)(z)=z^J+(q^J-q^h)*sum_(r<J) f_r*z^r/(q^r-q^h),
    (sigma_q-q^h)T_h(F)=(q^J-q^h)F.

Only short certified q differences are inverted. Its MPE values cost soft J. At fixed J its coefficientwise extension is linear and has no finite-clock membership mask. For the degree-<J tagged numerator N_w use (q^J-q^h)*sum_(r<J) [z^r]N_w*z^r/(q^r-q^h), with NO monic z^J term. This corresponding linear tagged input does not extract (1). The source's [rank-one integrable theorem](https://arxiv.org/html/math-ph/0408038) supplies a determinant/tau identity, not a mixed-component Laurent-projection algorithm. This is inherited acquired data; no new core claim is made here.

The primary [Chen–Singer, Residues and Telescopers for Rational Functions](https://arxiv.org/abs/1203.4200) studies rational q-summability through q-discrete residues. Its characteristic-zero, non-root-of-unity setup does not authorize an unknown finite-field orbit-membership algorithm. Here q is necessarily torsion locally, only its short differences are certified, and the finite boundary is essential. A characteristic-zero summability certificate or a short rational input cannot be counted as an initialized finite-ring solver. The previous constant-degree q-Gosper attempt remains prior failure, not new evidence here.

The sharply reduced remaining task is now: from O(K) weighted rows, actual short clocks and acquired sector tags, compute ONLY the two additive simple-pole residues (1), simultaneously over all sectors/bins, in soft K. No multiplicative amplitudes, unknown leading degree, separated-root hypothesis, or monic longer-clock detour is necessary. No such faster projection algorithm is established in this report.
