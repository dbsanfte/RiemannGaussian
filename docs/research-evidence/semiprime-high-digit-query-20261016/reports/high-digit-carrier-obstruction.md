# High-digit energy excludes small arithmetic and geometric progression carriers on the actual majority family

2026-10-16. Classical actual-source theorem. The argument uses the varying high input digit and additive energy, not merely the low square-image boundary. No whole-query algorithm or arithmetic-operation lower bound is claimed.

## 1. Uniform high-digit energy bound

Fix an odd prime m and a nonzero residue n in {1,...,m-1}. For h=0,...,m-1 set N_h=n+mh. For each tag j=1,...,m-1 let I_j be its inverse modulo m, a_j the canonical representative n j^(-2) mod m, and use the literal centered source lift

 b_j(h)=centered(-I_j(N_h-a_j j^2)/m mod m),
 delta_j(h)=a_j+m b_j(h)-2a_j j.

The quotient is integral, and changing h gives the exact congruence

 delta_j(h) = delta_j(0)-m I_j h (mod m^2).       (1)

The literal delta depends only on N modulo m^2: adding m^2 to N leaves both its canonical a and centered b unchanged. Let Delta_h be the deduplicated integer offset set. Its low image is n(S-1), with S all squares including zero, so

 |Delta_h| >= (m+1)/2.                           (2)

For a finite integer set V define its additive energy

 E(V)=#{(x_1,x_2,x_3,x_4) in V^4:x_1+x_2=x_3+x_4}.

Then the uniform bound is

 sum_(h=0)^(m-1) E(Delta_h) <= 4m^3.             (3)

Proof. Count ordered TAG quadruples instead; selecting one representative tag for each distinct offset injects set-energy quadruples into tag quadruples. Write their inverse residues t_1,t_2,t_3,t_4, all nonzero. Low-digit equality requires

 t_1^2+t_2^2-t_3^2-t_4^2-2(t_1+t_2-t_3-t_4)=0 mod m.         (4)

There are at most 2(m-1)^3 such ordered quadruples, since after fixing three variables the fourth satisfies a monic quadratic. Put S_1=t_1+t_2-t_3-t_4. If S_1!=0, equation (1) shows that equality modulo m^2, hence exact integer equality, occurs for AT MOST ONE h. If S_1=0, (4) also equates the sums of squares. Because 2 is invertible, the two pairs have equal sums and products, so their unordered multisets coincide. The tags are therefore the same unordered pair; there are at most 2(m-1)^2 such ordered quadruples, each contributing for at most m high digits. Their total plus the nonzero-S_1 bound is at most 2m(m-1)^2+2(m-1)^3 <=4m^3. No high-digit distribution assumption is used.

## 2. One simultaneous energy threshold excludes all small AP carriers

Fix 0<eta<1. Markov's inequality applied to (3) shows that for each low digit n at most 4m^(1-eta) high digits satisfy E(Delta_h)>m^(2+eta). Therefore the set of coprime input residues N modulo m^2 with that excessive energy has cardinality at most

 4m^(2-eta).                                                (4)

For every other residue, consider ANY cover by k finite INTEGER arithmetic progressions with total listed length T. Holes are allowed; all starts, steps, lengths, counts and assignments may depend on the full input or private advice. Steps may have arbitrary magnitudes or signs. Partition the actual distinct nodes among the progressions, obtaining disjoint sets V_i of sizes n_i, with sum n_i=J. Ignore empty parts. For a progression of length T_i, |V_i+V_i|<=2T_i. Cauchy--Schwarz gives E(V_i)>=n_i^4/(2T_i). Their internal energy quadruples are disjoint, so

 E(Delta)>=sum_i E(V_i)>=sum_i n_i^4/(2T_i)
          >=J^4/(2 k^2 T).                                  (5)

For clarity, the last inequality is Holder followed by sum_i T_i^(1/3)<=k^(2/3)T^(1/3). Together with J>m/2 and the retained energy threshold this forces

 k^2 T >= m^(2-eta)/32.                                     (6)

This applies SIMULTANEOUSLY to all advised integer progressions, with no enumeration or union over cover parameters. It is a literal integer-offset cover, not a cyclic cover modulo an unknown group order. For eta=1/25=.04, a carrier of total length T<=Cm needs k>=m^.48/sqrt(32C); a polylogarithmic number of progressions needs T>=m^1.96/(32k^2). Thus a bounded number of O(m)-total-length progressions is excluded, with a polynomial gap rather than only a constant-factor density loss.

## 3. Transfer to the same actual majority supply

Use the inherited original order-qualified balanced prime-pair supply P,Q=Theta(M^3), candidate m~M, and envelope K_*=O(M^.020). The pinned endpoint theorem supplies the actual varying-menu selector strips: at fixed P,m the Q strip is covered by O(G_m+1) half-open intervals of width at most m^2, where

 sum_m(G_m+1)=O(K_* M).                                      (7)

P is a unit modulo m^2. Thus Q -> P Q modulo m^2 is bijective, and each such interval contains at most one integer Q for each bad product residue. Equation (4) gives O(m^(2-eta)) bad Q per box, counting all integers and therefore also prime Q. There are O(M^3) possible integer P. Consequently

 bad original ordered pairs <= O(M^3 sum_m m^(2-eta)(G_m+1))
                            = O(K_* M^(6-eta)).              (8)

The candidate m values vary with the input. Multiplying a fixed-m global-box count by only K_* would not be valid; (7) is precisely the needed varying-selector control. Taking eta=.04 makes (8) O(M^5.980). Union it with the existing soft O(M^5.994) losses against the SAME original qualified supply of size Omega(M^6/log^2 M). The remaining family still has that order of magnitude. On EVERY remaining pair, at EVERY current candidate m, E(Delta)<=m^2.04 and (6) holds for ALL advised covers. No free simultaneous union over extra input menus is asserted.

This is an absolute bad-input count, not an intersection of independently thin retained families. No new prime-distribution theorem or hidden-field independence is used. The same new loss may also be unioned with the established endpoint/unit/exclusive-row losses, which are measured against that original supply and have smaller-than-six exponents. The energy statement itself uses no local-order hypothesis; that hypothesis is inherited only when combining with earlier gamma/query conclusions.

## 4. Arbitrary geometric carriers, including cyclic wraparound

Let gamma lie in ANY abelian group and have order D>8m^2. For the actual targets Z={gamma^(-N-delta):delta in Delta}, equality z_1 z_2=z_3 z_4 is equivalent to D dividing delta_1+delta_2-delta_3-delta_4. The absolute value of that integer is at most 8m^2, strictly less than D. Hence it is zero, and the multiplicative energy is EXACTLY

 E_times(Z)=E(Delta).                                        (9)

This applies separately in each hidden field under local order R>8m^2, and in the global unit group modulo N, where the order of gamma is a multiple of each local gamma order. No order or discrete logarithm is supplied to an algorithm.

Now cover Z by k arbitrary finite multiplicative geometric progressions {c_i rho_i^s:0<=s<T_i}, of total listed length T. Origins and ratios may be privately advised, need not lie in the gamma subgroup, and may cause arbitrary cyclic wraparound or repeated terms; ratio1 is allowed. Partition the distinct targets among the covering progressions. Each assigned V_i has |V_i V_i|<=2T_i-1, since all products have form c_i^2 rho_i^u for 0<=u<=2T_i-2. Multiplicative Cauchy--Schwarz and the identical partition inequality (5), followed by (9), yield the SAME bound

 k^2 T >= m^(2-eta)/32.                                    (10)

Thus the retained family simultaneously excludes every such small geometric carrier, including cyclic and out-of-subgroup advised carriers. There is no union over ratios, starts or hidden orders. Both local fields and the global group satisfy it on each retained input. For eta=.04, polylogarithmically many progressions require total length at least m^1.96/polylog(m), and total length O(m) requires at least a constant times m^.48 progressions. These are carrier-cover representation bounds, not operation lower bounds.

For completeness, a more general carrier consequence follows without assuming a progression cover. For ANY finite ambient carrier C containing Z, Cauchy--Schwarz gives E_times(Z)>=J^4/|ZZ|, and ZZ is contained in CC. Hence

 |CC| >= J^4/E_times(Z) >= m^(2-eta)/16.                      (11)

Thus an O(m)-size containing carrier must have a nearly quadratic productset on the retained family. If C is a rank-r multiplicative progression box {c product_(nu=1)^r rho_nu^(s_nu):0<=s_nu<L_nu} of listed size T=product L_nu, then |CC|<=product(2L_nu-1)<=2^r T, even with repeated elements and cyclic relations. Therefore

 2^r T >= m^(2-eta)/16.                                     (12)

This excludes nearlinear listed-size boxes of fixed rank or rank o(log m), including O(log log m) rank. It does not exclude arbitrary polylogarithmic rank, for which 2^r can be too large. More general nonlinear carriers with large productset are not ruled out.

## 5. Exact significance and escapes

The high digit is essential: low square image, fiber bounds and the short offset span alone admit surrogate lifts inside a length-2m integer interval. Equation (1), together with the low quadratic, makes cubic energy rare across high digits and excludes those surrogates on the actual majority supply. The conclusion concerns deduplicated integer offsets, not an explicit output-array lower bound.

This is a substantive obstruction to moving/enlarged carriers using a few O(m)-total-length integer or geometric progressions, even with holes, cyclic wraparound and advice. It is not an arithmetic-operation lower bound. Growing progression counts/length budgets consistent with (6) and (10), nonlinear non-geometric carriers, shared computations not requiring such covers, source-specific cancellation and different factor-selective observables remain outside the theorem. Even an available cover would still require charged handling of its holes and the original product. No improved acquisition bound, new Lean theorem, build or numerical example is claimed.
