# Executed multi-shift pole jumps with exact finite boundary

26 October 2026. Scratch paper execution. **Result:** a pole can be moved by an arbitrary paid jump d without retaining Jd denominator coefficients: its new numerator has degree<J and is initialized by modular arithmetic. A short jump, and even d=O(K^(4/3)) via the shared backend, fits soft K. For a unique native weak pair its common transport amplitude can also be dropped after the prefix gate. However the gate is exactly the original prefix product, and fused jumps retain its cumulative length. The complete initialized hierarchy gives the retained soft(J+sqrt(Jh)) cost, not the desired separated bound. No general lower bound or universal failure of multi-denominator transport is asserted.

## 1. Actual source and finite functional

Use the retuned beta-coupled unique bank, degree-J acquired F, actual q-clock i=0,...,h-1, J=O(K^(2/3)), h=O(K²), original-K preparation. Put D_delta(X)=F(X)+delta and acquire the two numerators p_0=F', p_1=H_w, with

H_w(X)=sum_j w_j prod_(k!=j)(X-T_k), w_j=j.

Product trees acquire these in soft J without row separation. For the fast interpolation implementation of the transport below, ALSO run the licensed actual D' gate: nonunit row aliases localize and factor, or continuing rows become globally unit-separated. This costs soft J algebra plus the once-only original soft-K extractor on a terminating branch; it is not inferred from uniqueness. At the good hit theta=q^I, p_1(theta)=w_hit p_0(theta), and p_0(theta)!=0.

Use the full-clock barycentric functional from frozen geometric-contraction/selected-condensation §7:

L[f]=sum_(i<h) omega_i f(q^i), omega_i=(q^i)^(h-1)/W'(q^i).

Every omega_i is a unit, but an h-entry array is not supplied. A requested omega_0=1/(q;q)_(h-1) costs soft sqrt(h) by the scalar factorial backend, and successive requested initial weights use

omega_i/omega_(i-1)=(q^h-q^i)/(1-q^i).

Thus any initial d weights cost soft(sqrt(h)+d), not h. The two residues L[p_a/D_delta] have common nonzero amplitude omega_I F'(theta), so their weak ratio is the actual row mark. We use componentwise Laurent coefficients, not numerical inversion of D_delta at a collision.

## 2. A real multiple-shift transport, with its boundary

For 0<=d<=h put

A_d(X)=prod_(s=1)^d(q^h-q^s X),
B_d(X)=prod_(s=1)^d(1-q^s X), K_d=A_d/B_d.

The exact finite identity for our rational source is

L[f]=sum_(i=0)^(d-1) omega_i f(q^i)
          +L[K_d(X) f(q^d X)].                       (1)

Indeed omega_i K_d(q^i)=omega_(i+d) for i+d<h; if i+d>=h, a numerator factor vanishes. Denominator factors are all screened gaps with exponents i+s between1 and h+d-1, so NONE is inverted at a native collision. The zero numerator at the last d nodes kills the overhang as a rational identity in delta before taking residues. This avoids the invalid step of applying Pearson to a function singular at its endpoint coefficient.

For a good hit I>=d, (1) transfers it to I-d with EXACT residue amplitude omega_I p_a(theta). If I<d, its residue is in the displayed prefix, not silently lost. The two-source ratio is preserved. All statements hold at finite q-order because these are literal finite sums; the required actual gap range, including doubled original exponents for the retuned parity base, is checked rather than assuming an infinite q-orbit. Explicitly, let h_raw be the retuned unthinned window. The conservative scale gives h_raw<=sqrt(2)H/4+9 and the common padded parity clock has 2h<=h_raw+3. For d<=h its largest ORIGINAL screened exponent is at most 2(h+d-1)<=2h_raw+4<=sqrt(2)H/2+22<16H for K>=54. The rooted base is certified by m²-powering to the original prepared base, so this is the actual doubled footprint, not a hypothetical unit order.

A primary algorithmic context is Du–Huang–Li, *A q-Analogue of the Modified Abramov–Petkovsek Reduction*, author PDF https://cs.uwaterloo.ca/~h2huang/Papers/DHL2018.pdf , §2 Lemma1 and Corollary1 (forward/backward congruences). Its hypotheses are a characteristic-zero field and q not a root of unity; its reduction algorithm is NOT imported at native finite order. Formula (1), its endpoint term and composite-ring guards are proved directly above. Its shift-congruence viewpoint motivates this specific multi-shift test, rather than providing an uncharged evaluator.

## 3. Acquire a degree-J transferred numerator

First actually screen F(q^i), 0<=i<d. Direct monic MPE costs soft(J+d). A nonunit localizes to an ORIGINAL row/index and factors via the licensed mixed-label consumer, with once-only original soft-K extraction separately charged. On continuation all these values are global units; therefore the prefix term in (1) is regular in delta and has zero selected residue.

Let D_d(X)=F(q^dX)+delta, monic-normalized by its known leading q^(dJ). B_d and D_d have unit resultant on this branch: B_d's roots q^-s map to original indices d-s. Explicitly,

Res_X(q^(-dJ)D_d(X),B_d(X))
 =q^(-Jd(d-1)/2) prod_(i=0)^(d-1)(F(q^i)+delta).   (2)

Thus the inverse of B_d modulo D_d is lawful after that gate. Acquire A_d,B_d coefficient lists in soft d for a short jump. The fast safe implementation is the actual separated-row interpolation in §4, NOT an assumption that a final unit resultant makes every intermediate Euclidean pivot a unit. No additive pivot is assigned a mixed-label decoder.

The forced short numerator is

P_(d,a)(X)=A_d(X) p_a(q^dX) B_d(X)^-1 mod D_d(X), deg<J. (3)

The difference between K_d p_a(q^dX)/D_d and P_(d,a)/D_d has denominator only B_d. It has no delta pole on the clock because B_d is a global unit there. Consequently, on the prefix-unit branch,

Res_delta L[p_a/D_delta]=Res_delta L[P_(d,a)/D_d].   (4)

This is actual pole TRANSPORT, not attempted elimination. It moves the denominator to F(q^dX)+delta and preserves the marked amplitude. It never expands the product of Jd shifted row factors. The original same-denominator Pearson obstruction does not apply to (4).

## 4. Ring-safe numerical interpolation alternative and long-jump cost

After the mandatory globally unit-separated row gate, evaluate A_d,B_d at the supplied nodes q^-d T_j, invert B_d ONLY after the prefix product gate, and interpolate values K_d(q^-d T_j) p_a(T_j). This acquires P_(d,a) at delta=0 in soft(J+d). That constant numerator is sufficient for the selected residue: D_d is linear in delta and P_(d,a) is analytic, so only its delta^0 coefficient contributes at every zero node. If fixed higher delta jets are wanted, Hensel/Newton lifts of the roots of F+delta start at the supplied T_j with certified derivative units, and the same MPE/interpolation computes them at fixed-rank cost. This supplies a safe fast realization of (3), not an assumption about Euclidean pivots.

For larger d, the same A_d,B_d node values are two finite geometric products. The already acquired shared geometric engine computes ALL row values and fixed jets in soft(J+sqrt(Jd)), including the prefix B_d gate and its actual localization branch. Interpolation costs soft J. This is a complete costed alternative, not a new theorem. At J<=K^(2/3), d=O(K^(4/3)) it is soft K. At d~h~K² its worst-case bound is K^(4/3), so a single nearly-full jump has not become cheap.

The explicit coefficient list A_d,B_d costs d and should NOT be charged to this latter faster numerical variant. Conversely the numerical variant must acquire actual row separation and the prefix-unit branch before interpolating/inverting; it is not free coefficient access from a product descriptor.

## 5. Dropping K_d for the native UNIQUE weak pair

There is a useful stronger simplification for this output. After the prefix-unit branch, shift all actual row roots to q^-d T_j. Their good hit has index I-d. Rebuild any physical weak row-mark pair on the shifted family; the arbitrary new nonzero per-hit amplitude is acceptable. K_d, P_d and even the barycentric amplitude normalization can be omitted for this changed sufficient output. This is not numerical equality with (4).

If the clock is shortened to 0,...,h-d-1, this is EXACTLY the original suffix, preserving its unique good hit with no overhang claim at all. If instead the original h-clock is kept to maintain a common interface, its added original positions h,...,h+d-1 have no good hit. This last statement uses NATIVE provenance, not generic F: the original true physical index is in |i|<M0. In the rooted parity bank q=(pi^H')², extending the index by d<=h changes the original integer relation exponent by at most2dH'. The previously proved original exponent bound <16H² increases by at most32H² since h<16H and H'<=H. It stays <48H²<256H², below the good pi order. Hence a new numerical alias cannot create an overhang hit, and the integer true-index bound excludes an actual one. The actual doubled short-gap footprint also has slack under the conservative m³<=K/1024 preparation. Wrong bins/other components may have extra hits; the weak denominator norm/coordinate gates and bounded rejection remain necessary.

Thus the native overhang theorem legitimately allows a common-h shifted weak target. It does NOT identify which shift lands the unknown I near a paid endpoint. Prefix regularity remains required. Without it, a hit with I<d disappears from the suffix and the shifted family is not a complete cover.

## 6. Execute the hierarchy and locate its exact cost

For a FIXED functional L_h the transport coefficients have the exact cocycle closure

K_(a+b)(X)=K_a(X) K_b(q^a X).

There is NO fixed-quotient scaling obstruction for the already acquired numerator. Indeed D_d(q^e X)=D_(d+e)(X), so P(X)->P(q^e X) is a well-defined isomorphism between the corresponding moving quotient algebras (with the known leading normalization). Its coefficient scaling costs soft J. For doubling, P_d(q^dX) already supplies K_d(q^dX)p(q^(2d)X) modulo D_(2d). What is missing is the OTHER factor K_d(X) modulo that NEW D_(2d). The known K_d residue modulo D_d does not supply it: scaling that residue changes its argument to q^dX. Its new denominator values test original indices d,...,2d-1, whereas the old denominator gate tested0,...,d-1.

Therefore composing jumps can keep a short numerator, and shifting that numerator is paid. Acquisition/reuse of the new K factor and its new actual strip gate is the precise issue; no moving-modulus quotient carry is asserted. If the clock is shortened, rebuild its functional/weights and use the weak-amplitude rebasing of §5 rather than applying the fixed-h numerical cocycle unchanged. The cumulative denominator's resultant (2) is still the cumulative original PREFIX product. It is not a product of already known unit constants unless all intervening prefix strips were actually gated.

A direct sequence of d~sqrt(h) strip gates/rebases costs soft(h+Jh/d) in algebra, already above the separated target at h~K². Fusing the strip descriptors into one jump s permits the shared engine cost soft(J+sqrt(Js)); it returns exactly the familiar prefix query, not a faster independent initialization. This accounting is a statement about THESE two implementations, not a lower bound for pole transport.

A complete adaptive algorithm is: test the first half prefix by that shared engine; nonunit localizes and factors, while a global-unit branch rebases to the remaining suffix and halves its horizon. Repeat until the window length is O(K), when explicit clock acquisition/MPE and actual localization cost soft K. The costs sum geometrically to soft(J+sqrt(Jh)), with logarithmic setup factors. The same controller can first test a prefix of length K^(4/3) at soft K; this is a real conditional cheap branch but no all-semiprime theorem places the hit in it. A publicly chosen shift menu with final short windows is merely another proposed coverage family and must prove it covers the actual native indices; no such theorem is inferred from the exact transport law.

## 7. Precise remaining target and prior credit

The multiple-shift construction succeeds algebraically: finite boundary, degree-J numerator, exact common pole amplitude, native weak-amplitude drop, and short-jump initialization are all explicit. The first unpaid operation for a long leap is the PREFIX unit predicate or the equivalent A_d/B_d values modulo the row polynomial, with the same original leaf recovery. A new method could compute only the selected transferred pair while bypassing that full prefix gate; nothing here rules it out. Such a method must also handle the case I<d rather than silently discarding its boundary residue.

Prior credit retained: geometric-contraction/selected-condensation §7 supplies the full-clock Pearson functional and same-denominator forced numerator; residue-shortcuts/deformed-telescoping supplies finite residue orbit transport and admissible-boundary cautions; scalar-acceleration/pole-kernel-handoff supplies the selected pole kernel; separated-selector supplies the unique weak row-index consumer. This note tests a genuinely different multi-shift jump with degree-J reduction and exact gate/resultant formula. It does not count a descriptor, a generic q-Gosper theorem or the old prefix evaluator as a new sixth-rate algorithm.
