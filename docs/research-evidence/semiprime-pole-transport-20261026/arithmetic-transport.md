# Execute arithmetic phase transport on a compatible weighted cover

26 October 2026. Scratch-only finite construction. Read direct-contraction/ternary-fusion, fused-readout/quadratic-lifts, residue-shortcuts/content-cover and the retuned unique-support contract. **Outcome:** an actual smaller-conductor Gauss cover can be compiled into full quadratic-phase fibres, with all carries and axes, then into O(log g) GP strings per parent. This is a lawful combination of existing arithmetic inputs and chirp contraction, not a new exponent improvement. Its paid product/localization cost grows as soft(K^(5/4) g^(1/4)); it does NOT inherit the retuned selected ellipse's singleton output. The exact first unpaid improvement is a shared norm of the compiled parent strings, rather than a missing root table.

## 1. Why the old monic triples cannot simply replace selected weighted rows

The old formulas y_r=p U_j^r q0^(c_r) concern the two monic catalogues (a,1) or (1,c), with coefficient changes by delta=K/3. Their full three-child table and bounded carries are already paid and credited. A selected weighted ellipse contains arbitrary coefficient pairs and need not retain all three corresponding monic rows. In a balanced weighted ellipse its semiaxes are O(sqrt K), while delta is Theta(K). For sufficiently large K, two admitted coefficients differing by delta cannot both lie in the same coordinate range. A primitive eligible pair has unit derivative 2aj modulo3, hence exactly one of the three lifts of a stationary parent colour satisfies its child congruence. Thus a complete old coefficient-digit triple is not automatically present in this primitive weighted bank. This is an actual scoped compatibility check, not an exclusion of a different fusion family.

The following rebuild supplies a genuinely covered family rather than pretending those missing children were selected.

## 2. A complete weighted hierarchy with fixed coefficients

Choose g=3^t, g² dividing K/2, and delta=K/g. Use the already prepared ORIGINAL groups and conductor K; do not assume N<=delta^6. At conductor delta, acquire one deterministic weighted Gauss row v_j=(a_j,c_j) for each unit parent colour j modulo delta, in the parity lattice if desired. Its canonical stationary phase is acquired. Its weighted norm is O(sqrt(delta N)). All parent reductions and row labels cost soft K.

For each parent retain the FIXED child coefficients

    a=g*a_j, c=g*c_j,

and complete to every child colour j_s=j+s*delta, 0<=s<g. These are all odd units since delta is even. Parent stationarity modulo delta implies a*j_s²=cN modulo K for every s. Therefore canonical child phases exist. This gives O(K) actual integer row labels, including those arising from parent axes. It retains a witness for every actual factor colour, by using that colour's own parent Gauss row; no uniqueness is asserted.

Let v be the inverse of j modulo H, and write the EXACT integer

    kappa=(c_j*N*v²-a_j)/delta.

It is integral by parent stationarity. Expanding the inverse of j+s*delta modulo H and multiplying the phase by g gives the exact congruence

    ell_s-ell_0=(H/g)*Q(s) mod H,
    Q(s)=kappa*s-c_j*N*v³*s² mod g.                  (1)

The cubic and higher inverse terms vanish: g*delta³/H=delta/g is an integer, since g²|K. Thus (1) does not require c_j to be a 3-unit and does not discard higher-content or axis parents. There is no unknown factor in its coefficients. The associated global roots obey

    y_s=y_0*qhat^(e_s)*q^(k_s),
    qhat=pi^(H/g), q=qhat^g,
    e_s=Q(s) in [0,g), k_s in {-1,0}.              (2)

The last bound uses centered original phases and FINAL canonical e_s directly. No centered-to-canonical secondary carry is lost. The barpi exponent a+cN is fixed on the fibre. Every numeric root/start and carry is acquired with O(log N)-bit exponents in soft K.

## 3. Group the actual quadratic images, including degeneracies

The image multiset of Q(s) modulo g has a complete short AP compiler. First separate any constant offset, and divide both linear and quadratic coefficients by their largest common 3-power. If both vanish modulo g, it is one phase with multiplicity g. Otherwise:

* quadratic coefficient a 3-unit: complete the square, and apply the already proved square-valuation strata. Each nonzero square stratum is a canonical AP; multiplicity is 2*3^r, and the zero-square multiplicity is 3^floor(t/2), at the reduced precision.
* quadratic coefficient divisible by3 and linear coefficient a unit: derivative is a unit everywhere, so the map is a bijection modulo the reduced 3-power by elementary Hensel lifting. Its image is the entire AP, with the multiplicity from the divided common power.

This takes O(log g) AP descriptions per parent, or O(g) direct arithmetic if one chooses to validate the full already-paid child table. It needs no auxiliary root of unity, Gauss-sum evaluation or finite-field square-root oracle. Degenerate axes are included: their quadratic coefficient is zero and they enter the linear/constant cases.

After unit multiplication and translation from completing the square, represent each full residue coset with its final canonical start e0 in [0,D) and length g/D. It is then one AP without wrap. If an unreduced translated integer start is retained instead, split its wrap explicitly into at most two parts. This normalization is needed for the finite concatenation below.

Before using (2) without the individual q carries, perform the four normalized endpoint gates from quadratic-lifts, with the ACTUAL enlarged window and signed labels. Proper gcds factor; global saturated labelled leaves use the original mixed decoder. On continuation the removed/added endpoint factors are certified global units. If these gates terminate, charge the once-only original soft-K extractor. Original unit-gap/order margins are checked for the actual physical window; no all-precision promise is inferred from a GP descriptor.

For a canonical AP e=e0+Dv, 0<=v<L, with DL=g, its qhat-phase product followed by the q-clock is exactly a consecutive qhat^D product of length Lh, up to its explicit start. Indeed v-Li runs through a full consecutive integer interval for 0<=v<L,0<=i<h. This is a finite multiset identity, not a cyclic norm at an auxiliary root. Known positive multiplicities do not change product nonunit predicates. The zero stratum is a singleton q-string.

If the long qhat^D interval wraps a local group order, one must NOT infer a 0/1 residue count from a string zero. The safe consumer here is only product/nonunit with actual leaf localization. The inverse integer map v-Li identifies the underlying AP phase and physical clock index, hence a short actual mixed label. All parent axes and added phases retain that label provenance.

## 4. Horizon, coverage and full acquisition cost

Scaling a parent Gauss vector by g gives weighted norm O(sqrt(gKN)). The same explicit Cauchy–Schwarz and centered-phase argument as the parity audit gives an actual full signed horizon

    h_g=O(sqrt(g)*sqrt(N)/K^(3/2))
       =O(sqrt(g)*K^(3/2)) at N<=K^6.              (3)

An explicit original-conductor choice is D_g=ceil(sqrt(2gKN)), M_g=ceil(4D_g/H)+2 and h_g=2M_g+1. The same parity-audit calculation gives

    h_g<=8sqrt(2g)K^(3/2)+9<16H,
    |actual local alias label|<12sqrt(g)K^(7/2)+4H+8<16H²,

for K>=54 and g²|K/2. Indeed sqrt(g)<K^(1/4), so even the looser bounds 8sqrt(2)K^(7/4)+9<16K² and 12K^(15/4)+4K²+8<16K⁴ hold throughout this range. These explicit margins force every good-bin numerical hit to its actual integer stationary index using ord(pi)>256H². For the four endpoint gates or padding extend the displayed alias bound by at most H; the same strict <16H² margin still holds for K>=54. A unit-padding implementation still performs its actual endpoint gates. For a RETUNED conductor K' with original N/order preparation, replace the geometric horizon by O(sqrt(g)*sqrt(N)/(K')^(3/2)); do not use N<=(K')^6. The literal ternary g=3 step fits the conservative retuned margin. Arbitrary other fixed or growing g must check the actual bound h_g<=(sqrt(2g)/4)H+9 (and its padded/doubled-gap footprint) against ORIGINAL preparation; constant g alone is not that certificate. No uniform largest-g retuned claim is inferred here.

There are O(K/g) parent rows, O(log g) canonical phase strata per row, and O(K) complete child labels. The inherited division-free common-GP backend acquires all products needed for a nonunit predicate and row/string localization. At the coarsest stratum scale the bound is

    soft(K+sqrt((K/g)*(g*h_g)))
      =soft(K+sqrt(K*h_g))
      =soft(K^(5/4)*g^(1/4)).                      (4)

The finer square strata form the same convergent geometric cost sum as in the old chirp-collapse report. This is a charged bound for this particular initialized backend, not a lower bound. No inverse 1-qhat^n beyond the physical gap contract is used: the GP product/MPE engine is division-free at unknown-order bases.

A nonunit product is localized to a parent/AP/clock leaf by the inherited hereditary subqueries. All integer labels remain short and nontrivial: a+cN cannot vanish for a nonzero axis; for nonaxis rows the coefficient bound is O(gK), far below N in the prepared branch, so c!=0 dominates a. This coefficient bound is uniform across bins: the parent parity Hermite bound and the inequality 2|a_j c_j|B^2 N <= a_j^2 B^4+c_j^2 N^2 give |a_j c_j| <= 2 delta/sqrt(3). Scaling gives |ac| <= 2gK/sqrt(3), which bounds either nonzero integer coefficient individually. Shortest axes scale to coefficients of magnitude 2K. Thus the complete mixed-relation decoder applies even when the scalar beta label vanishes. One cannot decode an unlocalized aggregate as one annihilator.

The larger ellipse has weighted area O(gK), so the old <3K high-direction disjointness proof does not transfer for growing g. Multiple parent supports can overlap, and a full-bin singleton/row-tag ratio is not promised. In particular this rebuild cannot simply consume the retuned unique bank's weaker first-jet interface. The safe product/localization consumer above is fully covered, whereas an optimized unique partition would require a new support theorem.

## 5. What this execution settles

Grouping bounded monic carries alone did not make those monic triples members of the weighted selected bank. The compatible construction above instead completes real stationary coefficient fibres, compiles their possible degenerate quadratic phases and pays their exact finite norm starts. It combines already credited conductor retuning, quadratic-lift completion and chirp/GP concatenation. The obtained rate (4) does not beat the original bank, so it is not claimed as goal progress.

The first missing contraction is now the product/nonunit functional of the acquired O(K/g) parent phase-stratum strings of lengths up to g*h_g, with their common base hierarchy and known multiplicities. Its starts and carries are supplied, its finite endpoints are gated, and original recovery is licensed. A new shared contraction of those strings could be useful; an A2 trace, a cubic determinant, or an auxiliary-root cyclic identity alone does not acquire it. No broad survey or general impossibility claim is substituted for that explicit acquisition boundary.
