# Execute finite Lambert partial fractions on the even pole target

26 October 2026. Primary-source and paper-only arithmetic execution. Scratch only; no tests, numerical campaign, implementation, Lean or repository changes.

**Result.** A finite Lambert partial-fraction identity collapses the clock SUM to a reciprocal finite q-product per row, with exact native poles and all endpoints. Its unrestricted weighted residue can cancel, but the ORIGINAL one-row-per-colour bank has a stronger public partition: O(sqrt K) contiguous colour blocks each have at most ONE good-field hit. Their weighted reciprocal residues therefore require no cofactor normalization or moment-depth search. Section 7 upgrades this to sign-invariant squared-colour-fibre blocks, retaining complete AW pairs. Sections 6–7 give this stronger viable interface; the earlier moment-bank derivation remains a multiset alternative. The initialized completion retains the old soft-K^(5/4) product/derivative bill. No cheaper residue acquisition or new factor bound is proved.

## 1. Native finite input and primary mechanism

Use the frozen [primitive-pair packet](/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-primitive-pair-20261026/README.md), its whole-bin squared tag, and the frozen pure-weighted common-tag theorem. Put rho=q^{-1}, normalize the actual signed interval by T_j=q^M0*y_j, and write

    G(z)=(z;rho)_h, n=h-1, f_n=(rho;rho)_n.

The acquired row multiset has size J=O(K), h=O(K^{3/2})<16H, and all short geometric differences are actual units. Its true good bin has at least one hit; every hit has the SAME canonical squared-colour integer u=[R²]_{n*}, n*=3^ceil(e/2). The public total-row-count guard J<R is retained, including after any paid completion. No separated row-root hypothesis is needed.

Primary finite context: Gu–Prodinger, [Partial fraction decomposition proofs of some q-series identities](https://www.finanz.math.tugraz.at/~prodinger/Guo-Rice.pdf), §2, proof of Theorem 2.1 and equation (2.1), explicitly develops finite rational partial fractions underlying finite Lambert/q-Rice identities. Its infinite |q|<1 notation is not used as a modular evaluation theorem. The particular elementary specialization below is proved directly by its finite pole coefficients. No Appell infinite tail, AW fringe identity or unknown root of unity is imported.

## 2. Exact finite identity, including native deformation

Define the supplied-unit barycentric coefficients

    c_i=(-1)^i rho^{i(i+1)/2} [n choose i]_rho,
    0<=i<=n.

For every 0<=r<=n, finite partial fractions give

    sum_(i=0)^n c_i*rho^{-ri}/(1-z*rho^i)
       = f_n*z^r/G(z).                            (1)

Proof: at z=rho^{-i}, the coefficient of (1-z rho^i)^{-1} on the right is f_n*rho^{-ri}/product_{k!=i}(1-rho^{k-i})=c_i*rho^{-ri}. The rational function is proper for r<=n and these are all its poles. This proof clears to a polynomial identity and uses only the certified differences through h. In particular it remains valid over the actual composite coefficient algebra.

To keep the ORIGINAL additive pole convention, substitute z=T_j/(1+delta) and divide by 1+delta. Equation (1) becomes

    sum_i c_i*rho^{-ri}/(1-T_j*rho^i+delta)
      = f_n*(T_j/(1+delta))^r
          /[(1+delta)G(T_j/(1+delta))].            (2)

All 1+delta inverses are formal unit-start inverses. No constant native collision factor is inverted: (2) is interpreted componentwise as a Laurent rational identity.

At a row hit T_j=rho^{-I}, its delta-residue is c_I*T_j^r; at a nonhit it is zero. The clock guard gives at most one hit per row in EVERY component, so the pole remains simple even with repeated rows. For r=0 the result is NOT the original unweighted residue: it replaces the positive count d by sum_hits c_I. Each c_I is a unit, but an unknown sum of units has no automatic nonvanishing guarantee. The old d<R argument does not transfer to it. No assertion that this cancellation actually occurs on a particular native family is needed or made; its absence would require an additional proved arithmetic lemma.

## 3. A cancellation-safe short moment statistic

Put D0=min(J,h) and use r=0,...,D0-1, which always lies within 0,...,n=h-1, including completed catalogues or bounded native inputs. Define M_r as the sum over j of the delta-residues in (2), and N_r as the same sum with each row weighted by its CANONICAL squared tag w2_j. Then at the good bin

    N_r=u*M_r, for every r.                       (3)

At least one M_r is NONZERO at that good field. To prove it, group the hits by their distinct clock values z_l=rho^{-I_l}, l=1,...,d0, where d0<=min(J,h). Their multiplicities m_l satisfy 1<=m_l<=J<R. Consequently

    M_r=sum_(l=1)^d0 (m_l*c_(I_l))*z_l^r.

Every coefficient m_l*c_(I_l) is nonzero and every pair z_l-z_k is a certified unit. The first d0<=D0 moments therefore cannot all vanish, by the invertible Vandermonde matrix. Repeated rows are counted correctly; no characteristic-zero positivity or unproved row separation is involved. This is a guaranteed finite arithmetic statistic, not a conjectural noncancellation of one weighted Lambert residue.

If the two length-D0 vectors are acquired for all bins, selecting a valid weak pair costs only soft K. For each bin test all M_r by norm gcd. A proper factor terminates; saturated norms can be skipped. A correct-bin nonzero good moment ensures a unit norm or a proper factor occurs. Choose ONE unit-norm moment in that bin. At the correct bin ANY such choice satisfies (3). Its ratio is validated by tau-coordinate gcd and ONE bounded scalar scan, followed by the two-root squared-tag and restricted-HH consumer. A wrong-bin rejected pair may cause that bin to be declined; there is no need to scan n* tags separately for all D0 moments. All vector norm tests cost soft J, and only one scalar scan/menu per bin is charged. All vector output lengths are at most J, even when J>h. Thus the acquisition output and its consumer still fit soft K.

This moment-based selection is linear-algebra prior machinery, not a new general locator theory. Its concrete purpose here is to make the exact finite Lambert weighting admissible for the EVEN common-tag consumer without silently assuming its zeroth weighted count is nonzero.

## 4. Every normalization and baseline acquisition is charged

The scalar f_n is acquired in soft sqrt h by the inherited division-free geometric-product engine, with its unit premise supplied by the short q screen. It is within soft K. Formula (1) gives c_i individually from three finite factorials. Emitting the whole length-h coefficient list costs at least the explicit O(h) stream for this construction; the already audited common q-binomial section operator avoids that emission for single linear actions, but does not automatically evaluate (2) jointly on the J same-root arguments.

There is an exact per-row normalization back to the unweighted count. At a hit T_j=rho^{-I},

    c_I=f_n/[-T_j*G'(T_j)],
    inverse(c_I)=-T_j*G'(T_j)/f_n.                (4)

Thus the needed normalizer is a LONG clock cofactor, not a missing short factorial constant. Acquiring G and G' at every row can be done by the existing shared engine in a constant-rank dual-number algebra, at soft(J+sqrt(Jh)). Alternatively the complete row-value classification already supplies ordinary flags and hence the original unweighted pair at that same cost. Formula (4) therefore does not furnish a cheaper amplitude normalization.

For a fully executed completion of the NEW moment vectors, first acquire all G(T_j),G'(T_j) by that engine. Norm/coordinate classification either factors or makes each G(T_j) globally zero or globally unit. On a zero row, every component is a clock root and -T_j G'(T_j) is a unit by clock distinctness; use (4) to acquire its c_I. Nonhit rows contribute zero. A weighted product tree for sum_j flag_j*c_I/(1-T_j z), and its w2_j-weighted version, then acquires the first D0=min(J,h) moments in soft J, including repeated roots. This does NOT find I, and does not invert G at a collision. The complete moment route still costs soft(K^{5/4}) over all bins. All component classification, original endpoint normalization and once-only terminating decoder contracts are retained.

The transformed right side in (2) is consequently a finite reciprocal-product singular extraction, not an initialized constant-size Lambert value. Its numerator is short for r<J but its denominator still contains every clock factor. Using a continued fraction for that reciprocal rational function would require the actual relevant finite coefficients or a separate initialized recurrence; the partial-fraction identity alone supplies neither.

## 5. Scope and next arithmetic question

The strongest executed finite summation here supplies (1)–(2), with a rigorously cancellation-safe EVEN moment bank (3). It transforms a long sum without analytic limits and isolates its exact missing per-row normalization (4). It does not cancel collision poles or authorize division through them. A direct soft-K acquisition of this particular residue-moment bank would suffice, with the stated validator; none is established here.

The remaining issue is a collective finite singular evaluation of the same-row denominators in (2). Merely acquiring a q-binomial linear action, using a characteristic-zero Lambert reciprocity theorem, or assuming the zeroth weighted residue is nonzero would leave that operation unpaid. This report asserts no general lower bound, no equivalence between every weak readout and a full norm, and no new sixth-rate factoring algorithm.


## 6. Stronger original-bank interface: public colour blocks have one pole

This refinement uses the ORIGINAL deterministic Gauss bank, one row for each unit j in [1,K), separately in every public factor bin. It must NOT be asserted for the completed coefficient-pair catalogue, which can have many rows with the same j. The finite identity (2) applies to either input, but the following combinatorial promise is original-bank only.

Put n*=3^ceil(e/2), B0=ceil(K/n*), and partition the public tags into intervals

    C_b=[b*n*,(b+1)*n*) intersect [1,K), 0<=b<B0.

In the correct good bin every hit has j=R modulo n*. Each such interval contains at most one integer with that residue, and there is exactly one acquired row for that j. The all-component clock screen gives at most one hit per row. Hence EACH colour block has at most ONE good-field leaf hit, irrespective of its content or whether it is an axis. At least one block hits by the inherited complete cover.

For each block request ONLY the pair of simple residues

    V_b=Res_delta sum_(j in C_b) f_n/
           [(1+delta)G(T_j/(1+delta))],
    U_b=the same residue with canonical multiplier w2_j.

At a good hit (2) gives exactly (V_b,U_b)=(c_I,c_I*u), where c_I is a certified unit and u=[R²]_{n*}. A no-hit block has (0,0) at that field. Thus the clock-cofactor normalization (4) is NOT required for this output, and neither a J-moment bank nor an unknown leading precision is needed. Primitive original subbanks and original axis subbanks likewise have at most one good hit in total (full K tags there), but the block partition covers ALL contents uniformly and needs no primitive-witness promise.

The consumer is completely paid. Test all B0=O(sqrt K) V_b norms: a proper gcd factors, a saturated norm is declined, and a unit norm is a legal inverse. Choose the FIRST unit-norm block in each bin and apply the established coordinate/scalar validator once. At a correct bin every such chosen block necessarily hits, because a no-hit block has V_b=0 at its good field and hence cannot have unit norm. Its ratio is therefore the correct u. If a hitting block has a nonunit norm, the norm gcd is proper because its good value is nonzero; it cannot be lost to a saturated-norm decline. Correct-bin success follows, while a wrong bin can be declined after one bounded failed attempt. The squared-tag two-root Hensel and HH palette costs remain soft K over all bins. No scan of n* tags for every block is required.

### Execute the acquisition options, not merely the decoder

The block roots T_j are actual acquired Gauss outputs at consecutive colour indices. They are not thereby a geometric progression: the shortest coefficient vector and its canonical conic phase vary with j. Consequently finite partial fractions in CLOCK index i do not give an independent summation theorem in block index j.

A fully initialized exact Lambert block-pair completion is to acquire every G(T_j),G'(T_j) jointly as in §4, classify flags, obtain c_I on flagged rows from (4), then sum by public block and tag. It costs the old soft(K+sqrt(Kh))=soft K^(5/4), with O(K) input and only O(sqrt K) final pairs. Output admissibility did not need the normalization, but this particular baseline uses it to evaluate the precise Lambert residues without locating I.

Calling the existing query independently on each block instead gives

    soft sum_b [J_b+sqrt(J_b*h)]
      =soft(K+(K/n*)sqrt(n* h)),

where J_b<=n*. At n*~K^(1/2), h~K^(3/2), this is K^(3/2), worse than the joint engine. A direct constant-rank first jet for each block is equally legal under the unique-good-hit promise, but has the same repeated-call bill. No direct-product algebra containing B0 blocks is treated as constant rank.

The strongest fresh handoff from this finite Lambert test is therefore the above O(sqrt K) SINGLE-POLE block trace. Any unit-amplitude acquisition satisfying those pairs is sufficient; it need not reproduce the unweighted count or all row values. Its formula retains every native clock endpoint, canonical even weight and componentwise Laurent pole. A collective sum identity evaluating those specific block traces in total soft K would finish the consumer. The executed finite partial fraction identity has not yet acquired it.

## 7. Preferred sign-invariant partition: keep the AW pairs intact

There is a better partition for this EVEN interface, preserving the native +/- phase pairs. This refines the contiguous blocks of §6, without changing their cost or single-pole proof. Again it uses only the ORIGINAL one-row-per-colour bank.

Pair each unit colour j with K-j and use the representative j<K/2. The deterministic Gauss inputs for those two colours are identical, so the coefficient pair is the same and the centered phases are opposite. In each pair the canonical squared tag is

    u=[j²]_(n*).

For every unit-square u modulo n*, there are exactly K/n* colours above its two roots and hence exactly

    L=K/(2n*)=3^floor(e/2)

unordered +/- pairs. Acquire these fibres by public integer squaring and sorting; order each fibre deterministically. For ell=0,...,L-1, form block ell from the ell-th pair in EACH square fibre. There are n*/3 fibres, so each block has n*/3 pairs, and the entire original row list is retained exactly. All setup is soft K and requires no native-field square roots or row-root separation.

Every correct-bin hit has the same u*=[R²]_{n*}. Each block contains exactly one pair with u*, and the other pairs cannot hit there. The two colours of that pair cannot BOTH hit: that would require R=-R modulo n*, contradicting that 2R is a unit. The clock guard also prevents two hits in either row. Thus each sign-invariant block has at most ONE good hit, and some block has one. This includes nonprimitive contents and axes through the full original common-tag theorem.

The Lambert residue pair per block is unchanged, except its sum is over this sign-invariant subset. Its per-clock coefficient c_i is independent of the sign member and the mark u is identical, so the observable respects the paired AW symmetry. For a pair with normalized roots c*x,c/x, define G_+=G(c*x/(1+delta)), G_-=G(c/x/(1+delta)). Its unweighted rational summand is exactly

    f_n/(1+delta) * (G_++G_-)/(G_+*G_-).         (8)

The tagged summand is its canonical integer u multiple. Equation (8) is symmetric, finite, and keeps the entire original clock. At the sole good hit one denominator has a simple zero and the other is a unit; the residue is precisely the nonzero c_I. No odd sign selector or row cofactor normalization is required. Formula (8) does not itself evaluate the paired bulk; it is the actual finite symmetric input for a further contraction.

The same norm scan/one-selected-block-per-bin validator and constant-menu squared-tag HH consumer apply. Its L=O(sqrt K) output pairs are thus a complete uniform weak target. Separate block backend calls still cost K^(3/2), while the all-row product/derivative baseline gives the exact pairs at K^(5/4). The public sign-invariant partition reduces cancellation/normalization requirements, not that already paid acquisition bill.

**Final handoff:** the preferred target is the O(sqrt K) symmetric SINGLE-POLE block traces (8), with their canonical squared tags. This is compatible with finite AW or Lambert manipulations and has guaranteed nonzero good amplitudes without unknown Hasse precision. Their total-soft-K acquisition remains open.
