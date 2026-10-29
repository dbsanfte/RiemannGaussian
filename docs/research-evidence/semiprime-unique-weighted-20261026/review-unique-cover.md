# Independent proof review: a globally unique short-clock weighted cover

26 October 2026. Paper-only audit of root's eligible-domain selection, synchronized with the completed-ellipse/compiler contracts. No repository edits or tests. **PASS.** The selected actual rows have hypothetical root supports partitioning every unit colour modulo K. Consequently a correct bin has EXACTLY ONE good-field row-clock hit, with the original short h=O(K^(3/2)). This is a coverage/uniqueness theorem and paid input selection; it is NOT a faster query acquisition theorem.

## 1. Orient integer directions; no phase-nesting premise

For every nonaxis completed coefficient pair write (a,b)=d*(a0,b0), with gcd(|a0|,|b0|)=1. Orient a0>0 and d>0, identifying opposite signs. The full ellipse contains the positive-oriented actual pair whenever it contains its negative. Opposite phases obey ell_-=-ell_+ modulo H, so their hypothetical zero supports coincide. The selected actual positive row keeps its own canonical phase and physical clock metadata. No equality of scalar products or dropped q-carry is required. All selected rows retain the ellipse margin, so the symmetric original clock still covers every physical index.

For any admitted direction a0,b0 are both 3-units: an admitted pair has equal 3-valuations in a,b below e, because |ab|<=K/sqrt3 excludes a,b both divisible by 3^e. Removing their integer gcd leaves zero 3-valuation in both cores. The cores are either both odd or mixed in parity. In the mixed case every admitted multiplier d is even; in the both-odd case either parity of d is allowed.

Define the public eligible domain of an actual pair v=d*(a0,b0) by

 E_v={unit r modulo K: a*r²=b*N modulo K}.

On odd r its modulus-2 condition is automatic for every admitted pair. At the 3-part, t=v3(d)<e and

 E_v={unit r: r²=N*b0/a0 modulo 3^(e-t)}.            (1)

Thus along a direction these domains are nested as t increases. Unit multiplier factors and extra 2-powers do not alter the domain. This proves exactly the nesting used below; there is NO need to assert general nesting of canonical PHASE classes at different multipliers.

## 2. One maximal ramified pair covers its entire direction

For each oriented direction present in the actual completed table choose ANY actual coefficient pair v_max with maximal t=v3(gcd(a,K)). All pairs of that direction have E_v subset E_vmax by (1).

For fixed v_max, complete colour enumeration is already paid. Group its actual rows by the centered canonical phase ell. The incidence compiler proves each such equal-phase class is exactly the hypothetical root support of each row in that class, and those classes partition E_vmax. Select one ACTUAL row per phase class. This covers the direction's entire eligible domain without retaining duplicate supports or computing an unknown factor colour.

Only perform this step on directions whose maximal t>=1. If two different such directions had a common eligible colour r, their maximal coefficient vectors would both be divisible by 3 and belong to Lambda_r. Dividing by 3 shows their determinant is a multiple of 3K. The same ellipse area bound gives absolute determinant <=2K/sqrt3<2K, a contradiction unless they are parallel. They are different oriented integer directions, so parallelism is excluded. Hence their WHOLE eligible domains, not merely ambiguous phase classes, are disjoint.

The argument remains valid when some maximal phase classes happen to be singletons. They are selected as part of the ramified direction; the rule does not classify directions by phase-class SIZE.

## 3. Fill the complement with singleton rows

Mark the union of the selected ramified domains using the already enumerated compatible colours. Consider an unmarked unit colour r. The complete ellipse contains the original Gauss witness at its own colour r. If that witness is nonaxis and has v3(g)>=1, its direction's maximal domain would contain r, contradicting unmarkedness. Therefore it is a nonaxis g=1 or g=2 row, or a filtered primitive axis.

Each such row has root support exactly {r} modulo K. For g=1 this follows immediately from the compiler. For g=2, r'-r is a multiple of K/2=3^e and is even because both colours are odd, hence a multiple of K. Axis supports are {r} by their separate explicit proof; larger axis multiples were never admitted.

Select ONE such actual row for each unmarked r. Existence is proved by the Gauss witness, but implementation need not recompute it: scan the completed g=1/g=2/axis rows and retain the first actual colour-r representative. Positive orientation is available by the symmetry of the completed ellipse. Do not choose singleton rows on colours already marked by a ramified domain.

All selected supports are now nonempty, pairwise disjoint and cover every unit r modulo K. In particular

 J_selected<=phi(K)=K/3.

This bound is on actual selected rows, not a fractional or virtual representation.

## 4. Exact good-field uniqueness, tags and startup cost

In a correct bin the existing exact-integer/clock proof says a selected row hits iff the factor colour R modulo K lies in its hypothetical root support. The support partition therefore gives exactly ONE hitting row. The local q order and h<16H give at most one clock hit within it. Every unit hypothetical colour, including the actual smaller OR larger nonsplit factor, is covered. Axes and higher contents have not been discarded.

The selected row's squared tag is [R²]_n because its support lies in r=j modulo K/g and n divides K/g. Negative orientations require no decoder change: the kept actual row independently obeys the same signed clock bound. Wrong bins do not inherit this uniqueness promise and remain bounded separate attempts.

All operations use the previously acquired full ellipse table: integer direction keys via gcd, maximum 3-valuations, sorting canonical phase classes, marking eligible colours, and filling singleton fallbacks. Total row and eligible-colour data are O(K) (up to integer-arithmetic logarithms). No K-by-K scan, unknown order, unknown R, or root-of-unity projection is used. Numeric selected roots are a subset of already acquired native roots; the original supplied q and endpoints remain valid. Thus total selection and initialization cost soft K.

## 5. New acquisition freedom, with the output distinction retained

This makes the WHOLE selected bin a singleton target. For any supplied UNIT clock/row amplitudes, the two residue sums (unmarked, squared-tag marked) have good values (A,A*[R²]_n), A nonzero. They no longer need an O(sqrt K) block palette or an unknown count/cofactor normalization. A finite Lambert source is therefore admissible on the entire selected bank: its c_I amplitude is a unit. Norm of the unmarked residue gives a proper factor or a genuine inverse at the good attempt. Its ratio supplies the correct coarse square tag to the existing validator and HH consumer.

This arbitrary-amplitude statement is a TWO-scalar projective interface. A single marked arbitrary-amplitude residue A*u is not automatically a small integer or covered by the M1 divisor decoder. With constant clock amplitudes, the selected M1 itself has good value u (count exactly one), which is indeed the smaller integer target. These interfaces must not be silently identified.

The current division-free row engine still acquires all products/residues in soft(K+sqrt(Kh))=soft K^(5/4). The selection theorem does not initialize a faster full-bin Lambert functional, selected subresultant, cofactor ratio or determinant. It opens those unique-hit interfaces at the SHORT weighted clock, without an acquisition exponent claim.

## 6. Limited prior-credit check

A targeted read/search of frozen evidence found earlier conditional unique-hit minus/monic families, the uniform two-monic good-family construction with clock 2H+1, and original-bank per-block singleton theorems. Those retain their credit. This argument instead selects actual rows from the complete weighted ellipse to give one whole-bin hit at h=O(K^(3/2)). The search is not a literature-wide novelty claim. No general within-direction phase nesting or cross-pair normalization theorem is asserted beyond the exact eligible-domain facts proved above.

Final disposition: the simplified eligible-domain proof is complete, including mixed singleton classes inside ramified directions, 2-adic content, sign orientation, primitive axes, every-unit coverage and paid metadata. No substantive gap found.

## Final source read

Read the stable unique-cover.md §§1–6 after the independent derivation above. Its simplified proof agrees with the reviewed eligible-domain argument, including high directions whose maximal classes are singletons, 2-adic parity, original own-row fallback, actual opposite-sign phases and short physical clocks. The whole-bin arbitrary-amplitude TWO-scalar interface and constant-clock one-moment interface are correctly distinguished. Final transcription disposition: PASS; no correction requested.
