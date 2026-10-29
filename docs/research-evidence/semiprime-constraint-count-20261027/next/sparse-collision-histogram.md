# Sparse collision grouping of actual occurrence lists

FINAL research supplement, scratch only. No canonical source or sealed-packet origin was edited. SparseCollisionHistogram.lean strictly compiles with autoImplicit=false/warningAsError=true. All15 namespace linters and every generated declaration standard-axiom audit PASS:23 declarations/20 theorems. These counts are supplemental and are not part of the parent's canonical-module totals.

## Literal duplicate-list bridge

For ANY actual list xs and label map into a decidable-equality type, let m(k)=countP(label=k,xs), and derive K=(xs.map label).toFinset from that very list. pair_grouping proves exactly

    sum_(i occurrence in xs) sum_(j occurrence in xs) [label(i)=label(j)]
      = sum_(k in K) m(k)^2.

No Nodup xs, Fintype label alphabet, bucket coverage, histogram answer or label injectivity is assumed. Diagonal pairs and repeated equal port occurrences are all retained. The proof rewrites each literal inner list indicator scan to countP, identifies countP with the actual mapped-key list count, and uses the exact list-multiplicity regrouping theorem. sparse_keys_card proves |K|<=xs.length. joint_pair_grouping applies the same statement to the ACTUAL pair label (head(i),slot(i)), hence matches both original incidence equalities simultaneously. It does not confuse equality of head labels alone with joint incidence equality.

weighted_pair_grouping proves the stronger identity for arbitrary occurrence weights in any commutative semiring (thus also integer/rational signed weights): sum_i,j [label(i)=label(j)]*w_i*w_j equals sum_k (sum_(i:label(i)=k) w_i)^2. All bucket values are defined as literal list sums. regroup derives key coverage from the actual mapped occurrence list at this application; no supplied sparse histogram is a hypothesis.

## Full partial-prefix head formula

Take the original port/vertex occurrence list xs, variable-key map key, actual current anchored colour colour(key), and active predicate key in remaining. Put T=|xs| and S=number of anchored occurrences. Let C_fixed be the sum of squared colour-bucket multiplicities of anchored occurrences. Let D_free be the sum of squared VARIABLE-KEY multiplicities of free occurrences. These are the weighted buckets using0/1 fixed/free weights; D_free is not a histogram of the currently stored colours of free variables.

For A=L^4 and B=r^(4Q-1), head_prefix_grouping proves (over any commutative ring) that the complete ordered head-pair classifier sum is exactly

    A*C_fixed + B*(T^2-S^2) + (A-B)*D_free.

Loops/repeated keys force the D_free correction. If the original all-head-pair list contains each variable key once, D_free=f where f=T-S, and the equivalent nonnegative integer expression is

    A*(C_fixed+f) + B*(f*(f-1)+2*f*S).

For a general duplicate list, use D_free, not f. The generic theorem follows by a pointwise fixed/free/key-equality partition, exact double-list sum algebra, and weighted_pair_grouping. No probabilistic independence or assignment enumeration is assumed. original_head_pairs explicitly rewrites the ACTUAL original SourceScoreCountsPadding.paddedLocal on the canonical word menu, for every typed original environment and Nodup remaining list, into this classifier. Composing original_head_pairs with head_prefix_grouping gives the all-prefix original head histogram equality. Default/fixed/newest-override semantics come from the already proved original head formula, not a new oracle.

Q0 has no head coordinate. For r1, A=B=1 and anchored colours coincide, giving T² even with duplicated keys. Empty occurrence lists and empty free/fixed partitions are included by ordinary empty sums. Repeated source terms are not removed.

The analogous joint incidence histogram is directly valid for fully anchored original ports, using label(i)=(current owner word,current factor word). The general partially free INCIDENCE kernel has two independent key constraints and additional alias patterns across port pairs. This supplement does not claim its whole-prefix grouping or incremental-state/dictionary algorithm is proved; that remains a separate connector beyond the algebraic ΔB proposal.

## Deterministic acquisition, not unit-cost hashing

A concrete next implementation may first acquire each actual occurrence label and its optional weight exactly once, retaining its getter/physical read report. Deterministically sort these explicit labels by a physical total comparator (lexicographic on one/two acquired word IDs or coordinates), then run-length scan, add actual weights/counts and square each completed bucket. Equal-sort keys must use semantic numeric/coordinate equality, including any high-zero padding; an assumed unit-cost hash/equality oracle is not allowed. The actual mapped list supplies every key, so no external bucket catalogue or coverage certificate is needed.

With T occurrences and label payload width b, mergesort uses O(T log(T+1)) comparisons and charged label-copy/control work; conservative insertion into an explicit association list costs O(T²) comparisons and also suffices for a fixed-polynomial materialized bound. Counts have O(log(T+1)) bits; signed weighted sums add the original weight-width bound. Exact integer arithmetic preserves the identities. Sorting changes only a commutative grouping of score terms, not candidate order or the original left-on-tie chooser. The bit comparator/copy/read and arithmetic loops, actual storage/address bounds and source-specific label acquisition must be instrumented before any formal runtime bound. No execution/clock theorem is claimed by this supplemental mathematical proof.

The useful reduction is from literal all-port-pair scans to a sparse occurrence-label pass plus run-length buckets. Removing original LOCAL completion enumeration is already canonical work from the main packet; this supplement attacks the remaining quadratic all-port-pair summation. Actual source phase/port grouping, incremental updates, fully acquired dictionary state and public-source/counter binding remain explicitly open.
