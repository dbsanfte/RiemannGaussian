# Exact original incidence-completion shortcut

The two new proof modules close the original incidence formula for every prefix. They do not install a new physical callback themselves: the parent owns the paid powers and physical classifier. Their exact theorem simplifies the existing `SourceScoreCountsPadding.paddedLocal`, including its original active-support scan and ordered recursive truth count.

## Original structure, not a generic graph promise

An original incidence descriptor is `(a,b,c,d)` with owners `a,c` encoded from `Sum.inl` and factors `b,d` encoded from `Sum.inr`. Completeness of the original acquired index list makes all four cross inequalities true: `a≠b`, `a≠d`, `c≠b`, `c≠d`. Parent module `SourceIncidenceNamespaces` proves this for actual descriptor compilation and the original indexed caller. Either owner pair or factor pair may still repeat a key. Duplicate descriptors remain separate summands.

Thus the incidence test is the product of two equality predicates on disjoint key sets. No triangle, shared-free-variable path or cross-pair duplicate edge occurs in the original source. Applying a two-edge rank obtained by simply adding edge flags to an arbitrary intersecting graph would be incorrect; this proof deliberately does not do so.

## Formula

Let `L=r^Q`, `r>0`, `A` be the actual duplicate-free remaining key list, and `ω=denote env` for the actual cached environment (including defaults, reverse fixed prefix and newest-first overrides). For one pair `(u,v)` set

* `active(u,v) := u≠v ∧ (u∈A ∨ v∈A)`;
* `OK(u,v) := u=v ∨ u∈A ∨ v∈A ∨ ω(u)=ω(v)`.

A free key must be treated as free even when its current default/override differs from an anchor: its completion overwrites that value. Its current cache value is not an extra constraint.

The edge probability is exactly 1 for a loop, 1/L for an active nonloop, the actual anchor equality indicator otherwise. The product of the two probabilities is the incidence probability. Therefore the original four-coordinate padded count is

```
if OK(a,c) and OK(b,d):
    if active(a,c) and active(b,d): L²
    elif active(a,c) or active(b,d): L³
    else: L⁴
else: 0
```

Equivalently it is zero on an anchor conflict, otherwise `L^(4-d)` where `d` is the number (0,1,2) of active nonloop pairs. Each such disjoint edge consumes at least one different free key, so the underlying unpadded count is `L^(m-d)` for the actual active count m; the implemented formal endpoint proves the padded formula directly and does not assume that raw-count expression.

## Exact Lean endpoints and proof

`SemiprimeSourceIncidencePairAverage` proves:

* `mean_delta`: the actual canonical source-word enumeration assigns probability 1/L to any specified whole word. This uses its proved completeness and Nodup, not a supplied uniformity assertion.
* `pair_mean_step`: eliminates one actual remaining key, handling loops, either active endpoint, the other endpoint still free, and both anchored.
* `pair_average`: exact one-edge conditional average for every duplicate-free remaining list.
* `separated_average`: exact product formula for both disjoint equality pairs, proved by induction on the actual remaining order. At each step at most one pair can depend on the newly assigned key; the other factor pulls out of the finite mean.

`SemiprimeSourceIncidenceCountFormula` defines `pairActive`, `pairOK`, `classifiedCount`, proves `classified_cases`, and proves

```
paddedLocal_formula r Q hr a b c d remaining env hn hab had hcb hcd
```

whose left side is the VALUE OF THE EXISTING original `paddedLocal (alphabet r Q) (.incidence a b c d) remaining env`, and whose right side is `classifiedCount (r^Q) remaining (denote env) a b c d`. No count answer, completion-cardinality lemma, conditional probability, anchor-value oracle, or extra span/rank promise is a premise. Parent's namespace theorem discharges the four inequalities for every actual compiled term.

The final transfer uses the already proved `localTerm_count`, exact `localTerm_value`, and the source `wordExpectation_filter`; cancellation divides only by the known positive integer L⁴. Nothing divides by an unknown group order or by a modular score value. These are characteristic-zero finite counting identities, subsequently usable for exact integer word production.

## All-prefix and degenerate cases

The theorem allows any actual environment and any remaining order with Nodup. Every original sequential remaining range is Nodup. Repeated keys inside either equality are tautologies; descriptor repetitions retain their multiplicity. Physical IDs must be compared by numeric equality/injective bank decoding, not Boolean-list structural equality (leading-zero aliases are not separate words).

For r=1 or Q=0, L=1. The proof still holds, with the four possible values collapsing to 0 or 1; actual canonical words are singleton and contradictory anchors cannot arise among them. There is no head coordinate when Q=0. Empty remaining lists, no active endpoints, an empty fixed prefix, arbitrary overrides, and an anchored conflict are all inside the theorem, without exceptional-path assumptions. r=0 is intentionally outside this endpoint, matching the actual positive source group count.

It is important that the actual menu is the complete duplicate-free function alphabet. An arbitrary duplicate list is not uniform: e.g. two independent draws from `[0,0,1]` have five equality completions, not three. No shortcut theorem is claimed for such an advised or duplicate menu. Duplicate remaining keys are likewise not a premise of this proof; the actual original range never has them.

## Constructive acquisition and ledger

Per incidence term, classify each pair using one actual key-equality test, two remaining-membership tests, and, only when both distinct endpoints are anchored, two actual environment-ID reads and one physical ID equality. Cross-pair independence is proved once from descriptor namespaces; it is not tested by an assignment search. No bank row or colour lookup is needed for incidence once acquired IDs are certified injective. The maximal literal scan alternative uses at most four scans of the original remaining list, so costs O(N) metadata visits per term rather than L^m completions. On the original contiguous remaining range, membership can instead use its two boundary comparisons, once that concrete refinement is attached.

Root's `SourceCountPowers` acquires L²,L³,L⁴ (and the head value G) by actual multiplication, not magnitude-linear L⁴ unary construction. A paid classifier then copies the selected power or zero. Alternatively tally three incidence classes `c2,c3,c4` and combine `I=c2 L²+c3 L³+c4 L⁴`; tally head full/flat classes and combine `H=hFull L⁴+hFlat G`. Every tally prefix is at most the descriptor count T. Cached original integer weights can be multiplied into these five powers once. All ordinary source descriptor multiplicities are preserved.

This is a genuine removal of the local candidate-assignment loops: it does not acquire a full L^m tensor by another representation. Initial bank acquisition, metadata/environment scans, physical key comparisons, copied output words, class-counter arithmetic and power construction must still be charged in the new caller. This note does not assert the full public primitive clock is closed.

## Prior credit and scope

The imported source `SqrtLog/PackingWords.lean` already has unconditional `mean_eval`, `mean_eval_mul` and `mean_incidence_collision` identities. Existing local expectation/filter and count-to-padding theorems are reused directly. The new result is their actual all-prefix, original-program conditional specialization with alias/anchor cases and an exact existing-padded-count endpoint. A bounded search of relevant PackingWords/LocalExpectation/PackingAlgorithm and current count modules found no existing all-prefix classification of these four incidence lanes. The arbitrary two-edge graph component interpretation remains a useful informal generalization, not a prerequisite or a new Lean theorem in this deliverable.

## Verification

Both new canonical sources strictly compile with `autoImplicit=false`, `warningAsError=true`. Ordinary-root 15 linters pass; all automatically generated declarations pass the standard-three-axiom scan (propext, Classical.choice, Quot.sound only): PairAverage 18 declarations/17 theorems, CountFormula 13 declarations/8 theorems. Separate output-path recompiles are pinned in `incidence-formula-verification.json`. No old source or sealed evidence packet was edited.
