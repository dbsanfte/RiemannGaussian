/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramQuery
import RiemannGaussian.SemiprimeSourceHistogramSetupBounds
import RiemannGaussian.SemiprimeSourceHistogramArithmeticBounds
import RiemannGaussian.SemiprimeSourceHistogramFeatureBitsBounds
import RiemannGaussian.SemiprimeSourceHistogramHeadBounds

/-! # Actual original histogram-query width and clock
All sixteen feature passes, the all-coordinate head pass, signed arithmetic,
and one actual prefix dictionary are paid. Setup is separately retained; no
histogram, Fits, output-width, callback-clock or native count advice is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeSourceHistogramQueryBounds
open scoped BigOperators
open SemiprimeBitArithmetic SemiprimeRationalBits
open SemiprimeSourceHistogramQuery
open SemiprimeSourceHistogramArithmeticBounds
open SemiprimeSourceIncidenceHistogram (Feature)

/-- Original logarithmic acquired-input widths, before fixed-depth score arithmetic. -/
def baseWidth (n M r Q lam : ℕ) : ℕ := 1+
  Nat.clog 2 (r^Q+1)+Nat.clog 2 ((r^Q)^2+1)+Nat.clog 2 ((r^Q)^4+1)+
  Nat.clog 2 (r^(4*Q-1)+1)+Nat.clog 2 (n^2*lam^2*(r^Q)^4+1)+
  Nat.clog 2 (4*M^2+1)+Nat.clog 2 (M^2+1)+Nat.clog 2 ((Q*n)^2+1)+
  Nat.clog 2 (Q+1)+Nat.clog 2 (n+2)

/-- Actual incidence/head output shape fits this fixed-depth acquired-width envelope. -/
def laneWidth (n M r Q lam : ℕ) : ℕ := grow (baseWidth n M r Q lam) 20

/-- Actual final signed score shape, independent of histogram values. -/
def outputWidth (n M r Q lam : ℕ) : ℕ := grow (laneWidth n M r Q lam) 2

private theorem base_caps (n M r Q lam : ℕ) :
    1 ≤ baseWidth n M r Q lam ∧
    Nat.clog 2 (r^Q+1) ≤ baseWidth n M r Q lam ∧
    Nat.clog 2 ((r^Q)^2+1) ≤ baseWidth n M r Q lam ∧
    Nat.clog 2 ((r^Q)^4+1) ≤ baseWidth n M r Q lam ∧
    Nat.clog 2 (r^(4*Q-1)+1) ≤ baseWidth n M r Q lam ∧
    Nat.clog 2 (n^2*lam^2*(r^Q)^4+1) ≤ baseWidth n M r Q lam ∧
    Nat.clog 2 (4*M^2+1) ≤ baseWidth n M r Q lam ∧
    Nat.clog 2 (M^2+1) ≤ baseWidth n M r Q lam ∧
    Nat.clog 2 ((Q*n)^2+1) ≤ baseWidth n M r Q lam ∧
    Nat.clog 2 (Q+1) ≤ baseWidth n M r Q lam ∧
    Nat.clog 2 (n+2) ≤ baseWidth n M r Q lam := by
  unfold baseWidth
  omega

/-- Complete prefix construction from actual selected IDs, without native ID encoding. -/
def prefixBudget (L k : ℕ) : ℕ :=
  k*(100*(Nat.clog 2 (L+1)+SemiprimeSourceHistogramTrieBounds.clockWidth k+2))+1

/-- Complete per-query report, separate from the once-acquired setup producer.
The only incidence count is M; there is no M²+Q*n² descriptor construction. -/
def scoreBudget (n F M r Q lam k : ℕ) : ℕ :=
  prefixBudget (r^Q) k+
  16*SemiprimeSourceHistogramFeatureBitsBounds.budget (n+F) (r^Q) M+
  SemiprimeSourceHistogramHeadBounds.budget r Q (SemiprimeSourceHistogramPortKeys.keyWidth n) n+
  90*unitBudget (baseWidth n M r Q lam)+3*unitBudget (laneWidth n M r Q lam)+k+10

/-- Actual sparse original port-list size discharges the query's M parameter. -/
theorem records_length (n F r Q lam : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner).data.records.length=∑ e,arity e := by
  rw [SemiprimeSourceHistogramSetup.records_actual,
    SemiprimeSourceHistogramPortKeys.acquirePorts_value,List.length_map]
  exact (SemiprimeSourceHistogramMetadata.sizes n F Q arity).2.2.1

/-- Original head cache is the actual complete original vertex list, not an advised scan. -/
theorem vertices_actual (n F r Q lam : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner).vertices=
      (SemiprimeSourceHistogramHeadBits.verticesWith (List.finRange n)).value := by
  change (SemiprimeSourceHistogramHeadBits.verticesWith
    (SemiprimeSourceHistogramPortKeys.acquireOriginal n F Q arity owner).metadata.vertices).value=_
  rw [SemiprimeSourceHistogramPortKeys.acquireOriginal_metadata]
  simp only [SemiprimeSourceHistogramMetadata.acquire,SemiprimeSourceHistogramMetadata.finFast_value]

/-- Original list counting gives the actual compact coordinate operand width. -/
theorem coordinate_length (n F r Q lam : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner).coordinateCount.length ≤
      Nat.clog 2 (Q+1) := by
  have h := SemiprimeSourceHistogramCountInput.count_length
    (SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner).data.metadata.coordinates
  rw [SemiprimeSourceHistogramSetup.metadata_actual,
    (SemiprimeSourceHistogramMetadata.sizes n F Q arity).2.2.2.1] at h
  exact h

/-- Every acquired scale and weight output fits the same original logarithmic cap. -/
theorem scales_widths (n F r Q lam : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    let cache := SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner
    let W := baseWidth n (∑ e,arity e) r Q lam
    cache.scales.alphabet.length ≤ W ∧ cache.scales.square.length ≤ W ∧
    cache.scales.fourth.length ≤ W ∧ cache.scales.head.length ≤ W ∧
    cache.scales.weights.incidence.length ≤ W ∧ cache.scales.weights.head.length ≤ W := by
  let cache := SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner
  have h := SemiprimeSourceHistogramScales.acquire_lengths r Q lam cache.data.records cache.data.metadata.vertices
  have hm := records_length n F r Q lam arity owner
  have hn : cache.data.metadata.vertices.length=n := by
    rw [SemiprimeSourceHistogramSetup.metadata_actual]
    exact (SemiprimeSourceHistogramMetadata.sizes n F Q arity).1
  rw [hm,hn] at h
  obtain ⟨_,hL,hS,hA,hG,hwa,hwb,_,_,_,_⟩ := base_caps n (∑ e,arity e) r Q lam
  exact ⟨h.1.trans hL,h.2.1.trans hS,h.2.2.1.trans hA,h.2.2.2.1.trans hG,
    h.2.2.2.2.1.trans hwa,h.2.2.2.2.2.trans hwb⟩

/-- Actual feature histograms derive width from their original ordered port count. -/
theorem feature_width (n F r Q lam : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (dict : SemiprimeSourceHistogramTrie.Trie) (k s : ℕ) (f g : Feature) :
    (SemiprimeSourceHistogramFeatureBits.acquire dict k s f g
      (SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner).data.records).bits.length ≤
        baseWidth n (∑ e,arity e) r Q lam := by
  have h := SemiprimeSourceHistogramFeatureBitsBounds.acquire_length dict k s f g
    (SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner).data.records
  rw [records_length] at h
  obtain ⟨_,_,_,_,_,_,_,hI,_,_,_⟩ := base_caps n (∑ e,arity e) r Q lam
  exact h.trans hI

/-- All actual sixteen producer clocks follow original acquired prefix/port data. -/
theorem feature_clock (n F r Q lam : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (fixed : List (List Bool))
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids)
    (k s : ℕ) (f g : Feature) :
    (SemiprimeSourceHistogramFeatureBits.acquire (SemiprimeSourceHistogramPrefix.acquire fixed).trie k s f g
      (SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner).data.records).clock ≤
        SemiprimeSourceHistogramFeatureBitsBounds.budget (n+F) (r^Q) (∑ e,arity e) := by
  rw [SemiprimeSourceHistogramSetup.records_actual]
  have h := SemiprimeSourceHistogramFeatureBitsBounds.acquirePorts_clock owner
    (SemiprimeSourceHistogramMetadata.acquire n F Q arity).incidences
    (SemiprimeSourceHistogramPrefix.acquire fixed).trie k s f g (r^Q)
    (SemiprimeSourceHistogramPrefix.stored_compact fixed)
    (SemiprimeSourceHistogramDictRefinement.count_cap r Q fixed hf)
  rwa [(SemiprimeSourceHistogramMetadata.sizes n F Q arity).2.2.1] at h

/-- Actual incidence producers and fixed-depth combination both retain their costs. -/
theorem incidence_bound_original (n F r Q lam : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (fixed : List (List Bool))
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids) (k s : ℕ) :
    let cache := SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner
    let dict := (SemiprimeSourceHistogramPrefix.acquire fixed).trie
    Width (incidenceWith cache dict k s).word (laneWidth n (∑ e,arity e) r Q lam) ∧
    (incidenceWith cache dict k s).clock ≤
      16*SemiprimeSourceHistogramFeatureBitsBounds.budget (n+F) (r^Q) (∑ e,arity e)+
        60*unitBudget (baseWidth n (∑ e,arity e) r Q lam) := by
  let cache := SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner
  let dict := (SemiprimeSourceHistogramPrefix.acquire fixed).trie
  let hist := fun f g => SemiprimeSourceHistogramFeatureBits.acquire dict k s f g cache.data.records
  obtain ⟨hW,_,_,_,_,_,_,_,_,_,_⟩ := base_caps n (∑ e,arity e) r Q lam
  have hs := scales_widths n F r Q lam arity owner
  have h := SemiprimeSourceHistogramArithmeticBounds.incidence_bound cache.scales hist
    (baseWidth n (∑ e,arity e) r Q lam) hW hs.1 hs.2.1
    (fun f g => feature_width n F r Q lam arity owner dict k s f g)
  have hsum := SemiprimeSourceHistogramSquaresBounds.list_sum_cap
    SemiprimeSourceHistogramArithmetic.featurePairs
    (fun fg => (hist fg.1 fg.2).clock)
    (SemiprimeSourceHistogramFeatureBitsBounds.budget (n+F) (r^Q) (∑ e,arity e))
    (fun fg _ => feature_clock n F r Q lam arity owner fixed hf k s fg.1 fg.2)
  rw [SemiprimeSourceHistogramArithmeticBounds.featurePairs_length] at hsum
  exact ⟨h.1,h.2.trans (Nat.add_le_add_right hsum _)⟩

/-- Actual physical head counters and collision word derive all head-arithmetic guards. -/
theorem head_bound_original (n F r Q lam : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (fixed : List (List Bool))
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids) (k s : ℕ) :
    let cache := SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner
    let dict := (SemiprimeSourceHistogramPrefix.acquire fixed).trie
    Width (headWith cache dict k s).word (grow (baseWidth n (∑ e,arity e) r Q lam) 8) ∧
    (headWith cache dict k s).clock ≤
      SemiprimeSourceHistogramHeadBounds.budget r Q (SemiprimeSourceHistogramPortKeys.keyWidth n) n+
        30*unitBudget (baseWidth n (∑ e,arity e) r Q lam)+3 := by
  let cache := SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner
  let dict := (SemiprimeSourceHistogramPrefix.acquire fixed).trie
  let data := SemiprimeSourceHistogramHeadBits.acquire cache.rows dict k s cache.vertices
  let C : RationalReport := ⟨(SemiprimeSourceHistogramArithmetic.fromState data.histogram).word,data.clock+3⟩
  obtain ⟨hW,_,_,_,_,_,_,_,hH,hq,hcount⟩ := base_caps n (∑ e,arity e) r Q lam
  have hs := scales_widths n F r Q lam arity owner
  have hvlen : cache.vertices.length=n := by
    rw [vertices_actual,SemiprimeSourceHistogramHeadBounds.verticesWith_length,List.length_finRange]
  have hc := SemiprimeSourceHistogramHeadBounds.counter_lengths cache.rows dict k s cache.vertices n hvlen.le
  have hp : data.head.fixed.length ≤ baseWidth n (∑ e,arity e) r Q lam := hc.1.trans hcount
  have hf' : data.head.free.length ≤ baseWidth n (∑ e,arity e) r Q lam := hc.2.trans hcount
  have hq' := (coordinate_length n F r Q lam arity owner).trans hq
  have hrows : cache.rows=SemiprimeSourceHistogramRowKeys.acquireCaches r Q := rfl
  have hdict : dict=(SemiprimeSourceHistogramPrefix.acquire fixed).trie := rfl
  have hlen : data.head.keys.length ≤ Q*n := by
    change (SemiprimeSourceHistogramHeadBits.produce cache.rows dict k s cache.vertices).keys.length ≤ _
    rw [vertices_actual,hrows,hdict]
    have h := SemiprimeSourceHistogramHeadBounds.produce_length r Q fixed hf k s
      (SemiprimeSourceHistogramHeadBits.verticesWith (List.finRange n)).value
    simpa only [SemiprimeSourceHistogramHeadBounds.verticesWith_length,List.length_finRange] using h
  have hbits : data.histogram.bits.length ≤ baseWidth n (∑ e,arity e) r Q lam := by
    have h := SemiprimeSourceHistogramSquaresBounds.square_width data.head.keys
    have hm := Nat.clog_mono_right 2 (Nat.add_le_add_right (Nat.pow_le_pow_left hlen 2) 1)
    exact h.trans (hm.trans hH)
  have hC : Width C.word (baseWidth n (∑ e,arity e) r Q lam) := unsigned_width _ _ hW hbits
  have h := SemiprimeSourceHistogramArithmeticBounds.head_bound cache.scales
    (⟨cache.coordinateCount,0⟩:SemiprimeSourceCompactBits.Report)
    (⟨data.head.fixed,0⟩:SemiprimeSourceCompactBits.Report)
    (⟨data.head.free,0⟩:SemiprimeSourceCompactBits.Report) C
    (baseWidth n (∑ e,arity e) r Q lam) hW hs.2.2.1 hs.2.2.2.1 hq' hp hf' hC
  have hdclock : data.clock ≤ SemiprimeSourceHistogramHeadBounds.budget r Q
      (SemiprimeSourceHistogramPortKeys.keyWidth n) n := by
    change (SemiprimeSourceHistogramHeadBits.acquire cache.rows dict k s cache.vertices).clock ≤ _
    rw [vertices_actual,hrows,hdict]
    simpa only [List.length_finRange] using
      SemiprimeSourceHistogramHeadBounds.acquire_static_clock r Q fixed hf k s (List.finRange n)
  refine ⟨h.1,?_⟩
  exact h.2.trans (by
    change 0+0+0+(data.clock+3)+30*unitBudget (baseWidth n (∑ e,arity e) r Q lam) ≤ _
    omega)

/-- All actual lane inputs fit the derived weighted-arithmetic envelope. -/
theorem scoreWith_bound_original (n F r Q lam : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (fixed : List (List Bool))
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids) (k s : ℕ) :
    let cache := SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner
    let dict := (SemiprimeSourceHistogramPrefix.acquire fixed).trie
    Width (scoreWith cache dict k s).word (outputWidth n (∑ e,arity e) r Q lam) ∧
    (scoreWith cache dict k s).clock ≤
      16*SemiprimeSourceHistogramFeatureBitsBounds.budget (n+F) (r^Q) (∑ e,arity e)+
      SemiprimeSourceHistogramHeadBounds.budget r Q (SemiprimeSourceHistogramPortKeys.keyWidth n) n+
      90*unitBudget (baseWidth n (∑ e,arity e) r Q lam)+
      3*unitBudget (laneWidth n (∑ e,arity e) r Q lam)+3 := by
  let cache := SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner
  let dict := (SemiprimeSourceHistogramPrefix.acquire fixed).trie
  have hI := incidence_bound_original n F r Q lam arity owner fixed hf k s
  have hH := head_bound_original n F r Q lam arity owner fixed hf k s
  have hs := scales_widths n F r Q lam arity owner
  have hbase : baseWidth n (∑ e,arity e) r Q lam ≤ laneWidth n (∑ e,arity e) r Q lam :=
    (show baseWidth n (∑ e,arity e) r Q lam ≤ grow (baseWidth n (∑ e,arity e) r Q lam) 0 by simp [grow]).trans
      (grow_mono _ (by decide : 0 ≤ 20))
  have hh := widen hH.1 (grow_mono (baseWidth n (∑ e,arity e) r Q lam) (by decide : 8 ≤ 20))
  have h := SemiprimeSourceHistogramArithmeticBounds.weighted_bound cache.scales
    (incidenceWith cache dict k s) (headWith cache dict k s)
    (laneWidth n (∑ e,arity e) r Q lam) (grow_pos _ 20)
    (hs.2.2.2.2.1.trans hbase) (hs.2.2.2.2.2.trans hbase) hI.1 hh
  refine ⟨h.1,?_⟩
  exact h.2.trans (by
    have hi := hI.2
    have hh' := hH.2
    change (incidenceWith cache dict k s).clock ≤ _ at hi
    change (headWith cache dict k s).clock ≤ _ at hh'
    omega)

/-- Actual selected-ID membership closes prefix acquisition without encoded-ID advice. -/
theorem prefix_clock (r Q : ℕ) (fixed : List (List Bool))
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids) :
    (SemiprimeSourceHistogramPrefix.acquire fixed).clock ≤ prefixBudget (r^Q) fixed.length :=
  SemiprimeSourceHistogramPrefix.acquire_clock fixed _ fixed.length le_rfl
    (fun id hi => SemiprimeSourceCompactWordBank.ids_bounded r Q id (hf id hi))

/-- Complete actual query shape and report from original setup and selected prefix.
Only reached-menu membership is required; no output/Fits/clock advice occurs. -/
theorem score_bound (n F r Q lam : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (fixed : List (List Bool)) (s : ℕ)
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids) :
    let cache := SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner
    Width (score cache fixed s).word (outputWidth n (∑ e,arity e) r Q lam) ∧
    (score cache fixed s).clock ≤ scoreBudget n F (∑ e,arity e) r Q lam fixed.length := by
  have h := scoreWith_bound_original n F r Q lam arity owner fixed hf fixed.length s
  have hp := prefix_clock r Q fixed hf
  refine ⟨h.1,?_⟩
  unfold score scoreBudget
  dsimp only
  omega

/-- Final original-query report, including one actually acquired prefix trie. -/
theorem score_clock (n F r Q lam : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (fixed : List (List Bool)) (s : ℕ)
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids) :
    (score (SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner) fixed s).clock ≤
      scoreBudget n F (∑ e,arity e) r Q lam fixed.length :=
  (score_bound n F r Q lam arity owner fixed s hf).2

/-- Final signed physical output width is derived from acquired original dimensions. -/
theorem score_width (n F r Q lam : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (fixed : List (List Bool)) (s : ℕ)
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids) :
    Width (score (SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner) fixed s).word
      (outputWidth n (∑ e,arity e) r Q lam) :=
  (score_bound n F r Q lam arity owner fixed s hf).1

/-- Standalone input acquisition remains an explicit separately paid producer.
This does not assert a new setup-clock or full-machine execution theorem. -/
theorem indexed_clock (n F r Q lam : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (fixed : List (List Bool)) (s : ℕ)
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids) :
    (indexed n F r Q lam arity owner fixed s).clock ≤
      (SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner).clock+
        scoreBudget n F (∑ e,arity e) r Q lam fixed.length+3 := by
  exact Nat.add_le_add_right (Nat.add_le_add_left
    (score_clock n F r Q lam arity owner fixed s hf) _) 3

/-- Reachable-prefix length caps enlarge only the actual prefix acquisition term. -/
theorem scoreBudget_prefix_mono (n F M r Q lam : ℕ) {k K : ℕ} (hk : k ≤ K) :
    scoreBudget n F M r Q lam k ≤ scoreBudget n F M r Q lam K := by
  have hc := Nat.clog_mono_right 2 (Nat.add_le_add_right hk 2)
  unfold scoreBudget prefixBudget SemiprimeSourceHistogramTrieBounds.clockWidth
  gcongr

/-- Closed standalone original setup plus actual query report. Cached callers pay
this setup once, then use score_clock for each subsequent query. -/
theorem indexed_clock_closed (n F r Q lam : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (fixed : List (List Bool)) (s : ℕ)
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids) :
    (indexed n F r Q lam arity owner fixed s).clock ≤
      SemiprimeSourceHistogramSetupBounds.budget n F r Q lam (∑ e,arity e) (r^Q)+
        scoreBudget n F (∑ e,arity e) r Q lam fixed.length+3 := by
  have hs := SemiprimeSourceHistogramSetupBounds.acquire_clock n F r Q lam arity owner (NeZero.pos r)
  exact (indexed_clock n F r Q lam arity owner fixed s hf).trans
    (Nat.add_le_add_right (Nat.add_le_add_right hs _) 3)

end RiemannGaussian.SemiprimeSourceHistogramQueryBounds
