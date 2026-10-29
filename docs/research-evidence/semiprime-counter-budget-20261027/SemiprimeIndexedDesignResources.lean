/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeFullSetupCounter
import RiemannGaussian.SemiprimeScheduledCounter

/-! # Quantitative resources for the actual indexed source design
The enumeration-parametric source bounds are instantiated at the actual indexed
lists. No equality with default enumeration or its deterministic choices is used.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace RiemannGaussian.SemiprimeIndexedDesignResources
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open SqrtLog MulticolorTypes
open SemiprimeRuntimeDesignAcquisition SemiprimeAcquiredSourceCounter
open SemiprimeSourceLayout
variable {n F r Q : ℕ} [NeZero r]

/-- The old semantic design at precisely the actual indexed source. -/
abbrev indexedDesign (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R B : ℕ) (t : Fin Q) :=
  build (raw (r:=r) arity coordinate eps R B t)

/-- Original head size is exactly its source subtype cardinal, not a bound
for a different tie order. -/
theorem head_card (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R B : ℕ) (t : Fin Q) (g : Fin r) :
    (indexedDesign (r:=r) arity coordinate eps R B t).h g =
      Fintype.card {v : Fin n // (layout (r:=r) (Q:=Q) arity coordinate eps R).head t v=g} := by
  simp only [indexedDesign,build,cache,uncache,headSize,raw]
  rw [Fintype.card_subtype]
  change (List.filter _ (List.finRange n)).length=_
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  simp only [List.toFinset_filter,List.toFinset_finRange,decide_eq_true_eq]
  rfl

/-- Every actual stored measurement bound is the original public height. -/
theorem measurement (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R B : ℕ) (t : Fin Q) (g : Fin r) :
    (indexedDesign (r:=r) arity coordinate eps R B t).W g=measurementBound B Q R := rfl

/-- The actual selected rank sum equals the source rank sum, including padding. -/
theorem rank_sum (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R B : ℕ) (t : Fin Q) :
    (∑ g : Fin r,(indexedDesign (r:=r) arity coordinate eps R B t).m g)=
      ∑ g : Fin r,LayoutRank.rowRank ((layout (r:=r) (Q:=Q) arity coordinate eps R).constraints t g) := by
  apply Finset.sum_congr rfl
  intro g _
  exact selected_count_source arity coordinate eps R B t g

/-- Actual indexed heads satisfy the published balanced bound. -/
theorem indexed_head_bound (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R B a : ℕ)
    (hp : PackingGuard (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2)
      Sigma.fst r Q eps B a) (t : Fin Q) (g : Fin r) :
    ((indexedDesign (r:=r) arity coordinate eps R B t).h g : ℚ)≤3*(n:ℚ)/(2*(r:ℚ)) := by
  rw [head_card]
  convert builtLayout_head_bound (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2)
      Sigma.fst (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps R B a hp t g using 1 <;> simp only [Fintype.card_fin,layout]
  rfl

/-- Actual indexed rank bound, directly from the enumeration-parametric source theorem. -/
theorem indexed_rank_le (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R B a : ℕ)
    (hp : PackingGuard (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2)
      Sigma.fst r Q eps B a)
    (hr : 2≤r) (hQ : 2≤Q) (hR : 4≤R) (hsize : 4*R≤Q)
    (hwidth : 32*((Q-1:ℕ):ℝ)*Real.log (2/(eps:ℝ))≤(R:ℝ)^2) (t : Fin Q) :
    ((∑ g : Fin r,(indexedDesign (r:=r) arity coordinate eps R B t).m g):ℚ)≤
      2*eps*(∑ e,arity e) := by
  have ht := builtLayout_total_rank
    (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2)
    Sigma.fst (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps R B a hp hr hQ hR hsize hwidth t
  convert ht using 1
  · apply Finset.sum_congr rfl
    intro g _
    exact congrArg (fun z : ℕ => (z:ℚ)) (selected_count_source arity coordinate eps R B t g)
  · simp only [Fintype.card_sigma,Fintype.card_fin]

/-- Every actual head has at most all original variables. -/
theorem head_le (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R B : ℕ) (t : Fin Q) (g : Fin r) :
    (indexedDesign (r:=r) arity coordinate eps R B t).h g≤n := by
  rw [head_card]
  simpa using Fintype.card_le_of_injective
    (fun v : {v : Fin n // (layout (r:=r) (Q:=Q) arity coordinate eps R).head t v=g} => v.val)
    Subtype.val_injective

/-- Literal native summary product is controlled by actual total selected rank. -/
theorem summary_le_rank (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R B : ℕ) (t : Fin Q) :
    SemiprimePacketArrayExecution.summaryCount r
      (indexedDesign (r:=r) arity coordinate eps R B t).h
      (indexedDesign (r:=r) arity coordinate eps R B t).m
      (indexedDesign (r:=r) arity coordinate eps R B t).W ≤
      (2*n*measurementBound B Q R+1)^
        (∑ g : Fin r,(indexedDesign (r:=r) arity coordinate eps R B t).m g) := by
  unfold SemiprimePacketArrayExecution.summaryCount
  simp only [Fintype.card_fin,measurement,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  calc
    _ ≤ ∏ g : Fin r,(2*n*measurementBound B Q R+1)^
        (indexedDesign (r:=r) arity coordinate eps R B t).m g := by
      apply Finset.prod_le_prod
      intro g _
      apply Nat.pow_le_pow_left
      have hh := head_le arity coordinate eps R B t g
      simpa only [Nat.mul_assoc] using
        Nat.add_le_add_right (Nat.mul_le_mul_right (measurementBound B Q R) (Nat.mul_le_mul_left 2 hh)) 1
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

/-- A denominator-weighted natural rank bound gives the literal floor exponent. -/
theorem summary_le_floor (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R B den cap : ℕ) (t : Fin Q) (hd : 0<den)
    (hrank : (∑ g : Fin r,(indexedDesign (r:=r) arity coordinate eps R B t).m g)*den≤cap) :
    SemiprimePacketArrayExecution.summaryCount r
      (indexedDesign (r:=r) arity coordinate eps R B t).h
      (indexedDesign (r:=r) arity coordinate eps R B t).m
      (indexedDesign (r:=r) arity coordinate eps R B t).W ≤
      (2*n*measurementBound B Q R+1)^(cap/den) := by
  exact (summary_le_rank arity coordinate eps R B t).trans
    (Nat.pow_le_pow_right (by omega) ((Nat.le_div_iff_mul_le hd).mpr hrank))

/-- Natural balanced head envelope for the actual indexed design. -/
theorem indexed_head_ceil (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R B a : ℕ)
    (hp : PackingGuard (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2)
      Sigma.fst r Q eps B a) (t : Fin Q) (g : Fin r) :
    (indexedDesign (r:=r) arity coordinate eps R B t).h g≤⌈3*(n:ℚ)/(2*(r:ℚ))⌉₊ := by
  exact_mod_cast (indexed_head_bound arity coordinate eps R B a hp t g).trans
    (Nat.le_ceil _)

open SemiprimeCounterRate SemiprimeSourceLayoutRate SemiprimeScheduledCounter

/-- Numeric packing guards instantiated at the actual indexed dimensions;
this theorem makes no assertion about enumeration equality. -/
theorem scheduledPackingGuard (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (w : ℕ)
    (hg : sourceLayoutGuard n w)
    (hocc : ∀ v,(Finset.univ.filter
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2=v)).card≤2)
    (hscope : ∀ e,arity e≤w) (hM : (∑ e,arity e)=2*n) :
    PackingGuard (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2)
      Sigma.fst (scheduledGroupCount (Nat.clog 2 n)) (scheduledPointCount (Nat.clog 2 n))
        (scheduledEpsilon n) 2 w := by
  have hg' : sourceLayoutGuard (Fintype.card (Fin n)) w := by simpa using hg
  have hm : Fintype.card (SemiprimeConstructedCounter.Incidence arity)=2*Fintype.card (Fin n) := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using hM
  simpa only [SemiprimeScheduledCounter.parameters,Fintype.card_fin] using
    SemiprimeScheduledCounter.packingGuard (coordinate:=coordinate) w hg' hocc hscope hm

/-- Scheduled actual indexed head cardinal bound, with no supplied balance premise. -/
theorem scheduled_head_bound (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (w : ℕ)
    (hg : sourceLayoutGuard n w)
    [NeZero (scheduledGroupCount (Nat.clog 2 n))]
    (hocc : ∀ v,(Finset.univ.filter
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2=v)).card≤2)
    (hscope : ∀ e,arity e≤w) (hM : (∑ e,arity e)=2*n)
    (t : Fin (scheduledPointCount (Nat.clog 2 n)))
    (g : Fin (scheduledGroupCount (Nat.clog 2 n))) :
    (indexedDesign (r:=scheduledGroupCount (Nat.clog 2 n)) arity coordinate
      (scheduledEpsilon n) (scheduledDegree (Nat.clog 2 n)) 2 t).h g≤
      ⌈3*(n:ℚ)/(2*(scheduledGroupCount (Nat.clog 2 n):ℚ))⌉₊ :=
  indexed_head_ceil arity coordinate (scheduledEpsilon n) (scheduledDegree (Nat.clog 2 n)) 2 w
    (scheduledPackingGuard arity coordinate w hg hocc hscope hM) t g

/-- The scheduled rank budget holds at the indexed tie order actually executed. -/
theorem scheduled_rank_budget (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (w : ℕ)
    (hg : sourceLayoutGuard n w)
    [NeZero (scheduledGroupCount (Nat.clog 2 n))]
    (hocc : ∀ v, (Finset.univ.filter
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2=v)).card≤2)
    (hscope : ∀ e,arity e≤w) (hM : (∑ e,arity e)=2*n)
    (t : Fin (scheduledPointCount (Nat.clog 2 n))) :
    (∑ g : Fin (scheduledGroupCount (Nat.clog 2 n)),
      (indexedDesign (r:=scheduledGroupCount (Nat.clog 2 n)) arity coordinate
        (scheduledEpsilon n) (scheduledDegree (Nat.clog 2 n)) 2 t).m g)*
      (scheduledGroupCount (Nat.clog 2 n)*Nat.clog 2 n)≤4*n := by
  have hg' : sourceLayoutGuard (Fintype.card (Fin n)) w := by simpa using hg
  have hm : Fintype.card (SemiprimeConstructedCounter.Incidence arity)=2*Fintype.card (Fin n) := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using hM
  have hp := SemiprimeScheduledCounter.packingGuard (coordinate:=coordinate) w hg' hocc hscope hm
  have hp' : PackingGuard (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2)
      Sigma.fst (scheduledGroupCount (Nat.clog 2 n)) (scheduledPointCount (Nat.clog 2 n))
        (scheduledEpsilon n) 2 w := by
    simpa only [SemiprimeScheduledCounter.parameters,Fintype.card_fin] using hp
  have hr := indexed_rank_le arity coordinate (scheduledEpsilon n)
    (scheduledDegree (Nat.clog 2 n)) 2 w hp'
    hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2.1
    (by simpa only [scheduledEpsilon_cast] using hg.2.2.2.2.2.2.2.2.2.2) t
  rw [hM] at hr
  have heps : 0<scheduledEpsilon n := by
    exact_mod_cast (show (0:ℝ)<(scheduledEpsilon n:ℝ) by
      rw [scheduledEpsilon_cast]; exact hg.2.2.2.2.2.2.1)
  have hd : (0:ℚ)<(scheduledGroupCount (Nat.clog 2 n)*Nat.clog 2 n:ℕ) :=
    one_div_pos.mp heps
  have hb := mul_le_mul_of_nonneg_right hr (le_of_lt hd)
  have he : (2*scheduledEpsilon n*(2*n:ℕ)) *
      (scheduledGroupCount (Nat.clog 2 n)*Nat.clog 2 n:ℕ)=(4*n:ℚ) := by
    change (2*(1/_)*_)*_=_
    field_simp
    push_cast
    ring
  rw [he] at hb
  simp only [indexedDesign,build,cache,uncache,raw] at hb ⊢
  exact_mod_cast hb

/-- The scheduled indexed design's LITERAL native summary count has the same
binary envelope, without identifying its layout with default enumeration. -/
theorem scheduled_summary_log_bound (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (w : ℕ)
    (hg : sourceLayoutGuard n w)
    [NeZero (scheduledGroupCount (Nat.clog 2 n))]
    (hocc : ∀ v,(Finset.univ.filter
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2=v)).card≤2)
    (hscope : ∀ e,arity e≤w) (hM : (∑ e,arity e)=2*n)
    (hν : 64≤Nat.clog 2 (Nat.clog 2 n))
    (t : Fin (scheduledPointCount (Nat.clog 2 n))) :
    let d := indexedDesign (r:=scheduledGroupCount (Nat.clog 2 n)) arity coordinate
      (scheduledEpsilon n) (scheduledDegree (Nat.clog 2 n)) 2 t
    Real.log (SemiprimePacketArrayExecution.summaryCount d.r d.h d.m d.W : ℝ)≤
      (48*(n:ℝ)*(Nat.clog 2 (Nat.clog 2 n):ℝ)^2/Real.sqrt (Nat.clog 2 n:ℝ))*Real.log 2 := by
  let d := indexedDesign (r:=scheduledGroupCount (Nat.clog 2 n)) arity coordinate
    (scheduledEpsilon n) (scheduledDegree (Nat.clog 2 n)) 2 t
  let rank : ℕ := ∑ g : Fin (scheduledGroupCount (Nat.clog 2 n)), d.m g
  have hb : rank*(scheduledGroupCount (Nat.clog 2 n)*Nat.clog 2 n)≤4*n :=
    scheduled_rank_budget arity coordinate w hg hocc hscope hM t
  have hr := source_summary_binary_rate hν hb
  have hc := summary_le_rank (r:=scheduledGroupCount (Nat.clog 2 n)) arity coordinate (scheduledEpsilon n)
    (scheduledDegree (Nat.clog 2 n)) 2 t
  have he : measurementBound 2 (scheduledPointCount (Nat.clog 2 n))
      (scheduledDegree (Nat.clog 2 n))=sourceHeight (Nat.clog 2 n) := rfl
  rw [he] at hc
  have hc' : SemiprimePacketArrayExecution.summaryCount d.r d.h d.m d.W≤
      sourceSignatureBase n^rank := by
    simpa only [d,rank,sourceSignatureBase,Nat.mul_assoc,indexedDesign,build,cache,uncache,raw] using hc
  have hp : 0<SemiprimePacketArrayExecution.summaryCount d.r d.h d.m d.W := by
    unfold SemiprimePacketArrayExecution.summaryCount
    apply Finset.prod_pos
    intro g _
    apply Finset.prod_pos
    intro j _
    omega
  have hl := Real.log_le_log (show (0:ℝ)<SemiprimePacketArrayExecution.summaryCount d.r d.h d.m d.W by
      exact_mod_cast hp) (show (SemiprimePacketArrayExecution.summaryCount d.r d.h d.m d.W:ℝ)≤
        (sourceSignatureBase n:ℝ)^rank by exact_mod_cast hc')
  rw [Real.log_pow] at hl
  exact hl.trans hr

/-- Positive scheduled rank denominator, from the ACTUAL guard's positive tolerance. -/
theorem scheduled_den_pos (w : ℕ) (hg : sourceLayoutGuard n w) :
    0<scheduledGroupCount (Nat.clog 2 n)*Nat.clog 2 n := by
  have heps : 0<scheduledEpsilon n := by
    exact_mod_cast (show (0:ℝ)<(scheduledEpsilon n:ℝ) by
      rw [scheduledEpsilon_cast]; exact hg.2.2.2.2.2.2.1)
  have hd : (0:ℚ)<(scheduledGroupCount (Nat.clog 2 n)*Nat.clog 2 n:ℕ) :=
    one_div_pos.mp heps
  exact_mod_cast hd

/-- Individual selected measurements have the safe native polynomial envelope. -/
theorem scheduled_measurement_le (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (w : ℕ)
    (hg : sourceLayoutGuard n w)
    [NeZero (scheduledGroupCount (Nat.clog 2 n))]
    (hocc : ∀ v,(Finset.univ.filter
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2=v)).card≤2)
    (hscope : ∀ e,arity e≤w) (hM : (∑ e,arity e)=2*n)
    (t : Fin (scheduledPointCount (Nat.clog 2 n)))
    (g : Fin (scheduledGroupCount (Nat.clog 2 n))) :
    (indexedDesign (r:=scheduledGroupCount (Nat.clog 2 n)) arity coordinate
      (scheduledEpsilon n) (scheduledDegree (Nat.clog 2 n)) 2 t).m g≤4*n := by
  have hb := scheduled_rank_budget arity coordinate w hg hocc hscope hM t
  have hd := scheduled_den_pos w hg
  have hs : (indexedDesign (r:=scheduledGroupCount (Nat.clog 2 n)) arity coordinate
      (scheduledEpsilon n) (scheduledDegree (Nat.clog 2 n)) 2 t).m g≤
      ∑ g : Fin (scheduledGroupCount (Nat.clog 2 n)),
        (indexedDesign (r:=scheduledGroupCount (Nat.clog 2 n)) arity coordinate
          (scheduledEpsilon n) (scheduledDegree (Nat.clog 2 n)) 2 t).m g :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)
  exact hs.trans (le_trans (Nat.le_mul_of_pos_right _ hd) hb)

/-- Literal scheduled summary-box cardinality with no rank/cardinality oracle. -/
theorem scheduled_summary_bound (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (w : ℕ)
    (hg : sourceLayoutGuard n w)
    [NeZero (scheduledGroupCount (Nat.clog 2 n))]
    (hocc : ∀ v,(Finset.univ.filter
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2=v)).card≤2)
    (hscope : ∀ e,arity e≤w) (hM : (∑ e,arity e)=2*n)
    (t : Fin (scheduledPointCount (Nat.clog 2 n))) :
    let d := indexedDesign (r:=scheduledGroupCount (Nat.clog 2 n)) arity coordinate
      (scheduledEpsilon n) (scheduledDegree (Nat.clog 2 n)) 2 t
    SemiprimePacketArrayExecution.summaryCount d.r d.h d.m d.W≤
      (2*n*measurementBound 2 (scheduledPointCount (Nat.clog 2 n))
        (scheduledDegree (Nat.clog 2 n))+1)^
        (4*n/(scheduledGroupCount (Nat.clog 2 n)*Nat.clog 2 n)) :=
  summary_le_floor (r:=scheduledGroupCount (Nat.clog 2 n)) arity coordinate (scheduledEpsilon n) (scheduledDegree (Nat.clog 2 n)) 2
    (scheduledGroupCount (Nat.clog 2 n)*Nat.clog 2 n) (4*n) t
    (scheduled_den_pos w hg) (scheduled_rank_budget arity coordinate w hg hocc hscope hM t)

/-- The CLOSED parameter-only floor envelope itself has the scheduled binary
log bound, not merely the actual summary cardinality below that envelope. -/
theorem summary_envelope_log (hν : 64≤Nat.clog 2 (Nat.clog 2 n)) :
    Real.log ((sourceSignatureBase n ^
      (4*n/(scheduledGroupCount (Nat.clog 2 n)*Nat.clog 2 n)) : ℕ):ℝ)≤
      (48*(n:ℝ)*(Nat.clog 2 (Nat.clog 2 n):ℝ)^2/Real.sqrt (Nat.clog 2 n:ℝ))*Real.log 2 := by
  rw [Nat.cast_pow,Real.log_pow]
  exact source_summary_binary_rate hν (Nat.div_mul_le_self (4*n) _)

/-- The actual encoded physical design, with its original acquired input caches. -/
abbrev physicalDesign (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R B : ℕ) (t : Fin Q) : SemiprimeNodeArrayExecution.RuntimeDesign n F :=
  (SemiprimePaidRuntimeDesign.build
    (SemiprimePaidRawAcquisition.raw (n:=n) (F:=F) (SemiprimePaidRawAcquisition.acquire arity coordinate
      (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps R B).value t)
    (SemiprimePaidRawAcquisition.reader (n:=n) (SemiprimePaidRawAcquisition.acquire arity coordinate
      (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps R B).value t)
    (SemiprimePaidMeasurementBound.bits B Q R)).value

/-- The physical design transfer uses only actual original occurrence/numerical guards. -/
theorem physical_eq (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R B : ℕ)
    (howner : ∀ v,(Finset.univ.filter
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2=v)).card≤B)
    (hQ : 1≤Q) (hAQ : Subexp.TailInterval.intervalStart r Q R≤Q) (t : Fin Q) :
    physicalDesign (r:=r) arity coordinate eps R B t=indexedDesign (r:=r) arity coordinate eps R B t :=
  SemiprimeFullSetupCounter.physical_design (r:=r) (Q:=Q) arity coordinate eps R B howner hQ hAQ t

end RiemannGaussian.SemiprimeIndexedDesignResources
