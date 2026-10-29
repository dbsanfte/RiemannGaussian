/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePaidConstraintRows
import RiemannGaussian.SemiprimePaidPackingSnapshot

/-! # Acquiring the complete finite integer constraint family
All row names and all original-coordinate entries are explicitly materialized.
The universal numerator and packing tables are acquired once before this loop.
The result is a scalar/list work ledger, not a primitive bit clock.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimePaidConstraintAcquisition
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes Subexp.ConstructivePacking
open SemiprimeMaterializedSourceUniversal
open SemiprimePaidConstraintRows (Index encode source source_value source_work)
variable {I : Type} {n r Q : ℕ}

/-- All complete-block row names in ascending block and original alphabet order. -/
def blockNames (keys : List (UniversalType r Q 1)) : ℕ → Run (List (Index I r Q))
  | 0 => ⟨[],1⟩
  | b+1 =>
      let prev := blockNames keys b
      let next := collect (fun u => (⟨Sum.inl (b,u),2⟩ : Run (Index I r Q))) keys
      ⟨prev.value++next.value,prev.work+next.work+prev.value.length+3⟩

theorem blockNames_value (keys : List (UniversalType r Q 1)) (b : ℕ) :
    (blockNames (I:=I) keys b).value=
      (List.range b).flatMap (fun k => keys.map (fun u => Sum.inl (k,u))) := by
  induction b with
  | zero => rfl
  | succ b ih => simp [blockNames,ih,collect_value,List.range_succ]

theorem blockNames_length (keys : List (UniversalType r Q 1)) (b : ℕ) :
    (blockNames (I:=I) keys b).value.length=b*keys.length := by
  rw [blockNames_value]
  simp [List.length_flatMap,List.sum_replicate]

theorem blockNames_work (keys : List (UniversalType r Q 1)) (b : ℕ) :
    (blockNames (I:=I) keys b).work≤10*(b+1)^2*(keys.length+1) := by
  induction b with
  | zero => simp [blockNames]; omega
  | succ b ih =>
      have hc := collect_work (fun u => (⟨Sum.inl (b,u),2⟩ : Run (Index I r Q))) keys 2
        (by intro u _; rfl)
      simp only [blockNames,blockNames_length]
      nlinarith

/-- Append every original incidence as a potential leftover row. -/
def names (keys : List (UniversalType r Q 1)) (blocks : ℕ) (is : List I) :
    Run (List (Index I r Q)) :=
  let bs := blockNames keys blocks
  let tail := collect (fun i => (⟨Sum.inr i,1⟩ : Run (Index I r Q))) is
  ⟨bs.value++tail.value,bs.work+tail.work+bs.value.length+2⟩

theorem names_value (keys : List (UniversalType r Q 1)) (blocks : ℕ) (is : List I) :
    (names keys blocks is).value=
      (List.range blocks).flatMap (fun b => keys.map (fun u => Sum.inl (b,u)))++is.map Sum.inr := by
  simp only [names,blockNames_value,collect_value]

theorem names_length (keys : List (UniversalType r Q 1)) (blocks : ℕ) (is : List I) :
    (names keys blocks is).value.length=blocks*keys.length+is.length := by
  simp only [names,List.length_append,blockNames_length,collect_value,List.length_map]

/-- The acquired row ordering is precisely the old padded enumeration ordering. -/
theorem names_packing (P : PackingData I (UniversalType r Q 1)) :
    (names P.types.values P.blockCount P.vertices.values).value=
      (SemiprimePaddedBlockExecution.indices P).values.map (encode P) := by
  rw [names_value]
  simp only [SemiprimePaddedBlockExecution.indices,SemiprimeFiniteEnumerations.sum,
    SemiprimeFiniteEnumerations.prod,SemiprimeFiniteEnumerations.fin,List.map_append,
    List.map_map,Function.comp_def,encode,List.product,List.map_flatMap]
  rw [← List.map_coe_finRange P.blockCount,List.flatMap_map]

theorem names_work (keys : List (UniversalType r Q 1)) (blocks : ℕ) (is : List I) :
    (names keys blocks is).work≤
      10*(blocks+1)^2*(keys.length+1)+3*is.length+blocks*keys.length+3 := by
  have hb := blockNames_work (I:=I) keys blocks
  have ht := collect_work (fun i => (⟨Sum.inr i,1⟩ : Run (Index I r Q))) is 1
    (by intro i _; rfl)
  simp only [names,blockNames_length]
  omega

variable [DecidableEq I]

/-- One dense original-coordinate row, acquired by literal finite callback calls. -/
def row (is : List I) (owner : I → Fin n)
    (addresses : SemiprimeMaterializedSourcePullback.Addresses I r Q)
    (producer : I → Run (UniversalType r Q 1))
    (cache : SemiprimePaidConstraintCache.Cache (r:=r) (Q:=Q))
    (t : Fin Q) (g : Fin r) (j : Index I r Q) : Run (List ℤ) :=
  let out := collect (source is owner addresses producer cache t g j) (List.finRange n)
  ⟨out.value,out.work+2*n+1⟩

/-- The complete Q-by-r-by-p-by-n integer family from already acquired finite data. -/
def table (is : List I) (owner : I → Fin n)
    (addresses : SemiprimeMaterializedSourcePullback.Addresses I r Q)
    (producer : I → Run (UniversalType r Q 1))
    (cache : SemiprimePaidConstraintCache.Cache (r:=r) (Q:=Q))
    (js : List (Index I r Q)) : Run (List (List (List (List ℤ)))) :=
  let out := collect (fun t => collect (fun g => collect
    (row is owner addresses producer cache t g) js) (List.finRange r)) (List.finRange Q)
  ⟨out.value,out.work+Q*(2*r+1)+2*Q+1⟩

theorem table_value (is : List I) (owner : I → Fin n)
    (addresses : SemiprimeMaterializedSourcePullback.Addresses I r Q)
    (producer : I → Run (UniversalType r Q 1))
    (cache : SemiprimePaidConstraintCache.Cache (r:=r) (Q:=Q)) (js : List (Index I r Q)) :
    (table is owner addresses producer cache js).value=
      (List.finRange Q).map (fun t => (List.finRange r).map (fun g =>
        js.map (fun j => (List.finRange n).map (fun v =>
          (source is owner addresses producer cache t g j v).value)))) := by
  simp only [table,row,collect_value]

/-- Complete acquired integer family and its literal original row names. -/
structure Family (I : Type) (r Q : ℕ) where
  /-- Original padded row names, in their exact source order. -/
  indices : List (Index I r Q)
  /-- Stored entries: node, head, original row, original variable. -/
  entries : List (List (List (List ℤ)))

/-- Actually acquire packing, numerators, row names and every integer entry. -/
def acquire (A R : ℕ) (is : List I) (owner : I → Fin n)
    (keys : List (UniversalType r Q 1)) (producer : I → Run (UniversalType r Q 1)) :
    Run (Family I r Q) :=
  let pack := SemiprimePaidPackingSnapshot.acquire is keys producer
  let cache := SemiprimePaidConstraintCache.acquire A R keys
  let js := names keys pack.value.blocks is
  let entries := table is owner pack.value.addresses producer cache.value js.value
  ⟨⟨js.value,entries.value⟩,pack.work+cache.work+js.work+entries.work+n+r+Q+4⟩

/-- Original integer entries are acquired in exactly the original padded row order. -/
theorem acquire_entries [Fintype I] (P : PackingData I (UniversalType r Q 1))
    (A R : ℕ) (owner : I → Fin n) (producer : I → Run (UniversalType r Q 1))
    (hp : ∀ i, (producer i).value=P.label i) :
    (acquire A R P.vertices.values owner P.types.values producer).value.entries=
      (List.finRange Q).map (fun t => (List.finRange r).map (fun g =>
        (SemiprimePaddedBlockExecution.indices P).values.map (fun j =>
          (List.finRange n).map (SemiprimePaddedBlockExecution.sourceRow P owner
            (fun u => u.head t) g (SemiprimeUniversalSourceExecution.constraint A R t g) j)))) := by
  unfold acquire
  dsimp only
  rw [SemiprimePaidPackingSnapshot.acquire_blocks P producer hp,
    SemiprimePaidPackingSnapshot.acquire_addresses P producer hp,names_packing,table_value]
  simp only [List.map_map,Function.comp_def,source_value P A R owner producer hp]

/-- Explicit polynomial for the already acquired integer-entry loop. -/
def tableBudget (M n D L B Q r p : ℕ) : ℕ :=
  Q*(r*(p*(n*(M*(3*L+B+9*Q+2*(D*(7*Q+4)+1)+29)+5)+4)+3)+3)+1+Q*(2*r+1)+2*Q+1

theorem table_work (A R : ℕ) (keys : List (UniversalType r Q 1))
    (is : List I) (owner : I → Fin n)
    (addresses : SemiprimeMaterializedSourcePullback.Addresses I r Q)
    (producer : I → Run (UniversalType r Q 1)) (B : ℕ)
    (hw : ∀ i, (producer i).work≤B) (js : List (Index I r Q)) :
    (table is owner addresses producer (SemiprimePaidConstraintCache.acquire A R keys).value js).work≤
      tableBudget is.length n keys.length addresses.length B Q r js.length := by
  let E := is.length*(3*addresses.length+B+9*Q+2*(keys.length*(7*Q+4)+1)+29)+1
  have hr (t : Fin Q) (g : Fin r) (j : Index I r Q) :
      (row is owner addresses producer (SemiprimePaidConstraintCache.acquire A R keys).value t g j).work≤
        n*(E+4)+2 := by
    have hc := collect_work (source is owner addresses producer
        (SemiprimePaidConstraintCache.acquire A R keys).value t g j) (List.finRange n) E
        (fun v _ => source_work A R keys is owner addresses producer B hw t g j v)
    simp only [List.length_finRange] at hc
    unfold row
    dsimp only
    nlinarith
  have hj (t : Fin Q) (g : Fin r) :
      (collect (row is owner addresses producer
        (SemiprimePaidConstraintCache.acquire A R keys).value t g) js).work≤
        js.length*(n*(E+4)+4)+1 := by
    exact collect_work _ _ _ (fun j _ => hr t g j)
  have hg (t : Fin Q) :
      (collect (fun g => collect (row is owner addresses producer
        (SemiprimePaidConstraintCache.acquire A R keys).value t g) js) (List.finRange r)).work≤
        r*(js.length*(n*(E+4)+4)+3)+1 := by
    simpa only [List.length_finRange] using collect_work _ (List.finRange r) _ (fun g _ => hj t g)
  have ht := collect_work _ (List.finRange Q) _ (fun t _ => hg t)
  simp only [List.length_finRange] at ht
  unfold table tableBudget
  dsimp only
  dsimp only [E] at ht
  norm_num only [Nat.add_assoc] at ht ⊢
  omega

/-- All setup and all entries; block count is an actual acquired dimension. -/
def budget (A R M n D B Q r blocks : ℕ) : ℕ :=
  SemiprimeMaterializedSourceAcquisition.packingBudget M D Q B+1+
  SemiprimeMaterializedSourceUniversal.tableBudget A R Q D+2*R+4+
  (10*(blocks+1)^2*(D+1)+3*M+blocks*D+3)+
  tableBudget M n D M B Q r (blocks*D+M)+n+r+Q+4

/-- The complete original integer family retains every setup and entry-loop report. -/
theorem acquire_work (P : PackingData I (UniversalType r Q 1)) (A R : ℕ)
    (owner : I → Fin n) (producer : I → Run (UniversalType r Q 1))
    (hp : ∀ i, (producer i).value=P.label i) (B : ℕ) (hw : ∀ i, (producer i).work≤B) :
    (acquire A R P.vertices.values owner P.types.values producer).work≤
      budget A R P.vertices.values.length n P.types.values.length B Q r P.blockCount := by
  have hpw := SemiprimePaidPackingSnapshot.acquire_work P producer hp B hw
  have hcw := SemiprimePaidConstraintCache.acquire_work A R P.types.values
  have hjw := names_work P.types.values P.blockCount P.vertices.values
  have htw := table_work A R P.types.values P.vertices.values owner
    (SemiprimePaidPackingSnapshot.acquire P.vertices.values P.types.values producer).value.addresses
    producer B hw (names P.types.values P.blockCount P.vertices.values).value
  have hl : (SemiprimePaidPackingSnapshot.acquire P.vertices.values P.types.values producer).value.addresses.length=
      P.vertices.values.length := by
    rw [SemiprimePaidPackingSnapshot.acquire_addresses P producer hp]
    exact List.length_map _
  rw [hl,names_length] at htw
  unfold acquire
  dsimp only
  rw [SemiprimePaidPackingSnapshot.acquire_blocks P producer hp]
  unfold budget
  omega

omit [DecidableEq I] in
/-- A minimum scan capped by the incidence count cannot create extra blocks. -/
theorem blocks_le (P : PackingData I (UniversalType r Q 1)) :
    P.blockCount≤P.vertices.values.length := by
  have h (keys : List (UniversalType r Q 1)) : P.minCount keys≤P.vertices.values.length := by
    induction keys with
    | nil => rfl
    | cons u us ih => exact (min_le_right _ _).trans ih
  exact h P.types.values

/-- A literal polynomial envelope for universal numerator setup. -/
def universalPolynomial (A R Q D : ℕ) : ℕ :=
  Q*(D*(D*(D*entryPolynomial Q R+2)+3)+3)+1+
    (A*(R+1)+A+R+R^2)+(2*A*(R+1)+R^2)+1

/-- A literal fixed polynomial after the actual universal alphabet pays subset expansion. -/
def polynomial (A R M n D B Q r : ℕ) : ℕ :=
  SemiprimeMaterializedSourceAcquisition.packingBudget M D Q B+1+
  universalPolynomial A R Q D+2*R+4+
  (10*(M+1)^2*(D+1)+3*M+M*D+3)+
  tableBudget M n D M B Q r (M*D+M)+n+r+Q+4

theorem budget_polynomial (A R M n D B Q r blocks : ℕ)
    (hD : 2^(2*Q)≤D) (hb : blocks≤M) :
    budget A R M n D B Q r blocks≤polynomial A R M n D B Q r := by
  have he := entryBudget_polynomial Q R D hD
  unfold budget polynomial universalPolynomial SemiprimeMaterializedSourceUniversal.tableBudget tableBudget
  gcongr

/-- Native r≥2 closes the universal-expansion and block-count premises internally. -/
theorem acquire_work_native (P : PackingData I (UniversalType r Q 1)) (hr : 2≤r)
    (A R : ℕ) (owner : I → Fin n) (producer : I → Run (UniversalType r Q 1))
    (hp : ∀ i, (producer i).value=P.label i) (B : ℕ) (hw : ∀ i, (producer i).work≤B) :
    (acquire A R P.vertices.values owner P.types.values producer).work≤
      polynomial A R P.vertices.values.length n P.types.values.length B Q r := by
  apply (acquire_work P A R owner producer hp B hw).trans
  apply budget_polynomial
  · rw [P.types.length_eq_card,card_universalType]
    have h : 2^(2*Q)≤r^(2*Q) := Nat.pow_le_pow_left hr _
    simpa only [show Q*(1+1)=2*Q by omega] using h
  · exact blocks_le P

end RiemannGaussian.SemiprimePaidConstraintAcquisition
