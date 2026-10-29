/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMaterializedSourceCache

/-! # Materialized packing addresses
Labels, all type buckets and their minimum size are acquired once. Each output
address is computed by actual finite scans of those cached values. The ledger
retains the label producer's cost and the complete register comparisons; it is
a scalar/list ledger, not a primitive bit clock.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeMaterializedPacking
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes Subexp.ConstructivePacking
open SemiprimeMaterializedSourceUniversal
variable {I : Type} [DecidableEq I] {r Q : ℕ}

/-- Acquire each callback once and retain all callback/list costs. -/
def mapPaid {α β : Type*} (f : α → Run β) : List α → Run (List β)
  | [] => ⟨[],1⟩
  | a::as => let v := f a; let tail := mapPaid f as
            ⟨v.value::tail.value,v.work+tail.work+2⟩

theorem mapPaid_value {α β : Type*} (f : α → Run β) (xs : List α) :
    (mapPaid f xs).value=xs.map (fun x => (f x).value) := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [mapPaid,ih,List.map_cons]

theorem mapPaid_work {α β : Type*} (f : α → Run β) (xs : List α) (B : ℕ)
    (h : ∀ x∈xs, (f x).work≤B) : (mapPaid f xs).work≤xs.length*(B+2)+1 := by
  induction xs with
  | nil => simp [mapPaid]
  | cons a as ih =>
      have ha := h a (by simp)
      have ht := ih (fun x hx => h x (by simp [hx]))
      simp only [mapPaid,List.length_cons]
      nlinarith

/-- One cached label for every original incidence. -/
def labels (producer : I → Run (UniversalType r Q 1)) (vertices : List I) :
    Run (List (I × UniversalType r Q 1)) :=
  mapPaid (fun i => let v := producer i; ⟨(i,v.value),v.work+1⟩) vertices

omit [DecidableEq I] in
theorem labels_value (producer : I → Run (UniversalType r Q 1)) (vertices : List I) :
    (labels producer vertices).value=vertices.map (fun i => (i,(producer i).value)) :=
  mapPaid_value _ _

/-- Scan materialized labels, including every complete universal-word comparison. -/
def bucket (u : UniversalType r Q 1) : List (I × UniversalType r Q 1) → Run (List I)
  | [] => ⟨[],1⟩
  | (i,v)::vs =>
      let eq := SemiprimeMaterializedSourceCache.same v u
      let tail := bucket u vs
      ⟨if eq.value then i::tail.value else tail.value,eq.work+tail.work+3⟩

omit [DecidableEq I] in
theorem bucket_value (u : UniversalType r Q 1) (vertices : List I)
    (f : I → UniversalType r Q 1) :
    (bucket u (vertices.map (fun i => (i,f i)))).value=
      vertices.filter (fun i => decide (f i=u)) := by
  induction vertices with
  | nil => rfl
  | cons i is ih =>
      simp only [List.map_cons,bucket,ih,List.filter_cons]
      simp only [SemiprimeMaterializedSourceCache.same_correct,decide_eq_true_eq]

omit [DecidableEq I] in
theorem bucket_work (u : UniversalType r Q 1) (ls : List (I × UniversalType r Q 1)) :
    (bucket u ls).work=ls.length*(7*Q+4)+1 := by
  induction ls with
  | nil => simp [bucket]
  | cons a as ih =>
      rcases a with ⟨i,v⟩
      simp only [bucket,SemiprimeMaterializedSourceCache.same_work,ih,List.length_cons]
      ring

/-- Minimum bucket size, with the length of each materialized bucket charged. -/
def minimum (cap : ℕ) : List (List I) → Run ℕ
  | [] => ⟨cap,1⟩
  | b::bs => let tail := minimum cap bs
             ⟨min b.length tail.value,tail.work+b.length+3⟩

omit [DecidableEq I] in
theorem minimum_value (P : PackingData I (UniversalType r Q 1))
    (keys : List (UniversalType r Q 1)) :
    (minimum P.vertices.values.length (keys.map P.bucket)).value=P.minCount keys := by
  induction keys with
  | nil => rfl
  | cons u us ih => simp only [List.map_cons,minimum,ih,PackingData.minCount]

omit [DecidableEq I] in
theorem minimum_work (cap : ℕ) (bs : List (List I)) (M : ℕ)
    (h : ∀ b∈bs, b.length≤M) : (minimum cap bs).work≤bs.length*(M+3)+1 := by
  induction bs with
  | nil => simp [minimum]
  | cons b bs ih =>
      have hb := h b (by simp)
      have ht := ih (fun x hx => h x (by simp [hx]))
      simp only [minimum,List.length_cons]
      nlinarith

/-- The literal first position in a bucket, computed by a finite incidence scan. -/
def position (i : I) : List I → Run ℕ
  | [] => ⟨0,1⟩
  | j::js => if i=j then ⟨0,3⟩ else
      let tail := position i js; ⟨tail.value+1,tail.work+3⟩

theorem position_value (i : I) (xs : List I) : (position i xs).value=xs.idxOf i := by
  induction xs with
  | nil => rfl
  | cons j js ih => by_cases h : i=j <;> simp [position,h,ih,eq_comm]

theorem position_work (i : I) (xs : List I) : (position i xs).work≤3*xs.length+1 := by
  induction xs with
  | nil => simp [position]
  | cons j js ih =>
      simp only [position,List.length_cons]
      split_ifs <;> dsimp only <;> omega

/-- Compute one address from cached bucket data and the cached common block count. -/
def place (keys : List (UniversalType r Q 1)) (bs : List (List I)) (blocks : ℕ)
    (iv : I × UniversalType r Q 1) : Run (I × Option (ℕ × UniversalType r Q 1)) :=
  let found := SemiprimeMaterializedSourceCache.lookup iv.2 keys bs
  let pos := position iv.1 (found.value.getD [])
  ⟨(iv.1,if pos.value<blocks then some (pos.value,iv.2) else none),found.work+pos.work+4⟩

theorem place_value (P : PackingData I (UniversalType r Q 1)) (i : I) :
    (place P.types.values (P.types.values.map P.bucket) P.blockCount (i,P.label i)).value=
      (i,(P.lookup i).map (fun a => (a.1.val,a.2))) := by
  have hf := SemiprimeMaterializedSourceCache.lookup_map (P.label i)
    P.types.values P.bucket (P.types.complete _)
  simp only [place,hf,Option.getD_some,position_value,PackingData.lookup]
  split_ifs <;> rfl

theorem place_work (P : PackingData I (UniversalType r Q 1)) (i : I) :
    (place P.types.values (P.types.values.map P.bucket) P.blockCount (i,P.label i)).work≤
      P.types.values.length*(7*Q+4)+3*P.vertices.values.length+6 := by
  have hf := SemiprimeMaterializedSourceCache.lookup_map (P.label i)
    P.types.values P.bucket (P.types.complete _)
  have hb := P.bucket_length_le (P.label i)
  have hl := SemiprimeMaterializedSourceCache.lookup_work (P.label i)
    P.types.values (P.types.values.map P.bucket)
  have hp := position_work i (P.bucket (P.label i))
  simp only [place,hf,Option.getD_some]
  omega

/-- Complete acquisition from finite inputs and an explicitly paid label program.
Labels and buckets are computed once, outside every subsequent address lookup. -/
def acquire (vertices : List I) (keys : List (UniversalType r Q 1))
    (producer : I → Run (UniversalType r Q 1)) :
    Run (List (I × Option (ℕ × UniversalType r Q 1))) :=
  let ls := labels producer vertices
  let bs := mapPaid (fun u => bucket u ls.value) keys
  let blocks := minimum vertices.length bs.value
  let output := mapPaid (place keys bs.value blocks.value) ls.value
  ⟨output.value,ls.work+bs.work+blocks.work+output.work+vertices.length+4⟩

/-- The addresses agree exactly, including original bucket order and leftovers. -/
theorem acquire_value (P : PackingData I (UniversalType r Q 1))
    (producer : I → Run (UniversalType r Q 1)) (h : ∀ i, (producer i).value=P.label i) :
    (acquire P.vertices.values P.types.values producer).value=
      P.vertices.values.map (fun i => (i,(P.lookup i).map (fun a => (a.1.val,a.2)))) := by
  have hl : (labels producer P.vertices.values).value=
      P.vertices.values.map (fun i => (i,P.label i)) := by simp only [labels_value,h]
  have hb : (mapPaid (fun u => bucket u (labels producer P.vertices.values).value)
      P.types.values).value=P.types.values.map P.bucket := by
    simp only [mapPaid_value,hl,bucket_value]
    rfl
  unfold acquire
  dsimp only
  rw [hb,minimum_value]
  change (mapPaid (place P.types.values (P.types.values.map P.bucket) P.blockCount)
    (labels producer P.vertices.values).value).value=_
  rw [hl,mapPaid_value,List.map_map]
  simp only [Function.comp_def,place_value]

/-- All original packing scans have an explicit fixed polynomial ledger.
The actual label producer's work is retained as B; it is never silently free. -/
theorem acquire_work (P : PackingData I (UniversalType r Q 1))
    (producer : I → Run (UniversalType r Q 1)) (h : ∀ i, (producer i).value=P.label i)
    (B : ℕ) (hw : ∀ i, (producer i).work≤B) :
    (acquire P.vertices.values P.types.values producer).work≤
      P.vertices.values.length*(B+3)+1+
      P.types.values.length*(P.vertices.values.length*(7*Q+4)+3)+1+
      P.types.values.length*(P.vertices.values.length+3)+1+
      P.vertices.values.length*(P.types.values.length*(7*Q+4)+3*P.vertices.values.length+8)+1+
      P.vertices.values.length+4 := by
  have hl : (labels producer P.vertices.values).value=
      P.vertices.values.map (fun i => (i,P.label i)) := by simp only [labels_value,h]
  have hb : (mapPaid (fun u => bucket u (labels producer P.vertices.values).value)
      P.types.values).value=P.types.values.map P.bucket := by
    simp only [mapPaid_value,hl,bucket_value]
    rfl
  have wl := mapPaid_work (fun i => let v := producer i; (⟨(i,v.value),v.work+1⟩ :
    Run (I × UniversalType r Q 1))) P.vertices.values (B+1)
      (fun i _ => Nat.add_le_add_right (hw i) 1)
  have wb := mapPaid_work (fun u => bucket u (labels producer P.vertices.values).value)
    P.types.values (P.vertices.values.length*(7*Q+4)+1)
      (by intro u _; simp only [bucket_work,hl,List.length_map]; rfl)
  have wm := minimum_work P.vertices.values.length (P.types.values.map P.bucket)
    P.vertices.values.length (by
      intro b hb
      obtain ⟨u,_,rfl⟩ := List.mem_map.mp hb
      exact P.bucket_length_le u)
  have wo := mapPaid_work (place P.types.values (P.types.values.map P.bucket) P.blockCount)
    (P.vertices.values.map (fun i => (i,P.label i)))
    (P.types.values.length*(7*Q+4)+3*P.vertices.values.length+6) (by
      intro iv hv
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hv
      exact place_work P i)
  simp only [List.length_map] at wm wo
  change (labels producer P.vertices.values).work≤_ at wl
  unfold acquire
  dsimp only
  rw [hb,minimum_value,hl]
  rw [hl] at wb
  simp only [PackingData.blockCount] at wo
  nlinarith

end RiemannGaussian.SemiprimeMaterializedPacking
