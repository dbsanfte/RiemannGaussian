/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMaterializedWords

/-! # Source-word search and cached assignment reads
The search driver uses the original four-index collision supports and preserves
the exact original deterministic choices. Its terminal score producer remains
explicit, with both semantic and work contracts. No terminal cost is set to one
or silently treated as bit work. Returned word lists are actual finite data.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeMaterializedWordSearch
open OAI.Algorithms.SubexponentialSAT
open LocalExpectation MulticolorTypes SqrtLog
open SemiprimeMaterializedWords

variable {I V E : Type*} [DecidableEq V] [DecidableEq E] {r Q : ℕ}

/-- Original collision/head supports as literal index lists, retaining harmless duplicates. -/
def supportCodes (owner : I → V) (factor : I → E) (indices : List (V ⊕ E)) :
    Packing.ScoreTerm I V Q → List ℕ
  | .inl (i,j) => [indexCode indices (.inl (owner i)),indexCode indices (.inr (factor i)),
      indexCode indices (.inl (owner j)),indexCode indices (.inr (factor j))]
  | .inr (_,v,w) => [indexCode indices (.inl v),indexCode indices (.inl w)]

theorem supportCodes_length (owner : I → V) (factor : I → E) (indices : List (V ⊕ E))
    (z : Packing.ScoreTerm I V Q) : (supportCodes owner factor indices z).length≤4 := by
  cases z <;> simp [supportCodes]

theorem supportCodes_set (owner : I → V) (factor : I → E) (indices : List (V ⊕ E))
    (z : Packing.ScoreTerm I V Q) :
    (supportCodes owner factor indices z).toFinset=Packing.numberedScoreSupport owner factor indices z := by
  cases z <;> ext j <;> simp [supportCodes,Packing.numberedScoreSupport,Packing.scoreSupport]

/-- Complete original-source search with an explicitly paid elementary score program. -/
def computedList (owner : I → V) (factor : I → E)
    (a : Word r Q) (tail : List (Word r Q)) (terms : List (Packing.ScoreTerm I V Q))
    (indices : List (V ⊕ E))
    (producer : Packing.ScoreTerm I V Q → (ℕ → Word r Q) → Run ℚ) (offset : ℚ) :
    Run (List (Word r Q)) :=
  search a tail terms (supportCodes owner factor indices) producer offset indices.length

/-- Actual computed source assignment, not supplied optimal labels. -/
theorem computedList_value [Fintype I] [Fintype V]
    (owner : I → V) (factor : I → E)
    (a : Word r Q) (tail : List (Word r Q)) (terms : List (Packing.ScoreTerm I V Q))
    (indices : List (V ⊕ E)) (x y : ℚ)
    (producer : Packing.ScoreTerm I V Q → (ℕ → Word r Q) → Run ℚ)
    (hp : ∀ z omega, (producer z omega).value=Packing.numberedScoreTerm owner factor indices x y z omega) :
    (fun i => decode a (computedList owner factor a tail terms indices producer
      (Packing.scoreOffset (I := I) (V := V) (r := r) (Q := Q) x y)).value (indexCode indices i))=
      Packing.computedWords owner factor a tail terms indices x y := by
  simp only [computedList,search_value,supportCodes_set,hp,Packing.computedWords]

/-- Whole-driver work is polynomial in the paid source alphabet and the actual
terminal-program budget. Word/code descriptor acquisition is a separate input. -/
theorem computedList_work (owner : I → V) (factor : I → E)
    (a : Word r Q) (tail : List (Word r Q)) (terms : List (Packing.ScoreTerm I V Q))
    (indices : List (V ⊕ E))
    (producer : Packing.ScoreTerm I V Q → (ℕ → Word r Q) → Run ℚ) (offset : ℚ)
    (B : ℕ) (hp : ∀ z omega, (producer z omega).work≤B) :
    (computedList owner factor a tail terms indices producer offset).work≤
      indices.length*(tail.length*(2*evaluatorBudget (a::tail).length terms.length indices.length B 4+3)+4)+1 :=
  search_work a tail terms (supportCodes owner factor indices) producer offset B 4 indices.length hp
    (supportCodes_length owner factor indices)

/-- Read one cached chosen label by an actual sequential list scan.
The reverse-prefix convention agrees with the published decoder. -/
def readRun {W : Type*} (default : W) : List W → ℕ → Run W
  | [], _ => ⟨default,1⟩
  | a::as, i =>
      if i=as.length then ⟨a,as.length+3⟩ else
      let rest := readRun default as i
      ⟨rest.value,rest.work+as.length+3⟩

theorem readRun_value {W : Type*} (default : W) (xs : List W) (i : ℕ) :
    (readRun default xs i).value=decode default xs i := by
  induction xs with
  | nil => rfl
  | cons a as ih => by_cases h : i=as.length <;> simp [readRun,decode,h,ih]

/-- Recomputing list lengths is paid rather than assumed cached. -/
theorem readRun_work {W : Type*} (default : W) (xs : List W) (i : ℕ) :
    (readRun default xs i).work≤3*(xs.length+1)^2 := by
  induction xs with
  | nil => simp [readRun]
  | cons a as ih =>
      by_cases h : i=as.length <;> simp only [readRun,h,ite_true,ite_false,List.length_cons] <;> nlinarith

/-- Obtain the selected label from the actual computed list and charge both stages. -/
def searchRead (owner : I → V) (factor : I → E)
    (a : Word r Q) (tail : List (Word r Q)) (terms : List (Packing.ScoreTerm I V Q))
    (indices : List (V ⊕ E))
    (producer : Packing.ScoreTerm I V Q → (ℕ → Word r Q) → Run ℚ) (offset : ℚ) (i : ℕ) :
    Run (Word r Q) :=
  let labels := computedList owner factor a tail terms indices producer offset
  let result := readRun a labels.value i
  ⟨result.value,labels.work+result.work⟩

/-- Exact output-list size at every sequential search prefix. -/
theorem assign_length {W : Type*} (a : W) (tail : List W)
    (evaluator : ℕ → List W → Run ℚ) (n : ℕ) (fixed : List W) :
    (assign a tail evaluator n fixed).value.length=n+fixed.length := by
  induction n generalizing fixed with
  | zero => simp [assign]
  | succ n ih => simp only [assign,ih,List.length_cons]; omega

theorem computedList_length (owner : I → V) (factor : I → E)
    (a : Word r Q) (tail : List (Word r Q)) (terms : List (Packing.ScoreTerm I V Q))
    (indices : List (V ⊕ E))
    (producer : Packing.ScoreTerm I V Q → (ℕ → Word r Q) → Run ℚ) (offset : ℚ) :
    (computedList owner factor a tail terms indices producer offset).value.length=indices.length := by
  simp only [computedList,search,assign_length,List.length_nil,Nat.add_zero]

theorem searchRead_work (owner : I → V) (factor : I → E)
    (a : Word r Q) (tail : List (Word r Q)) (terms : List (Packing.ScoreTerm I V Q))
    (indices : List (V ⊕ E))
    (producer : Packing.ScoreTerm I V Q → (ℕ → Word r Q) → Run ℚ) (offset : ℚ) (i B : ℕ)
    (hp : ∀ z omega, (producer z omega).work≤B) :
    (searchRead owner factor a tail terms indices producer offset i).work≤
      indices.length*(tail.length*(2*evaluatorBudget (a::tail).length terms.length indices.length B 4+3)+4)+1+
      3*(indices.length+1)^2 := by
  have h := computedList_work owner factor a tail terms indices producer offset B hp
  have hr := readRun_work a (computedList owner factor a tail terms indices producer offset).value i
  rw [computedList_length] at hr
  exact Nat.add_le_add h hr

end RiemannGaussian.SemiprimeMaterializedWordSearch
