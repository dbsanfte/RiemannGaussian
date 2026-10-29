/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceArrayProgramIR

/-! # Actual cached array addition and convolution instruction blocks -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace RiemannGaussian.SemiprimeSourceArrayProgramBlocks
open scoped BigOperators
open SemiprimeSourceArrayProgramIR SemiprimeRationalBits

/-- Independent scalar instructions use only the pre-block cached arrays. -/
theorem independent_value (code : List Instruction) (start k : ℕ) (env : ℕ → ℚ)
    (hc : ∀ i∈code,i.left<start ∧ i.right<start) (hk : k<code.length) :
    evaluate code start env (start+k)=(code[k]'hk).value env := by
  induction code generalizing start k env with
  | nil => simp at hk
  | cons i code ih =>
    have hi := hc i List.mem_cons_self
    cases k with
    | zero =>
      change evaluate code (start+1) (Function.update env start (i.value env)) start=i.value env
      rw [evaluate_old _ (start+1) start _ (by omega),Function.update_same]
    | succ k =>
      have ht : ∀ j∈code,j.left<start+1 ∧ j.right<start+1 := by
        intro j hj
        have h := hc j (List.mem_cons_of_mem _ hj)
        exact ⟨by omega,by omega⟩
      have hki : k<code.length := by simp only [List.length_cons] at hk; omega
      have hh := ih (start+1) k (Function.update env start (i.value env)) ht hki
      change evaluate code (start+1) (Function.update env start (i.value env)) (start+(k+1))=_
      rw [show start+(k+1)=start+1+k by omega,hh]
      have hj := hc (code[k]) (List.mem_cons_of_mem _ (List.getElem_mem hki))
      simp only [List.getElem_cons_succ,Instruction.value,
        Function.update_of_ne (by omega : (code[k]).left≠start),
        Function.update_of_ne (by omega : (code[k]).right≠start)]

/-- Emit one scalar addition for every coefficient, retaining both child arrays. -/
def addCode (J : ℕ) (a b : ℕ → ℕ) : List Instruction :=
  (List.range J).map (fun k => ⟨.add,a k,b k⟩)

/-- Exactly J physical additions are generated. -/
theorem addCode_length (J : ℕ) (a b : ℕ → ℕ) : (addCode J a b).length=J := by simp [addCode]

/-- Actual array-add block semantics, with initialized cached operand IDs. -/
theorem addCode_correct (J start k : ℕ) (a b : ℕ → ℕ) (env : ℕ → ℚ)
    (ha : ∀ i<J,a i<start) (hb : ∀ i<J,b i<start) (hk : k<J) :
    evaluate (addCode J a b) start env (start+k)=env (a k)+env (b k) := by
  have hh := independent_value (addCode J a b) start k env (by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    exact ⟨ha j (List.mem_range.mp hj),hb j (List.mem_range.mp hj)⟩)
    (by simpa only [addCode_length] using hk)
  simpa [addCode,Instruction.value,Operation.value,hk] using hh

/-- Independent array additions are well formed at every emitted position. -/
theorem addCode_wellFormed (J start : ℕ) (a b : ℕ → ℕ)
    (ha : ∀ i<J,a i<start) (hb : ∀ i<J,b i<start) :
    WellFormed start (addCode J a b) := by
  have helper : ∀ (xs : List Instruction) (next : ℕ),start≤next →
      (∀ i∈xs,i.left<start ∧ i.right<start) → WellFormed next xs := by
    intro xs
    induction xs with
    | nil => intro _ _ _; trivial
    | cons i xs ih =>
      intro next hn hc
      have hi := hc i List.mem_cons_self
      exact ⟨by omega,by omega,ih (next+1) (by omega) (fun j hj => hc j (List.mem_cons_of_mem _ hj))⟩
  apply helper _ start le_rfl
  intro i hi
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hi
  exact ⟨ha k (List.mem_range.mp hk),hb k (List.mem_range.mp hk)⟩

/-- Convolution computes each coefficient once, caching all scalar products and prefix sums. -/
def mulCode (zeroId start : ℕ) (a b : ℕ → ℕ) : ℕ → List Instruction
  | 0 => []
  | J+1 =>
      let previous := mulCode zeroId start a b J
      previous ++ dotCode zeroId (start+previous.length) J a b (J+1)

/-- The original quadratic convolution has exactly J(J+1) scalar instructions. -/
theorem mulCode_length (zeroId start : ℕ) (a b : ℕ → ℕ) (J : ℕ) :
    (mulCode zeroId start a b J).length=J*(J+1) := by
  induction J with
  | zero => rfl
  | succ J ih => simp only [mulCode,List.length_append,dotCode_length,ih];ring

/-- Stable final ID of one cached convolution coefficient. -/
def mulResult (start k : ℕ) : ℕ := start+(k+1)*(k+2)-1

/-- Every selected coefficient lies below the post-block frontier. -/
theorem mulResult_lt (start J k : ℕ) (hk : k<J) : mulResult start k<start+J*(J+1) := by
  have hp := Nat.mul_le_mul (show k+1≤J by omega) (show k+2≤J+1 by omega)
  have hpos : 0<(k+1)*(k+2) := Nat.mul_pos (by omega) (by omega)
  unfold mulResult
  omega

/-- Actual full convolution-block coefficient semantics. -/
theorem mulCode_correct (zeroId start J k : ℕ) (a b : ℕ → ℕ) (env : ℕ → ℚ)
    (hz : zeroId<start) (he : env zeroId=0)
    (ha : ∀ i<J,a i<start) (hb : ∀ i<J,b i<start) (hk : k<J) :
    evaluate (mulCode zeroId start a b J) start env (mulResult start k)=
      ∑ i∈Finset.range (k+1),env (a i)*env (b (k-i)) := by
  induction J with
  | zero => omega
  | succ J ih =>
    rw [mulCode,evaluate_append]
    by_cases hkj : k=J
    · subst k
      let previous := mulCode zeroId start a b J
      let next := start+previous.length
      let e := evaluate previous start env
      have hz' : zeroId<next := by dsimp [next];omega
      have he' : e zeroId=0 := (evaluate_old previous start zeroId env hz).trans he
      have hA : ∀ i<J+1,a i<next := fun i hi => lt_of_lt_of_le (ha i hi) (by dsimp [next];omega)
      have hB : ∀ i<J+1,b (J-i)<next := by
        intro i _
        exact lt_of_lt_of_le (hb (J-i) (by omega)) (by dsimp [next];omega)
      have hd := dotCode_correct zeroId next J (J+1) a b e hz' he' hA hB
      have hr : accumulator zeroId next (J+1)=mulResult start J := by
        simp only [accumulator,show J+1≠0 by omega,ite_false,next,previous,mulCode_length,mulResult]
        congr 1
        ring
      rw [hr] at hd
      change evaluate (dotCode zeroId next J a b (J+1)) next e (mulResult start J)=_
      rw [hd]
      apply Finset.sum_congr rfl
      intro i hi
      have hii := Finset.mem_range.mp hi
      rw [show e (a i)=env (a i) from evaluate_old previous start _ env (ha i hii),
        show e (b (J-i))=env (b (J-i)) from evaluate_old previous start _ env (hb _ (by omega))]
    · have hkJ : k<J := by omega
      have hresult := mulResult_lt start J k hkJ
      rw [← mulCode_length zeroId start a b J] at hresult
      rw [evaluate_old _ _ _ _ hresult]
      exact ih (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega)) hkJ

/-- The full cached convolution uses only initialized operands and earlier accumulators. -/
theorem mulCode_wellFormed (zeroId start J : ℕ) (a b : ℕ → ℕ)
    (hz : zeroId<start) (ha : ∀ i<J,a i<start) (hb : ∀ i<J,b i<start) :
    WellFormed start (mulCode zeroId start a b J) := by
  induction J with
  | zero => trivial
  | succ J ih =>
    rw [mulCode,wellFormed_append]
    refine ⟨ih (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega)),?_⟩
    apply dotCode_wellFormed
    · omega
    · intro i hi; exact lt_of_lt_of_le (ha i hi) (by omega)
    · intro i _; exact lt_of_lt_of_le (hb (J-i) (by omega)) (by omega)

end RiemannGaussian.SemiprimeSourceArrayProgramBlocks
