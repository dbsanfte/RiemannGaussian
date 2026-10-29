/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceArrayProgramBlocks
import RiemannGaussian.SemiprimeSourceArrayProgramLowering
import RiemannGaussian.SemiprimeSourceCodeArrayHeight

/-! # Original-representation safety of emitted scalar array instructions
Every multiplication and intermediate convolution prefix is bounded from the
original operand representations. No intermediate Fits answer is an input.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeSourceArrayProgramSafe
open scoped BigOperators
open SemiprimeRationalBits SemiprimeJetArrayHeight
open SemiprimeSourceArrayProgramIR SemiprimeSourceArrayProgramBlocks
open SemiprimeSourceArrayProgramLowering

/-- Original common integer representatives derive physical output fits. -/
theorem fits_representation {x : ℚ} {d B W : ℕ} (hd : 0<d)
    (hx : Representation x d B) (hden : d<2^W) (hnum : B<2^W) : Fits x W := by
  have h := representation_reduced_bound hd hx
  exact ⟨h.2.trans_lt hnum,h.1.trans_lt hden⟩

/-- Independent instructions preserve original operands, and hence original-derived fits. -/
theorem independent_safe (W : ℕ) (code : List Instruction) (start : ℕ) (env : ℕ → ℚ)
    (hi : ∀ i∈code,i.left<start ∧ i.right<start)
    (hf : ∀ i∈code,Fits (i.value env) W) : Safe W code start env := by
  induction code generalizing start env with
  | nil => trivial
  | cons i code ih =>
    have hhead := hi i List.mem_cons_self
    refine ⟨hf i List.mem_cons_self,ih (start+1) (Function.update env start (i.value env)) ?_ ?_⟩
    · intro j hj
      have h := hi j (List.mem_cons_of_mem i hj)
      exact ⟨by omega,by omega⟩
    · intro j hj
      have h := hi j (List.mem_cons_of_mem i hj)
      simpa only [Instruction.value,Function.update_of_ne (by omega : j.left≠start),
        Function.update_of_ne (by omega : j.right≠start)] using hf j (List.mem_cons_of_mem i hj)

/-- All emitted array-add outputs fit from the original common denominator. -/
theorem addCode_safe (J start d B W : ℕ) (a b : ℕ → ℕ) (env : ℕ → ℚ)
    (hd : 0<d) (ha : ∀ k<J,a k<start) (hb : ∀ k<J,b k<start)
    (hA : ∀ k<J,Representation (env (a k)) d B)
    (hB : ∀ k<J,Representation (env (b k)) d B)
    (hden : d<2^W) (hnum : 2*B<2^W) : Safe W (addCode J a b) start env := by
  apply independent_safe
  · intro i hi
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hi
    exact ⟨ha k (List.mem_range.mp hk),hb k (List.mem_range.mp hk)⟩
  · intro i hi
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hi
    have h := representation_add (hA k (List.mem_range.mp hk)) (hB k (List.mem_range.mp hk))
    exact fits_representation hd h hden (by simpa only [two_mul] using hnum)

/-- Every product AND addition in the actual dot prefix fits from original
operand representations; the zero accumulator is an original register. -/
theorem dotCode_safe (zeroId start k len d B W : ℕ) (a b : ℕ → ℕ) (env : ℕ → ℚ)
    (hd : 0<d) (hz : zeroId<start) (he : env zeroId=0)
    (ha : ∀ i<len,a i<start) (hb : ∀ i<len,b (k-i)<start)
    (hA : ∀ i<len,Representation (env (a i)) d B)
    (hB : ∀ i<len,Representation (env (b (k-i))) d B)
    (hden : d*d<2^W) (hnum : len*(B*B)<2^W) :
    Safe W (dotCode zeroId start k a b len) start env := by
  induction len with
  | zero => trivial
  | succ len ih =>
    rw [dotCode,safe_append,dotCode_length]
    have hprevious := ih (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega))
      (fun i hi => hA i (by omega)) (fun i hi => hB i (by omega))
      (lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_succ len)) hnum)
    refine ⟨hprevious,?_⟩
    let e := evaluate (dotCode zeroId start k a b len) start env
    have ea : e (a len)=env (a len) := evaluate_old _ start _ env (ha len (by omega))
    have eb : e (b (k-len))=env (b (k-len)) := evaluate_old _ start _ env (hb len (by omega))
    have hprod : Representation (e (a len)*e (b (k-len))) (d*d) (B*B) := by
      rw [ea,eb]
      exact representation_mul (hA len (by omega)) (hB len (by omega))
    have hprefix := dotCode_correct zeroId start k len a b env hz he
      (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega))
    have hsum : Representation (e (accumulator zeroId start len)) (d*d) (len*(B*B)) := by
      change Representation (evaluate (dotCode zeroId start k a b len) start env _) _ _
      rw [hprefix]
      have h := representation_sum (Finset.range len) (fun i => env (a i)*env (b (k-i)))
        (d*d) (B*B) (fun i hi => representation_mul
          (hA i (by have := Finset.mem_range.mp hi;omega))
          (hB i (by have := Finset.mem_range.mp hi;omega)))
      simpa only [Finset.card_range] using h
    have hpfit := fits_representation (Nat.mul_pos hd hd) hprod hden
      (lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (Nat.succ_pos len)) hnum)
    have hacc := accumulator_lt zeroId start len hz
    change Safe W [⟨.mul,a len,b (k-len)⟩,
      ⟨.add,start+2*len,accumulator zeroId start len⟩] (start+2*len) e
    refine ⟨hpfit,?_,trivial⟩
    change Fits ((Function.update e (start+2*len) (e (a len)*e (b (k-len)))) (start+2*len)+
      (Function.update e (start+2*len) (e (a len)*e (b (k-len)))) (accumulator zeroId start len)) W
    rw [Function.update_same,Function.update_of_ne (by omega : accumulator zeroId start len≠start+2*len)]
    have hadd := representation_add hprod hsum
    apply fits_representation (Nat.mul_pos hd hd) hadd hden
    convert hnum using 1; ring

/-- The entire emitted cached convolution is safe, including every term and
prefix at EVERY coefficient, not only the final returned coefficient. -/
theorem mulCode_safe (zeroId start J d B W : ℕ) (a b : ℕ → ℕ) (env : ℕ → ℚ)
    (hd : 0<d) (hz : zeroId<start) (he : env zeroId=0)
    (ha : ∀ i<J,a i<start) (hb : ∀ i<J,b i<start)
    (hA : ∀ i<J,Representation (env (a i)) d B)
    (hB : ∀ i<J,Representation (env (b i)) d B)
    (hden : d*d<2^W) (hnum : J*(B*B)<2^W) :
    Safe W (mulCode zeroId start a b J) start env := by
  induction J with
  | zero => trivial
  | succ J ih =>
    rw [mulCode,safe_append]
    refine ⟨ih (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega))
      (fun i hi => hA i (by omega)) (fun i hi => hB i (by omega))
      (lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_succ J)) hnum),?_⟩
    let previous := mulCode zeroId start a b J
    let next := start+previous.length
    let e := evaluate previous start env
    apply dotCode_safe zeroId next J (J+1) d B W a b e hd
    · dsimp [next];omega
    · exact (evaluate_old previous start zeroId env hz).trans he
    · intro i hi; exact (ha i hi).trans_le (by dsimp [next];omega)
    · intro i _; exact (hb (J-i) (by omega)).trans_le (by dsimp [next];omega)
    · intro i hi
      rw [show e (a i)=env (a i) from evaluate_old previous start _ env (ha i hi)]
      exact hA i hi
    · intro i _
      rw [show e (b (J-i))=env (b (J-i)) from evaluate_old previous start _ env (hb _ (by omega))]
      exact hB _ (by omega)
    · exact hden
    · exact hnum

/-- Internal compositional safety lemma: all demanded scalar values are the
EXACT original products/prefixes, not unknown execution-state quantities. -/
theorem dotCode_safe_known (zeroId start k len W : ℕ) (a b : ℕ → ℕ) (env : ℕ → ℚ)
    (hz : zeroId<start) (he : env zeroId=0)
    (ha : ∀ i<len,a i<start) (hb : ∀ i<len,b (k-i)<start)
    (hprod : ∀ i<len,Fits (env (a i)*env (b (k-i))) W)
    (hsum : ∀ m ≤ len,Fits (∑ i∈Finset.range m,env (a i)*env (b (k-i))) W) :
    Safe W (dotCode zeroId start k a b len) start env := by
  induction len with
  | zero => trivial
  | succ len ih =>
    rw [dotCode,safe_append,dotCode_length]
    refine ⟨ih (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega))
      (fun i hi => hprod i (by omega)) (fun m hm => hsum m (by omega)),?_⟩
    let e := evaluate (dotCode zeroId start k a b len) start env
    have ea : e (a len)=env (a len) := evaluate_old _ start _ env (ha len (by omega))
    have eb : e (b (k-len))=env (b (k-len)) := evaluate_old _ start _ env (hb len (by omega))
    have hprefix := dotCode_correct zeroId start k len a b env hz he
      (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega))
    have hacc := accumulator_lt zeroId start len hz
    change Safe W [⟨.mul,a len,b (k-len)⟩,
      ⟨.add,start+2*len,accumulator zeroId start len⟩] (start+2*len) e
    refine ⟨?_,?_,trivial⟩
    · change Fits (e (a len)*e (b (k-len))) W
      rw [ea,eb]
      exact hprod len (by omega)
    · change Fits ((Function.update e (start+2*len) (e (a len)*e (b (k-len)))) (start+2*len)+
        (Function.update e (start+2*len) (e (a len)*e (b (k-len)))) (accumulator zeroId start len)) W
      rw [Function.update_same,Function.update_of_ne (by omega : accumulator zeroId start len≠start+2*len)]
      change e (accumulator zeroId start len)=_ at hprefix
      rw [ea,eb,hprefix]
      have hs := hsum (len+1) (by omega)
      rw [Finset.sum_range_succ] at hs
      simpa only [add_comm] using hs

/-- Internal whole-array safety lemma with exact original scalar products and
finite convolution prefixes. The source specialization below proves these. -/
theorem mulCode_safe_known (zeroId start J W : ℕ) (a b : ℕ → ℕ) (env : ℕ → ℚ)
    (hz : zeroId<start) (he : env zeroId=0)
    (ha : ∀ i<J,a i<start) (hb : ∀ i<J,b i<start)
    (hprod : ∀ k<J,∀ i ≤ k,Fits (env (a i)*env (b (k-i))) W)
    (hsum : ∀ k<J,∀ m ≤ k+1,Fits (∑ i∈Finset.range m,env (a i)*env (b (k-i))) W) :
    Safe W (mulCode zeroId start a b J) start env := by
  induction J with
  | zero => trivial
  | succ J ih =>
    rw [mulCode,safe_append]
    refine ⟨ih (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega))
      (fun k hk => hprod k (by omega)) (fun k hk => hsum k (by omega)),?_⟩
    let previous := mulCode zeroId start a b J
    let next := start+previous.length
    let e := evaluate previous start env
    have ea (i : ℕ) (hi : i<J+1) : e (a i)=env (a i) := evaluate_old previous start _ env (ha i hi)
    have eb (i : ℕ) (hi : i<J+1) : e (b i)=env (b i) := evaluate_old previous start _ env (hb i hi)
    apply dotCode_safe_known zeroId next J (J+1) W a b e
    · dsimp [next];omega
    · exact (evaluate_old previous start zeroId env hz).trans he
    · intro i hi; exact (ha i hi).trans_le (by dsimp [next];omega)
    · intro i _; exact (hb (J-i) (by omega)).trans_le (by dsimp [next];omega)
    · intro i hi
      rw [ea i hi,eb (J-i) (by omega)]
      exact hprod J (by omega) i (by omega)
    · intro m hm
      have heq : (∑ i∈Finset.range m,e (a i)*e (b (J-i)))=
          ∑ i∈Finset.range m,env (a i)*env (b (J-i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        have him := Finset.mem_range.mp hi
        rw [ea i (by omega),eb (J-i) (by omega)]
      rw [heq]
      exact hsum J (by omega) m hm

end RiemannGaussian.SemiprimeSourceArrayProgramSafe
