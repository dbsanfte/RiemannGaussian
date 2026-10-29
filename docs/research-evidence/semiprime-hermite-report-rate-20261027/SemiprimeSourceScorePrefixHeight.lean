/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMaterializedScoreSearch
import RiemannGaussian.SemiprimeJetArrayHeight

/-! # Heights of the actual source conditional-expectation scratch
Original x/y bounds derive the terminal scores, every finite child-sum prefix,
and each executed averaging result. No terminal-score or intermediate-height
answer is an input. Source/control bit simulation remains a separate join.
-/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace RiemannGaussian.SemiprimeSourceScorePrefixHeight
open scoped BigOperators
open SemiprimeJetArrayHeight
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes
open SemiprimeMaterializedScoreEnvironment

/-- Literal zero admits the same common denominator as any score. -/
theorem zero_representation (d : ℕ) : Representation (0:ℚ) d 0 :=
  ⟨0,by simp,by simp⟩

/-- The executed terminal has only the three values 0,x²,y². -/
theorem terminal_representation {r Q : ℕ} (x y : ℚ) (d B : ℕ)
    (hx : Representation x d B) (hy : Representation y d B)
    (p : ScoreProgram Q) (env : Environment r Q) :
    Representation (terminal x y p env).value (d^2) (B^2) := by
  have hx2 : Representation (x^2) (d^2) (B^2) := by
    simpa only [pow_two] using representation_mul hx hx
  have hy2 : Representation (y^2) (d^2) (B^2) := by
    simpa only [pow_two] using representation_mul hy hy
  rw [terminal_value]
  cases p <;> simp only [programValue] <;> split_ifs <;> simp only [mul_one,mul_zero]
  · exact hy2
  · exact representation_mono (zero_representation _) (Nat.zero_le _)
  · exact hx2
  · exact representation_mono (zero_representation _) (Nat.zero_le _)

/-- Every actual cached finite sum has one denominator, with no cancellation assumption. -/
theorem sumRun_representation {A : Type*} (f : A → SemiprimeMaterializedWords.Run ℚ)
    (xs : List A) (d B : ℕ) (hf : ∀ a∈xs,Representation (f a).value d B) :
    Representation (SemiprimeMaterializedWords.sumRun f xs).value d (xs.length*B) := by
  induction xs with
  | nil => simpa only [SemiprimeMaterializedWords.sumRun,List.length_nil,Nat.zero_mul] using zero_representation d
  | cons a xs ih =>
    have ha := hf a List.mem_cons_self
    have hb := ih (fun a ha => hf a (List.mem_cons_of_mem _ ha))
    have hh := representation_add ha hb
    simpa only [SemiprimeMaterializedWords.sumRun,List.length_cons,Nat.add_mul,Nat.one_mul,
      Nat.add_comm] using hh

/-- Every actual partial child sum, not only its final value, is controlled. -/
theorem sumRun_prefix_representation {A : Type*} (f : A → SemiprimeMaterializedWords.Run ℚ)
    (xs : List A) (d B k : ℕ) (hf : ∀ a∈xs,Representation (f a).value d B) :
    Representation (SemiprimeMaterializedWords.sumRun f (xs.take k)).value d ((xs.take k).length*B) :=
  sumRun_representation f (xs.take k) d B (fun a ha => hf a (List.mem_of_mem_take ha))

/-- Executed division by the positive alphabet size introduces exactly one known factor. -/
theorem divide_representation {q : ℚ} (d B A : ℕ)
    (hq : Representation q d B) : Representation (q/(A:ℚ)) (d*A) B := by
  obtain ⟨z,hz,hb⟩ := hq
  refine ⟨z,?_,hb⟩
  rw [hz,Nat.cast_mul,div_div]

/-- Every actual recursive averaging result, uniformly over all cached environments. -/
theorem expectation_representation {r Q : ℕ} (alphabet : List (Word r Q)) (x y : ℚ)
    (d B : ℕ)
    (hx : Representation x d B) (hy : Representation y d B)
    (p : ScoreProgram Q) (remaining : List ℕ) (env : Environment r Q) :
    Representation (SemiprimeMaterializedScoreSearch.expectation alphabet x y p remaining env).value
      (d^2*alphabet.length^remaining.length) (B^2*alphabet.length^remaining.length) := by
  induction remaining generalizing env with
  | nil => simpa only [SemiprimeMaterializedScoreSearch.expectation,List.length_nil,pow_zero,mul_one] using
      terminal_representation x y d B hx hy p env
  | cons i remaining ih =>
    have hs := sumRun_representation
      (fun w => (⟨(SemiprimeMaterializedScoreSearch.expectation alphabet x y p remaining
        (extend env i w)).value,
        (SemiprimeMaterializedScoreSearch.expectation alphabet x y p remaining (extend env i w)).work+Q+2⟩ :
          SemiprimeMaterializedWords.Run ℚ)) alphabet
      (d^2*alphabet.length^remaining.length) (B^2*alphabet.length^remaining.length)
      (fun w _ => ih (extend env i w))
    have hh := divide_representation _ _ alphabet.length hs
    convert hh using 1 <;> simp only [SemiprimeMaterializedScoreSearch.expectation,List.length_cons,pow_succ] <;> ring

/-- All child-sum prefixes in an actual expectation frame have the original-data bound. -/
theorem expectation_child_prefix {r Q : ℕ} (alphabet : List (Word r Q)) (x y : ℚ)
    (d B : ℕ)
    (hx : Representation x d B) (hy : Representation y d B)
    (p : ScoreProgram Q) (remaining : List ℕ) (env : Environment r Q) (i k : ℕ) :
    Representation (SemiprimeMaterializedWords.sumRun
      (fun w => (⟨(SemiprimeMaterializedScoreSearch.expectation alphabet x y p remaining (extend env i w)).value,
        (SemiprimeMaterializedScoreSearch.expectation alphabet x y p remaining (extend env i w)).work+Q+2⟩ :
        SemiprimeMaterializedWords.Run ℚ)) (alphabet.take k)).value
      (d^2*alphabet.length^remaining.length) ((alphabet.take k).length*(B^2*alphabet.length^remaining.length)) := by
  apply sumRun_prefix_representation
  intro w _
  exact expectation_representation alphabet x y d B hx hy p remaining (extend env i w)

/-- Normalization cannot increase the derived numerator or denominator bounds. -/
theorem expectation_reduced_bounds {r Q : ℕ} (alphabet : List (Word r Q)) (x y : ℚ)
    (d B : ℕ) (hd : 0<d) (hA : 0<alphabet.length)
    (hx : Representation x d B) (hy : Representation y d B)
    (p : ScoreProgram Q) (remaining : List ℕ) (env : Environment r Q) :
    (SemiprimeMaterializedScoreSearch.expectation alphabet x y p remaining env).value.den≤
        d^2*alphabet.length^remaining.length ∧
      (SemiprimeMaterializedScoreSearch.expectation alphabet x y p remaining env).value.num.natAbs≤
        B^2*alphabet.length^remaining.length :=
  representation_reduced_bound (Nat.mul_pos (pow_pos hd _) (pow_pos hA _))
    (expectation_representation alphabet x y d B hx hy p remaining env)

/-- The actual right-recursive cached sum also stores suffix sums. -/
theorem sumRun_suffix_representation {A : Type*} (f : A → SemiprimeMaterializedWords.Run ℚ)
    (xs : List A) (d B k : ℕ) (hf : ∀ a∈xs,Representation (f a).value d B) :
    Representation (SemiprimeMaterializedWords.sumRun f (xs.drop k)).value d ((xs.drop k).length*B) :=
  sumRun_representation f (xs.drop k) d B (fun a ha => hf a (List.mem_of_mem_drop ha))

/-- Every suffix cached by the executed expectation child-sum has a derived bound. -/
theorem expectation_child_suffix {r Q : ℕ} (alphabet : List (Word r Q)) (x y : ℚ)
    (d B : ℕ)
    (hx : Representation x d B) (hy : Representation y d B)
    (p : ScoreProgram Q) (remaining : List ℕ) (env : Environment r Q) (i k : ℕ) :
    Representation (SemiprimeMaterializedWords.sumRun
      (fun w => (⟨(SemiprimeMaterializedScoreSearch.expectation alphabet x y p remaining (extend env i w)).value,
        (SemiprimeMaterializedScoreSearch.expectation alphabet x y p remaining (extend env i w)).work+Q+2⟩ :
        SemiprimeMaterializedWords.Run ℚ)) (alphabet.drop k)).value
      (d^2*alphabet.length^remaining.length) ((alphabet.drop k).length*(B^2*alphabet.length^remaining.length)) := by
  apply sumRun_suffix_representation
  intro w _
  exact expectation_representation alphabet x y d B hx hy p remaining (extend env i w)

/-- Common denominator extracted from the ORIGINAL source score scales. -/
def scaleDenominator (x y : ℚ) : ℕ := x.den*y.den
/-- Shared original-scale numerator envelope, before any score is evaluated. -/
def scaleNumerator (x y : ℚ) : ℕ := x.num.natAbs*y.den+y.num.natAbs*x.den

/-- Canonical scale data supply the input representations without any advice. -/
theorem scale_representations (x y : ℚ) :
    0<scaleDenominator x y ∧
      Representation x (scaleDenominator x y) (scaleNumerator x y) ∧
      Representation y (scaleDenominator x y) (scaleNumerator x y) := by
  have hOne (q : ℚ) : Representation (1:ℚ) q.den q.den := by
    refine ⟨(q.den:ℤ),?_,by simp⟩
    simp only [Int.cast_natCast]
    exact (div_self (by exact_mod_cast q.den_pos.ne')).symm
  have hx : Representation x x.den x.num.natAbs := ⟨x.num,(Rat.num_div_den x).symm,le_rfl⟩
  have hy : Representation y y.den y.num.natAbs := ⟨y.num,(Rat.num_div_den y).symm,le_rfl⟩
  have hxx := representation_mul hx (hOne y)
  have hyy := representation_mul hy (hOne x)
  simp only [mul_one] at hxx hyy
  refine ⟨Nat.mul_pos x.den_pos y.den_pos,?_,?_⟩
  · exact representation_mono hxx (Nat.le_add_right _ _)
  · rw [Nat.mul_comm y.den x.den] at hyy
    exact representation_mono hyy (Nat.le_add_left _ _)

/-- Actual nonempty source alphabets have automatic normalized scratch bounds;
no score, denominator or height answer is supplied by the caller. -/
theorem source_expectation_bounds {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (x y : ℚ) (p : ScoreProgram Q) (remaining : List ℕ) (env : Environment r Q) :
    (SemiprimeMaterializedScoreSearch.expectation (a::tail) x y p remaining env).value.den≤
        scaleDenominator x y^2*(a::tail).length^remaining.length ∧
      (SemiprimeMaterializedScoreSearch.expectation (a::tail) x y p remaining env).value.num.natAbs≤
        scaleNumerator x y^2*(a::tail).length^remaining.length := by
  have h := scale_representations x y
  exact expectation_reduced_bounds (a::tail) x y _ _ h.1 (by simp) h.2.1 h.2.2 p remaining env

/-- Extend a known averaging depth into the common support-four denominator. -/
theorem extend_depth {q : ℚ} (d B A s t : ℕ) (hA : 0<A) (hst : s≤t)
    (hq : Representation q (d*A^s) (B*A^s)) :
    Representation q (d*A^t) (B*A^t) := by
  have hOne_nat (c : ℕ) (hc : 0<c) : Representation (1:ℚ) c c := by
    refine ⟨(c:ℤ),?_,by simp⟩
    simp only [Int.cast_natCast]
    exact (div_self (by exact_mod_cast hc.ne')).symm
  have hOne := hOne_nat (A^(t-s)) (pow_pos hA _)
  have hh := representation_mul hq hOne
  simpa only [mul_one,mul_assoc,← pow_add,Nat.add_sub_of_le hst] using hh

/-- A concrete source term always uses the same support-four denominator,
independently of which active variables survive its actual support scan. -/
theorem localTerm_representation {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (x y : ℚ) (d B : ℕ) (hx : Representation x d B) (hy : Representation y d B)
    (p : ScoreProgram Q) (remaining : List ℕ) (hr : remaining.Nodup) (env : Environment r Q) :
    Representation (SemiprimeMaterializedScoreSearch.localTerm (a::tail) x y p remaining env).value
      (d^2*(a::tail).length^4) (B^2*(a::tail).length^4) := by
  have hs : (SemiprimeMaterializedWords.activeRun (support p) remaining).value.length≤4 := by
    rw [SemiprimeMaterializedWords.activeRun_value]
    exact (LocalExpectation.active_length_le (support p).toFinset remaining hr).trans
      ((List.toFinset_card_le _).trans (support_length p))
  have hh := expectation_representation (a::tail) x y d B hx hy p
    (SemiprimeMaterializedWords.activeRun (support p) remaining).value env
  exact extend_depth (d^2) (B^2) (a::tail).length _ 4 (by simp) hs hh

/-- Every stored suffix in the actual objective term sum has the SAME original
support-four denominator. An offset has not yet been subtracted here. -/
theorem objective_sum_suffix {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (x y : ℚ) (d B : ℕ)
    (hx : Representation x d B) (hy : Representation y d B)
    (remaining : List ℕ) (hr : remaining.Nodup) (env : Environment r Q) (k : ℕ) :
    Representation (SemiprimeMaterializedWords.sumRun
      (fun p => SemiprimeMaterializedScoreSearch.localTerm (a::tail) x y p remaining env)
      (programs.drop k)).value (d^2*(a::tail).length^4)
      ((programs.drop k).length*(B^2*(a::tail).length^4)) := by
  apply sumRun_suffix_representation
  intro p _
  exact localTerm_representation a tail x y d B hx hy p remaining hr env

/-- The fully executed objective, including its original supplied scale offset,
has an automatic common representation; no score output is an input. -/
theorem evaluate_representation {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (x y offset : ℚ)
    (remaining : List ℕ) (hr : remaining.Nodup) (env : Environment r Q) :
    let D := scaleDenominator x y^2*(a::tail).length^4
    let N := programs.length*(scaleNumerator x y^2*(a::tail).length^4)
    Representation (SemiprimeMaterializedScoreSearch.evaluate (a::tail) programs x y offset remaining env).value
      (D*offset.den) (N*offset.den+offset.num.natAbs*D) := by
  let D := scaleDenominator x y^2*(a::tail).length^4
  let N := programs.length*(scaleNumerator x y^2*(a::tail).length^4)
  have hh := scale_representations x y
  have hD : 0<D := Nat.mul_pos (pow_pos hh.1 _) (pow_pos (by simp) _)
  have hsum : Representation (SemiprimeMaterializedWords.sumRun
      (fun p => SemiprimeMaterializedScoreSearch.localTerm (a::tail) x y p remaining env) programs).value D N := by
    apply sumRun_representation
    intro p _
    exact localTerm_representation a tail x y _ _ hh.2.1 hh.2.2 p remaining hr env
  have hOne (c : ℕ) (hc : 0<c) : Representation (1:ℚ) c c := by
    refine ⟨(c:ℤ),?_,by simp⟩
    simp only [Int.cast_natCast]
    exact (div_self (by exact_mod_cast hc.ne')).symm
  have hs := representation_mul hsum (hOne offset.den offset.den_pos)
  have ho : Representation (-offset) offset.den offset.num.natAbs := by
    refine ⟨-offset.num,?_,by simp⟩
    rw [Int.cast_neg,neg_div]
    exact congrArg Neg.neg (Rat.num_div_den offset).symm
  have hot := representation_mul ho (hOne D hD)
  simp only [mul_one] at hs hot
  rw [Nat.mul_comm offset.den D] at hot
  simpa only [SemiprimeMaterializedScoreSearch.evaluate,sub_eq_add_neg] using representation_add hs hot

/-- The exact original-source scale formulas have explicit input-dimension
representations. This controls the caller link, not just evaluated score values. -/
theorem original_scale_representations (eps : ℚ) (de Be M n r A : ℕ)
    (he : Representation eps de Be) (hde : 0<de) (hr : 0<r) (hA : 0<A) :
    let D := de*A*(2*r)
    let B := Be*M*(2*r)+n*de*A
    Representation (eps*(M:ℚ)/(A:ℚ)) D B ∧
      Representation ((n:ℚ)/(2*(r:ℚ))) D B := by
  have hOne (c : ℕ) (hc : 0<c) : Representation (1:ℚ) c c := by
    refine ⟨(c:ℤ),?_,by simp⟩
    simp only [Int.cast_natCast]
    exact (div_self (by exact_mod_cast hc.ne')).symm
  have hM : Representation (M:ℚ) 1 M := ⟨(M:ℤ),by simp,by simp⟩
  have hx := divide_representation _ _ A (representation_mul he hM)
  have hx' := representation_mul hx (hOne (2*r) (by omega))
  have hy : Representation ((n:ℚ)/(2*(r:ℚ))) (2*r) n :=
    ⟨(n:ℤ),by simp,by simp⟩
  have hy' := representation_mul hy (hOne (de*A) (Nat.mul_pos hde hA))
  simp only [mul_one] at hy'
  have hz : Representation ((n:ℚ)/(2*(r:ℚ))) (de*A*(2*r)) (n*de*A) := by
    convert hy' using 1 <;> ring
  refine ⟨?_,representation_mono hz (Nat.le_add_left _ _)⟩
  simp only [mul_one] at hx'
  exact representation_mono hx' (Nat.le_add_right _ _)

/-- At the actual scheduled epsilon=1/(r*lambda), both score scales have
closed original-dimension bounds; no rational numerator/denominator advice remains. -/
theorem scheduled_scale_representations (M n r lam A : ℕ)
    (hr : 0<r) (hlam : 0<lam) (hA : 0<A) :
    let eps : ℚ := 1/((r*lam:ℕ):ℚ)
    let D := r*lam*A*(2*r)
    let B := M*(2*r)+n*(r*lam)*A
    Representation (eps*(M:ℚ)/(A:ℚ)) D B ∧
      Representation ((n:ℚ)/(2*(r:ℚ))) D B := by
  have he : Representation (1/((r*lam:ℕ):ℚ)) (r*lam) 1 := ⟨1,by simp,by simp⟩
  simpa only [Nat.one_mul] using original_scale_representations
    (1/((r*lam:ℕ):ℚ)) (r*lam) 1 M n r A he (Nat.mul_pos hr hlam) hr hA

end RiemannGaussian.SemiprimeSourceScorePrefixHeight
