/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceOffsetHeight

/-! # Original-input bounds for the scores actually compared in label search
The offset is acquired by the existing offsetRun. These proofs use its derived
representation and the actual support-four evaluator, including all choices of
search prefix. They do not identify the scalar ledger with a primitive clock.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeSourceScoreState
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes
open SemiprimeJetArrayHeight SemiprimeSourceScorePrefixHeight
open SemiprimeSourceOffsetHeight SemiprimeMaterializedScoreEnvironment

/-- An original-scale representation for the executed objective, including offset subtraction. -/
theorem evaluate_representation {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (x y offset : ℚ) (d B e C : ℕ)
    (hd : 0<d) (he : 0<e) (hx : Representation x d B) (hy : Representation y d B)
    (ho : Representation offset e C) (remaining : List ℕ) (hr : remaining.Nodup)
    (env : Environment r Q) :
    Representation (SemiprimeMaterializedScoreSearch.evaluate (a::tail) programs
      x y offset remaining env).value
      ((d^2*(a::tail).length^4)*e)
      ((programs.length*(B^2*(a::tail).length^4))*e+C*(d^2*(a::tail).length^4)) := by
  let D := d^2*(a::tail).length^4
  let N := programs.length*(B^2*(a::tail).length^4)
  have hD : 0<D := Nat.mul_pos (pow_pos hd _) (pow_pos (by simp) _)
  have hs : Representation (SemiprimeMaterializedWords.sumRun
      (fun p => SemiprimeMaterializedScoreSearch.localTerm (a::tail) x y p remaining env)
      programs).value D N := by
    apply sumRun_representation
    intro p _
    exact localTerm_representation a tail x y d B hx hy p remaining hr env
  have hs' := extend_factor D N e he hs
  have ho' : Representation (-offset) e C := by
    obtain ⟨z,hz,hb⟩ := ho
    refine ⟨-z,?_,by simpa using hb⟩
    rw [Int.cast_neg,neg_div,hz]
  have hot := extend_factor e C D hD ho'
  rw [Nat.mul_comm e D] at hot
  simpa only [SemiprimeMaterializedScoreSearch.evaluate,sub_eq_add_neg] using
    representation_add hs' hot

/-- Every actual sequential objective call inherits the bound; its range is inherently nodup. -/
theorem sequential_representation {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (x y offset : ℚ) (d B e C : ℕ)
    (hd : 0<d) (he : 0<e) (hx : Representation x d B) (hy : Representation y d B)
    (ho : Representation offset e C) (s : ℕ) (fixed : List (Word r Q)) :
    Representation (SemiprimeMaterializedScoreSearch.sequential a tail programs
      x y offset s fixed).value
      ((d^2*(a::tail).length^4)*e)
      ((programs.length*(B^2*(a::tail).length^4))*e+C*(d^2*(a::tail).length^4)) :=
  evaluate_representation a tail programs x y offset d B e C hd he hx hy ho
    (List.range' fixed.length s) List.nodup_range' (baseEnvironment a fixed)

/-- Canonical scalar fields of each compared objective follow from the original envelopes. -/
theorem sequential_reduced_bounds {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (programs : List (ScoreProgram Q)) (x y offset : ℚ) (d B e C : ℕ)
    (hd : 0<d) (he : 0<e) (hx : Representation x d B) (hy : Representation y d B)
    (ho : Representation offset e C) (s : ℕ) (fixed : List (Word r Q)) :
    let q := (SemiprimeMaterializedScoreSearch.sequential a tail programs x y offset s fixed).value
    q.den≤(d^2*(a::tail).length^4)*e ∧
    q.num.natAbs≤(programs.length*(B^2*(a::tail).length^4))*e+C*(d^2*(a::tail).length^4) :=
  representation_reduced_bound
    (Nat.mul_pos (Nat.mul_pos (pow_pos hd _) (pow_pos (by simp) _)) he)
    (sequential_representation a tail programs x y offset d B e C hd he hx hy ho s fixed)

/-- Original scheduled scale denominator. -/
def scaleD (r lam Q : ℕ) : ℕ := r*lam*r^(2*Q)*(2*r)
/-- Original scheduled scale numerator envelope. -/
def scaleB (M n r lam Q : ℕ) : ℕ := M*(2*r)+n*(r*lam)*r^(2*Q)
/-- One common denominator for every compared objective in the same search. -/
def scoreDenominator (r lam Q : ℕ) : ℕ :=
  (scaleD r lam Q)^2*(r^Q)^4*offsetDenominator (scaleD r lam Q) r Q
/-- One numerator envelope, retaining the actual number of original score instructions. -/
def scoreNumerator (M n r lam Q T : ℕ) : ℕ :=
  (T*((scaleB M n r lam Q)^2*(r^Q)^4))*offsetDenominator (scaleD r lam Q) r Q+
    offsetNumerator (scaleB M n r lam Q) M n r Q*((scaleD r lam Q)^2*(r^Q)^4)

/-- The literal objective callback used inside the original source producer.
Only original enumerations, schedule, and a current search prefix are arguments. -/
abbrev callerScore {I E : Type} [Fintype I] [DecidableEq E] {n r Q : ℕ}
    (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (lam s : ℕ)
    (fixed : List (Word r Q)) : ℚ :=
  let x := (1/((r*lam:ℕ):ℚ))*(en.incidences.values.length:ℚ)/(en.types.values.length:ℚ)
  let y := (n:ℚ)/(2*(r:ℚ))
  (SemiprimeMaterializedScoreSearch.sequential en.wordFirst en.wordTail
    (SemiprimeMaterializedSourceWords.compileAll owner factor en.indices.values en.terms.values).value
    x y (SemiprimeMaterializedSourceWords.offsetRun (Fintype.card I) n r Q x y).value s fixed).value

/-- Every actual scheduled-source objective, with acquired programs and acquired offset,
has original-derived common bounds. No score, scale-height, or offset answer is assumed. -/
theorem caller_score_representation {I E : Type} [Fintype I] [DecidableEq I] [DecidableEq E]
    {n r Q : ℕ} [NeZero r] (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (lam : ℕ) (hlam : 0<lam)
    (s : ℕ) (fixed : List (Word r Q)) :
    Representation (callerScore owner factor en lam s fixed) (scoreDenominator r lam Q)
      (scoreNumerator en.incidences.values.length n r lam Q en.terms.values.length) := by
  have hr : 0<r := NeZero.pos r
  have hs := caller_scale_representations en lam hlam
  have ho := caller_offset_representation en lam hlam
  have hd : 0<scaleD r lam Q := by unfold scaleD; positivity
  have he : 0<offsetDenominator (scaleD r lam Q) r Q := by unfold offsetDenominator; positivity
  have h := sequential_representation en.wordFirst en.wordTail
    (SemiprimeMaterializedSourceWords.compileAll owner factor en.indices.values en.terms.values).value
    _ _ _ (scaleD r lam Q) (scaleB en.incidences.values.length n r lam Q)
    (offsetDenominator (scaleD r lam Q) r Q)
    (offsetNumerator (scaleB en.incidences.values.length n r lam Q) en.incidences.values.length n r Q)
    hd he hs.1 hs.2 ho s fixed
  simpa only [callerScore,← en.incidences.length_eq_card,
    SemiprimeMaterializedSourceWords.compileAll_value,List.length_map,caller_word_length,
    scoreDenominator,scoreNumerator] using h

/-- Positive schedule inputs give a genuinely positive common denominator. -/
theorem scoreDenominator_pos (r lam Q : ℕ) (hr : 0<r) (hlam : 0<lam) :
    0<scoreDenominator r lam Q := by
  unfold scoreDenominator scaleD offsetDenominator
  positivity

/-- Canonical rational fields of the actual compared scores satisfy the original envelopes. -/
theorem caller_score_reduced_bounds {I E : Type} [Fintype I] [DecidableEq I] [DecidableEq E]
    {n r Q : ℕ} [NeZero r] (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (lam : ℕ) (hlam : 0<lam)
    (s : ℕ) (fixed : List (Word r Q)) :
    (callerScore owner factor en lam s fixed).den≤ scoreDenominator r lam Q ∧
    (callerScore owner factor en lam s fixed).num.natAbs≤
      scoreNumerator en.incidences.values.length n r lam Q en.terms.values.length :=
  representation_reduced_bound (scoreDenominator_pos r lam Q (NeZero.pos r) hlam)
    (caller_score_representation owner factor en lam hlam s fixed)

/-- The raw cross-products used in a comparison of any two executed candidate scores
have a uniform bound. Both candidate states are arbitrary, so this covers every search frame. -/
theorem caller_comparison_cross_products {I E : Type} [Fintype I] [DecidableEq I] [DecidableEq E]
    {n r Q : ℕ} [NeZero r] (owner : I → Fin n) (factor : I → E)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) E r Q) (lam : ℕ) (hlam : 0<lam)
    (s t : ℕ) (fixed other : List (Word r Q)) :
    let a := callerScore owner factor en lam s fixed
    let b := callerScore owner factor en lam t other
    let B := scoreNumerator en.incidences.values.length n r lam Q en.terms.values.length
    let D := scoreDenominator r lam Q
    a.num.natAbs*b.den≤B*D ∧ b.num.natAbs*a.den≤B*D ∧
      a.num.natAbs*b.den+b.num.natAbs*a.den≤2*(B*D) := by
  have ha := caller_score_reduced_bounds owner factor en lam hlam s fixed
  have hb := caller_score_reduced_bounds owner factor en lam hlam t other
  have h₁ := Nat.mul_le_mul ha.2 hb.1
  have h₂ := Nat.mul_le_mul hb.2 ha.1
  exact ⟨h₁,h₂,by omega⟩

end RiemannGaussian.SemiprimeSourceScoreState
