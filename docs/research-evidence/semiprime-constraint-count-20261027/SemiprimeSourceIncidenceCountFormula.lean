/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceIncidencePairAverage
import RiemannGaussian.SemiprimeSourceIncidenceNamespaces

/-! # Exact original incidence counts from two constant-size edge classifiers -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceIncidenceCountFormula
open OAI.Algorithms.SubexponentialSAT
open LocalExpectation MulticolorTypes
open SemiprimeSourceHeadCountFormula SemiprimeSourceIncidencePairAverage
open SemiprimeMaterializedScoreEnvironment SemiprimeSourceScoreCountsPadding

/-- A nonloop equality with at least one still-free endpoint costs one word. -/
def pairActive (remaining : List ℕ) (a c : ℕ) : Prop :=
  a≠c ∧ (a∈remaining ∨ c∈remaining)

/-- Anchors are compared only if neither endpoint is free; defaults and
previous overrides never constrain a genuinely still-free endpoint. -/
def pairOK {W : Type*} (remaining : List ℕ) (ω : ℕ → W) (a c : ℕ) : Prop :=
  a=c ∨ a∈remaining ∨ c∈remaining ∨ ω a=ω c

instance pairActiveDecidable (remaining : List ℕ) (a c : ℕ) :
    Decidable (pairActive remaining a c) := by unfold pairActive;infer_instance

instance pairOKDecidable {W : Type*} [DecidableEq W]
    (remaining : List ℕ) (ω : ℕ → W) (a c : ℕ) :
    Decidable (pairOK remaining ω a c) := by unfold pairOK;infer_instance

/-- Four cached integer lanes suffice for every separated original incidence. -/
def classifiedCount {W : Type*} [DecidableEq W] (L : ℕ) (remaining : List ℕ)
    (ω : ℕ → W) (a b c d : ℕ) : ℕ :=
  if pairOK remaining ω a c ∧ pairOK remaining ω b d then
    if pairActive remaining a c ∧ pairActive remaining b d then L^2
    else if pairActive remaining a c ∨ pairActive remaining b d then L^3 else L^4
  else 0

/-- The edge classifier is the exact conditional equality probability. -/
theorem pairPotential_classified {W : Type*} [DecidableEq W] (L : ℕ)
    (remaining : List ℕ) (ω : ℕ → W) (a c : ℕ) :
    pairPotential L remaining ω a c=
      if pairOK remaining ω a c then
        if pairActive remaining a c then 1/(L:ℚ) else 1 else 0 := by
  classical
  by_cases h : a=c
  · subst c;simp [pairPotential,pairOK,pairActive]
  by_cases hf : a∈remaining ∨ c∈remaining
  · have hok : pairOK remaining ω a c := by
      unfold pairOK
      rcases hf with ha|hc
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl hc))
    simp [pairPotential,pairActive,h,hf,hok]
  · have ha : a∉remaining := fun ha => hf (Or.inl ha)
    have hc : c∉remaining := fun hc => hf (Or.inr hc)
    simp [pairPotential,pairOK,pairActive,h,ha,hc]

/-- Clearing only the known positive integer L proves the literal lane value. -/
theorem classified_probability {W : Type*} [DecidableEq W] (L : ℕ) (hL : 0<L)
    (remaining : List ℕ) (ω : ℕ → W) (a b c d : ℕ) :
    pairPotential L remaining ω a c*pairPotential L remaining ω b d=
      (classifiedCount L remaining ω a b c d:ℚ)/(L:ℚ)^4 := by
  classical
  have hln : (L:ℚ)≠0 := by exact_mod_cast Nat.ne_of_gt hL
  rw [pairPotential_classified,pairPotential_classified]
  by_cases ha : pairOK remaining ω a c <;>
    by_cases hb : pairOK remaining ω b d <;>
    by_cases hc : pairActive remaining a c <;>
    by_cases hd : pairActive remaining b d <;>
    simp [classifiedCount,ha,hb,hc,hd] <;> field_simp

/-- Literal lane result belongs to the four cached possibilities, including L=1. -/
theorem classified_cases {W : Type*} [DecidableEq W] (L : ℕ)
    (remaining : List ℕ) (ω : ℕ → W) (a b c d : ℕ) :
    classifiedCount L remaining ω a b c d=0 ∨
    classifiedCount L remaining ω a b c d=L^2 ∨
    classifiedCount L remaining ω a b c d=L^3 ∨
    classifiedCount L remaining ω a b c d=L^4 := by
  classical
  by_cases h : pairOK remaining ω a c ∧ pairOK remaining ω b d
  · by_cases h2 : pairActive remaining a c ∧ pairActive remaining b d
    · simp [classifiedCount,h,h2]
    · by_cases h3 : pairActive remaining a c ∨ pairActive remaining b d
      · simp [classifiedCount,h,h2,h3]
      · simp [classifiedCount,h,h2,h3]
  · simp [classifiedCount,h]

/-- Exact ORIGINAL local count, for every prefix and every cached environment.
The only structural condition is discharged for every compiled source descriptor
by SourceIncidenceNamespaces; it is not an added promise on the source. -/
theorem paddedLocal_formula (r Q : ℕ) (hr : 0<r) (a b c d : ℕ)
    (remaining : List ℕ) (env : Environment r Q) (hn : remaining.Nodup)
    (hab : a≠b) (had : a≠d) (hcb : c≠b) (hcd : c≠d) :
    (paddedLocal (alphabet r Q) (.incidence a b c d) remaining env).value=
      classifiedCount (r^Q) remaining (denote env) a b c d := by
  classical
  have hL : 0<(alphabet r Q).length := by rw [alphabet_length];exact pow_pos hr Q
  have hp := localTerm_count (alphabet r Q) 1 1 (.incidence a b c d) remaining env hL hn
  have hs : DependsOn (support (.incidence a b c d : ScoreProgram Q)).toFinset
      (programValue (r:=r) (Q:=Q) 1 1 (.incidence a b c d)) := by
    intro v w h
    have ha := h a (by simp [support])
    have hb := h b (by simp [support])
    have hc := h c (by simp [support])
    have hd := h d (by simp [support])
    simp only [programValue,ha,hb,hc,hd]
  have hv := SemiprimeMaterializedScoreSearch.localTerm_value (alphabet r Q) 1 1
    (.incidence a b c d) remaining env
  rw [← wordExpectation_filter (alphabet r Q) (List.ne_nil_of_length_pos hL)
    _ _ hs remaining (denote env)] at hv
  have hf : programValue (r:=r) (Q:=Q) 1 1 (.incidence a b c d)=
      (fun v => (if v a=v c then 1 else 0)*(if v b=v d then 1 else 0)) := by
    funext v
    by_cases h1 : v a=v c <;> by_cases h2 : v b=v d <;> simp [programValue,h1,h2]
  rw [hf,separated_average r Q hr remaining hn (denote env) a b c d hab had hcb hcd,
    classified_probability (r^Q) (pow_pos hr Q)] at hv
  simp only [SemiprimeSourceScoreCounts.weight,one_mul,mul_one,alphabet_length] at hp
  have hden : ((r^Q:ℕ):ℚ)^4≠0 := pow_ne_zero _ (by exact_mod_cast Nat.ne_of_gt (pow_pos hr Q))
  have he : ((paddedLocal (alphabet r Q) (.incidence a b c d) remaining env).value:ℚ)=
      (classifiedCount (r^Q) remaining (denote env) a b c d:ℚ) := by
    exact (div_left_inj' hden).mp (hp.symm.trans hv)
  exact_mod_cast he

end RiemannGaussian.SemiprimeSourceIncidenceCountFormula
