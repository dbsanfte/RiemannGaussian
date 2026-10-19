/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Detector.TuplePrincipal
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Joined native compensation and literal prime residue variance

The one-prime identity is for the actual completed mask and actual high
summand, including every cube and original exclusion. The full principal
product is already imported from TuplePrincipal. The actual prime quotient
has strictly positive centered energy even when its complete mean vanishes.
No annular lower bound, source transfer, or improvement to row energy follows.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
noncomputable section
open scoped Classical BigOperators
namespace OpenAIReview.JoinedMarkVariance
open OAI OAI.SevenEighths OAI.SevenEighths.ProbePhysical
open OAI.SevenEighths.ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-- The actual complementary-subset mark retains all completed cube overlaps. -/
theorem completed_mask_split (S : Finset Id) (P I J : Id) (B c : ℂ) :
    B*completedMask S P I J-c*completedMask S 1 I J =
      completedMask S 1 I J*(B*(if P∣I*J^3 then 1 else 0)-c) := by
  unfold completedMask
  split_ifs <;> simp_all

/-- Same native physical/cofactor summand, before an absolute value or energy. -/
theorem actual_high_summand_split (S : Finset Id) (P : Id)
    (eta : HeckeFamily.Character) (u : O) (x w z : ℂ) (I J K L : Id) (B c : ℂ) :
    B*markedIdealHighSummand S P eta u x w z I J K L-
        c*markedIdealHighSummand S 1 eta u x w z I J K L =
      markedIdealHighSummand S 1 eta u x w z I J K L*
        (B*(if P∣I*J^3 then 1 else 0)-c) := by
  unfold markedIdealHighSummand highIdealMask
  have h := completed_mask_split S P I J B c
  linear_combination h *
    (if ∀p∈S,¬p∣K then (1:ℂ) else 0) *
    (if ∀p∈S,¬p∣L then (1:ℂ) else 0) *
    bareIdealHighSummand eta u x w z I J K L

/-- Literal residue test for divisibility by this actual prime ideal. -/
def residueMark (P : Id) (B c : ℂ) (a : O⧸P) : ℂ :=
  B*(if a=0 then 1 else 0)-c

/-- Pullback is precisely the actual ideal-membership mark. -/
theorem residueMark_mk (P : Id) (B c : ℂ) (a : O) :
    residueMark P B c (Ideal.Quotient.mk P a) =
      B*(if a∈P then 1 else 0)-c := by
  simp [residueMark,Ideal.Quotient.eq_zero_iff_mem]

/-- The actual prime quotient has norm many residues. -/
theorem quotient_card (P : Id) [P.IsMaximal] :
    Fintype.card (O⧸P)=P.absNorm := by
  rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]

/-- Exact complete first moment; mean centering is only a first-moment identity. -/
theorem residue_sum (P : Id) [P.IsMaximal] (B c : ℂ) :
    (∑a : O⧸P,residueMark P B c a)=B-(P.absNorm:ℂ)*c := by
  simp [residueMark,Finset.sum_sub_distrib,quotient_card]

/-- Exact full residue energy, retaining the single zero and every nonunit. -/
theorem residue_energy (P : Id) [P.IsMaximal] (B c : ℂ) :
    (∑a : O⧸P,‖residueMark P B c a‖^2)=
      ‖B-c‖^2+((P.absNorm:ℝ)-1)*‖c‖^2 := by
  let f : O⧸P → ℝ := fun a=>‖residueMark P B c a‖^2
  have he := Finset.add_sum_erase (Finset.univ : Finset (O⧸P)) f
    (a:=(0:O⧸P)) (Finset.mem_univ _)
  have hrest : (∑a∈(Finset.univ : Finset (O⧸P)).erase 0,f a)=
      ((P.absNorm:ℝ)-1)*‖c‖^2 := by
    calc
      _ = ∑_a∈(Finset.univ : Finset (O⧸P)).erase 0,‖c‖^2 := by
        apply Finset.sum_congr rfl
        intro a ha
        simp [f,residueMark,(Finset.mem_erase.mp ha).1]
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ,nsmul_eq_mul]
        rw [Nat.cast_sub (by exact Fintype.card_pos_iff.mpr inferInstance),
          Nat.cast_one,quotient_card]
  rw [←he,hrest]
  simp [f,residueMark]

/-- Exact variance formula; a perfectly centered prime still contributes variance. -/
theorem residue_variance (P : Id) [P.IsMaximal] (B c : ℂ) :
    (∑a : O⧸P,‖residueMark P B c a‖^2)/(P.absNorm:ℝ)=
      ‖B‖^2*((P.absNorm:ℝ)-1)/(P.absNorm:ℝ)^2+
        ‖B/(P.absNorm:ℂ)-c‖^2 := by
  have hq : (P.absNorm:ℝ)≠0 := by
    rw [←quotient_card]
    exact_mod_cast Fintype.card_ne_zero
  rw [residue_energy]
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.div_natCast_re,Complex.div_natCast_im]
  field_simp
  ring

/-- No nonzero actual prime mark has zero residue energy, for any center. -/
theorem residue_energy_pos (P : Id) [P.IsMaximal] (B c : ℂ) (hB : B≠0) :
    0<(∑a : O⧸P,‖residueMark P B c a‖^2) := by
  have hqN : 1<P.absNorm := by
    rw [←quotient_card]
    exact Fintype.one_lt_card
  have hq : (1:ℝ)<P.absNorm := by exact_mod_cast hqN
  rw [residue_energy]
  by_cases hc : c=0
  · simp only [hc,sub_zero,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,
      zero_pow,mul_zero,add_zero]
    exact sq_pos_of_pos (norm_pos_iff.mpr hB)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _)
      (mul_pos (by linarith) (sq_pos_of_pos (norm_pos_iff.mpr hc)))

/-- Perfect centering kills the complete mean and leaves positive energy. -/
theorem centered_mean_zero_energy_pos (P : Id) [P.IsMaximal] (B : ℂ) (hB : B≠0) :
    (∑a : O⧸P,residueMark P B (B/(P.absNorm:ℂ)) a)=0 ∧
      0<(∑a : O⧸P,‖residueMark P B (B/(P.absNorm:ℂ)) a‖^2) := by
  constructor
  · rw [residue_sum]
    have hq : (P.absNorm:ℂ)≠0 := by
      rw [←quotient_card]
      exact_mod_cast Fintype.card_ne_zero
    field_simp
    ring
  · exact residue_energy_pos P B _ hB

/-- All distinct-prime CRT coordinate profiles, with their original centers. -/
theorem residue_product_mean {ι : Type*} [Fintype ι] (P : ι → Id)
    [∀i,(P i).IsMaximal] (B c : ι → ℂ) :
    (∑a : ∀i,O⧸P i,∏i,residueMark (P i) (B i) (c i) (a i))=
      ∏i,(B i-(Ideal.absNorm (P i):ℂ)*c i) := by
  rw [←Fintype.prod_sum]
  exact Finset.prod_congr rfl (fun i _=>residue_sum (P i) (B i) (c i))

/-- Exact joined residue energy, including every cross-subset term before norms. -/
theorem residue_product_energy {ι : Type*} [Fintype ι] (P : ι → Id)
    [∀i,(P i).IsMaximal] (B c : ι → ℂ) :
    (∑a : ∀i,O⧸P i,‖∏i,residueMark (P i) (B i) (c i) (a i)‖^2)=
      ∏i,(‖B i-c i‖^2+((Ideal.absNorm (P i):ℝ)-1)*‖c i‖^2) := by
  simp_rw [norm_prod,←Finset.prod_pow]
  rw [←Fintype.prod_sum (fun i (a : O⧸P i)=>‖residueMark (P i) (B i) (c i) a‖^2)]
  exact Finset.prod_congr rfl (fun i _=>residue_energy (P i) (B i) (c i))

/-- A full centered product has positive energy; no individual subset is isolated. -/
theorem residue_product_energy_pos {ι : Type*} [Fintype ι] (P : ι → Id)
    [∀i,(P i).IsMaximal] (B c : ι → ℂ) (hB : ∀i,B i≠0) :
    0<(∑a : ∀i,O⧸P i,‖∏i,residueMark (P i) (B i) (c i) (a i)‖^2) := by
  rw [residue_product_energy]
  apply Finset.prod_pos
  intro i _
  rw [←residue_energy]
  exact residue_energy_pos (P i) (B i) (c i) (hB i)

end OpenAIReview.JoinedMarkVariance
#lint+ in OpenAIReview.JoinedMarkVariance

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut details : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    details := details.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  logInfo m!"Joined-mark variance audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.writeFile ".lake/arithmetic-operator-joined-mark-recovery/axioms.json"
    (Json.mkObj [("declarations",toJson declarations),("theoremsIncludingHelpers",toJson theorems),
      ("namespaceLinters",toJson (15:Nat)),("allLocalModuleProvenance",toJson true),
      ("onlyStandardAxioms",toJson true),("details",Json.arr details)]).pretty
