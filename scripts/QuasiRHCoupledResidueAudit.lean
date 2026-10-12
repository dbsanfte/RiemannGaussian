/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Detector.LocalPhysical
import OAI.NumberTheory.DirichletL.Moments.Canonical
import OAI.NumberTheory.DirichletL.Cusp.MatrixPhases
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Matching-channel audit of a coupled additive and residue row

This is a finite-period preflight, not an estimate for the entire physical
probe. The actual Eisenstein prime character and its additive trace retain
their matching channel after joining. Nonprincipal means of separate rows
do not imply cancellation of their product. No annular or Gaussian mask is
removed, and no assertion of a hypothetical-zero response is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2048
noncomputable section
open scoped BigOperators Classical
namespace OpenAIReview.CoupledResidue
open OAI

variable {F : Type*} [Field F] [Fintype F]

/-- The additive Fourier row with its actual negative-frequency convention. -/
def additiveRow (chi : MulChar F ℂ) (psi : AddChar F ℂ) (x : F) : ℂ :=
  gaussSum chi (psi.mulShift (-x))

/-- Joining the matching residue character is constant on every nonzero residue. -/
theorem matching_atom (chi : MulChar F ℂ) (psi : AddChar F ℂ) (x : F) :
    chi x * additiveRow chi psi x =
      if x = 0 then 0 else chi (-1) * gaussSum chi psi := by
  by_cases hx : x = 0
  · simp [hx, chi.map_zero]
  · rw [ite_eq_right hx]
    let a : Fˣ := Units.mk0 (-x) (neg_ne_zero.mpr hx)
    have h := gaussSum_mulShift chi psi a
    have hneg : chi (-1) * chi (-1) = 1 := by
      rw [← map_mul]
      simp
    have he : chi (-1) * (chi x * additiveRow chi psi x) = gaussSum chi psi := by
      have hxneg : chi (-x) = chi (-1) * chi x := by
        rw [show -x = (-1:F)*x by ring, map_mul]
      change chi (-x) * additiveRow chi psi x = gaussSum chi psi at h
      rwa [hxneg, mul_assoc] at h
    calc
      _ = chi (-1) * (chi (-1) * (chi x * additiveRow chi psi x)) := by
        rw [← mul_assoc, hneg, one_mul]
      _ = _ := by rw [he]

/-- Any literal finite mask remains as one signed sum; it cannot alter the local phase match. -/
theorem matching_weighted (chi : MulChar F ℂ) (psi : AddChar F ℂ)
    (w : F → ℂ) :
    (∑ x : F, w x * chi x * additiveRow chi psi x) =
      chi (-1) * gaussSum chi psi * ∑ x ∈ Finset.univ.erase 0, w x := by
  have hz : w 0 * chi 0 * additiveRow chi psi 0 = 0 := by rw [chi.map_zero]; ring
  rw [← Finset.sum_erase_add _ _ (by simp : (0 : F) ∈ Finset.univ), hz, add_zero,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [mul_assoc, matching_atom, ite_eq_right (Finset.mem_erase.mp hx).1]
  ring

/-- The matching channel survives a complete residue period, including its nonunit zero. -/
theorem matching_period (chi : MulChar F ℂ) (psi : AddChar F ℂ) :
    (∑ x : F, chi x * additiveRow chi psi x) =
      ((Fintype.card F : ℂ)-1) * chi (-1) * gaussSum chi psi := by
  simpa only [one_mul, Finset.sum_const, Finset.card_erase_of_mem,
    Finset.mem_univ, Finset.card_univ, nsmul_eq_mul, Nat.cast_sub
      (Fintype.card_pos_iff.mpr ⟨(0:F)⟩), Nat.cast_one, mul_comm, mul_left_comm,
    mul_assoc] using matching_weighted chi psi (fun _ => 1)

/-- The joined row is a ratio character, not a pair of unrelated mean-zero rows. -/
theorem cross_atom (chi phi : MulChar F ℂ) (psi : AddChar F ℂ) (x : F) :
    phi x * additiveRow chi psi x =
      (phi*chi⁻¹) x * chi (-1) * gaussSum chi psi := by
  by_cases hx : x = 0
  · simp [hx, phi.map_zero, (phi*chi⁻¹).map_zero]
  · have hn : chi x ≠ 0 := chi.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr hx)
    calc
      _ = (phi x * (chi x)⁻¹) * (chi x * additiveRow chi psi x) := by
        field_simp
      _ = _ := by
        rw [matching_atom, ite_eq_right hx, MulChar.mul_apply,
          MulChar.inv_apply_eq_inv']
        ring

/-- Exact complete-period projection: every NONmatching character vanishes; matching survives. -/
theorem cross_period (chi phi : MulChar F ℂ) (psi : AddChar F ℂ) :
    (∑ x : F, phi x * additiveRow chi psi x) =
      if phi=chi then ((Fintype.card F : ℂ)-1)*chi (-1)*gaussSum chi psi else 0 := by
  by_cases h : phi=chi
  · subst phi
    rw [ite_eq_left rfl, matching_period]
  · rw [ite_eq_right h]
    simp_rw [cross_atom, ← Finset.sum_mul]
    have hn : phi*chi⁻¹ ≠ 1 := by
      intro he
      have hh := congrArg (fun c : MulChar F ℂ => c*chi) he
      exact h (by simpa only [mul_assoc, inv_mul_cancel, mul_one, one_mul] using hh)
    rw [MulChar.sum_eq_zero_of_ne_one hn, zero_mul, zero_mul]

/-- The individual residue row is mean zero when the character is nonprincipal. -/
theorem residue_mean_zero (chi : MulChar F ℂ) (hchi : chi ≠ 1) :
    (∑ x : F, chi x) = 0 :=
  chi.sum_eq_zero_of_ne_one hchi

/-- The separate additive row also has mean zero; this does not pay the joined channel. -/
theorem additive_mean_zero (chi : MulChar F ℂ) (psi : AddChar F ℂ)
    (hpsi : psi.IsPrimitive) : (∑ x : F, additiveRow chi psi x) = 0 := by
  simp only [additiveRow, gaussSum, AddChar.mulShift_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro z _
  rw [← Finset.mul_sum]
  by_cases hz : z = 0
  · simp [hz, chi.map_zero]
  · have hn : -z ≠ 0 := neg_ne_zero.mpr hz
    have he : (∑ x : F, psi (-x*z)) = ∑ x : F, (psi.mulShift (-z)) x := by
      congr 1
      funext x
      simp only [AddChar.mulShift_apply]
      congr 1
      ring
    rw [he, AddChar.sum_eq_zero_of_ne_one (hpsi hn), mul_zero]

/-- Complete normalized coupled mean, preserving the complex Gauss phase. -/
def normalizedMean (chi : MulChar F ℂ) (psi : AddChar F ℂ) : ℂ :=
  (Fintype.card F : ℂ)⁻¹ * (Real.sqrt (Fintype.card F) : ℂ)⁻¹ *
    ∑ x : F, chi x * additiveRow chi psi x

/-- The normalized joined mean has no square-root cancellation at all. -/
theorem norm_normalizedMean (chi : MulChar F ℂ) (psi : AddChar F ℂ)
    (hchi : chi ≠ 1) (hpsi : psi.IsPrimitive) :
    ‖normalizedMean chi psi‖ = 1-(Fintype.card F : ℝ)⁻¹ := by
  have hcard : (0 : ℝ) < Fintype.card F := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0:F)⟩
  have hcard1 : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0:F)⟩
  have hneg : ‖chi (-1)‖ = 1 := by
    have h : ‖chi (-1)‖^2 = 1 := by
      rw [pow_two, ← norm_mul, ← map_mul]
      simp
    nlinarith [norm_nonneg (chi (-1))]
  rw [normalizedMean, matching_period]
  have he : (Fintype.card F : ℂ)⁻¹ * (Real.sqrt (Fintype.card F) : ℂ)⁻¹ *
      (((Fintype.card F : ℂ)-1)*chi (-1)*gaussSum chi psi) =
      (((Fintype.card F : ℝ)-1)/(Fintype.card F) : ℂ) * chi (-1) *
        ((Real.sqrt (Fintype.card F) : ℂ)⁻¹*gaussSum chi psi) := by
    push_cast
    ring
  rw [he, norm_mul, norm_mul, hneg,
    ShortDraftGauss.norm_normalized_gaussSum chi psi hchi hpsi, mul_one, mul_one]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  field_simp

/-- A uniform positive floor refutes complete-period mean-zero inference for joined rows. -/
theorem normalizedMean_lower (chi : MulChar F ℂ) (psi : AddChar F ℂ)
    (hchi : chi ≠ 1) (hpsi : psi.IsPrimitive) :
    (1/2 : ℝ) ≤ ‖normalizedMean chi psi‖ := by
  rw [norm_normalizedMean chi psi hchi hpsi]
  have hc : (2 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.one_lt_card
  have hi : (Fintype.card F : ℝ)⁻¹ ≤ (1/2 : ℝ) := by
    rw [← one_div]
    apply (div_le_iff₀ (by linarith : (0:ℝ)<Fintype.card F)).mpr
    linarith
  linarith

local notation "O" => OAI.ActualEisensteinCubic.O
open OAI.CanonicalRowCompletion OAI.ConcretePrimeRowBridge OAI.CubicEisenstein OAI.CompletedGauss
open OAI.SevenEighths.ProbePhysical OAI.GaussianShiftedPartition

/-- Exact bridge to the actual finite Eisenstein additive trace; no free phase is substituted. -/
theorem actual_gauss (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    [Fintype (O ⧸ Ideal.span {p})]
    (hg : goodLambda ∉ Ideal.span {p}) (m : O) :
    sexticGauss p hp (-m) =
      additiveRow (actualSextic (Ideal.span {p}) hg) (quotientTrace p hp)
        (Ideal.Quotient.mk _ m) := by
  unfold sexticGauss additiveRow gaussSum
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro d _
  rw [idealRowHom_prime _ _ hg, representative_spec]
  simp only [AddChar.mulShift_apply, map_neg]

/-- The genuine ideal-row factor cancels its matching genuine Gauss phase, including nonunits. -/
theorem actual_matching_atom (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    [Fintype (O ⧸ Ideal.span {p})]
    (hg : goodLambda ∉ Ideal.span {p}) (m : O) :
    idealRowHom m (Ideal.span {p}) * sexticGauss p hp (-m) =
      if m ∈ Ideal.span {p} then 0 else
        actualSextic (Ideal.span {p}) hg (-1) *
          gaussSum (actualSextic (Ideal.span {p}) hg) (quotientTrace p hp) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  rw [actual_gauss p hp hg m, idealRowHom_prime _ _ hg,
    matching_atom, Ideal.Quotient.eq_zero_iff_mem]

/-- Every valuation `6t+1` in the completed index has the SAME matching character. -/
theorem actual_matching_valuation (p : O)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (t : ℕ) (m : O) :
    idealRowHom m ((Ideal.span {p})^(6*t+1)) = idealRowHom m (Ideal.span {p}) := by
  rw [map_pow, idealRowHom_prime _ _ hg]
  have he : actualSextic (Ideal.span {p}) hg ^ (6*t+1) =
      actualSextic (Ideal.span {p}) hg := by
    have h6 : actualSextic (Ideal.span {p}) hg ^ 6 = 1 :=
      ActualEisensteinCubic.canonicalSextic_pow_six (Ideal.span {p}) hg
    rw [pow_add, pow_mul, h6,
      one_pow, pow_one, one_mul]
  rw [← MulChar.pow_apply' _ (by omega : 6*t+1 ≠ 0), he]

/-- In the actual completed `I*J^3` row, `I=p,J=p^(2t)` is always a matching channel. -/
theorem actual_completed_matching (p : O)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (t : ℕ) (m : O) :
    idealRowHom m ((Ideal.span {p}) * ((Ideal.span {p})^(2*t))^3) =
      idealRowHom m (Ideal.span {p}) := by
  have he : (Ideal.span {p}) * ((Ideal.span {p})^(2*t))^3 =
      (Ideal.span {p})^(6*t+1) := by
    rw [← pow_mul, ← pow_succ']
    congr 1
    omega
  rw [he, actual_matching_valuation p hg]

/-- The actual prime character is nonprincipal at every permitted odd-characteristic prime. -/
theorem actual_character_nonprincipal (p : O)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    actualSextic (Ideal.span {p}) hg ≠ 1 := by
  simpa only [pow_one] using
    ActualEisensteinCubic.canonicalSextic_pow_ne_one (Ideal.span {p}) hg hc
      (by norm_num : (1:ℕ) ≠ 0) (by norm_num : (1:ℕ) < 6)

/-- Complete-period matching is exactly the actual completed-index valuation `e=1 mod 6`. -/
theorem actual_valuation_period (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    [Fintype (O ⧸ Ideal.span {p})]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (e : ℕ) :
    (∑ x : O ⧸ Ideal.span {p}, (actualSextic (Ideal.span {p}) hg ^ e) x *
      additiveRow (actualSextic (Ideal.span {p}) hg) (quotientTrace p hp) x) =
      if e % 6 = 1 then
        ((Fintype.card (O ⧸ Ideal.span {p}) : ℂ)-1) *
          actualSextic (Ideal.span {p}) hg (-1) *
            gaussSum (actualSextic (Ideal.span {p}) hg) (quotientTrace p hp)
      else 0 := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  rw [cross_period]
  congr 1
  have ho := OAI.SevenEighths.CenteredMomentCanonical.actualSextic_order_six
    (Ideal.span {p}) hg hc
  have he := (pow_eq_pow_iff_modEq
    (x := actualSextic (Ideal.span {p}) hg) (n := e) (m := 1))
  rw [ho] at he
  norm_num only [pow_one, Nat.ModEq] at he
  exact propext he

/-- The completed squarefree/cube valuation `i+3j` matches precisely when `i=1,j` is even. -/
theorem completed_valuation_gate {i j : ℕ} (hi : i ≤ 1) :
    (i+3*j) % 6 = 1 ↔ i=1 ∧ j % 2 = 0 := by omega

/-- An arbitrary finite literal mask and full complex phase retain ONE signed matching sum. -/
theorem actual_masked_matching (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    [Fintype (O ⧸ Ideal.span {p})]
    (hg : goodLambda ∉ Ideal.span {p}) (t : ℕ) (B : Finset O) (w : O → ℂ) :
    (∑ m ∈ B, w m *
      idealRowHom m ((Ideal.span {p}) * ((Ideal.span {p})^(2*t))^3) *
        sexticGauss p hp (-m)) =
      (actualSextic (Ideal.span {p}) hg (-1) *
        gaussSum (actualSextic (Ideal.span {p}) hg) (quotientTrace p hp)) *
          ∑ m ∈ B.filter (fun m => m ∉ Ideal.span {p}), w m := by
  simp_rw [actual_completed_matching p hg t, mul_assoc, actual_matching_atom p hp hg]
  simp only [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : m ∈ Ideal.span {p}
  · simp [hm]
  · simp [hm, mul_comm, mul_assoc]

/-- Both genuine rows separately have zero mean but their normalized joined mean is at least one half. -/
theorem actual_separate_means_do_not_pay_join (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    [Fintype (O ⧸ Ideal.span {p})]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    (∑ x : O ⧸ Ideal.span {p}, actualSextic (Ideal.span {p}) hg x) = 0 ∧
    (∑ x : O ⧸ Ideal.span {p},
      additiveRow (actualSextic (Ideal.span {p}) hg) (quotientTrace p hp) x) = 0 ∧
    (1/2 : ℝ) ≤ ‖normalizedMean (actualSextic (Ideal.span {p}) hg) (quotientTrace p hp)‖ := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  have hchi := actual_character_nonprincipal p hg hc
  have hpsi : (quotientTrace p hp).IsPrimitive :=
    OAI.GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp
  exact ⟨residue_mean_zero _ hchi, additive_mean_zero _ _ hpsi,
    normalizedMean_lower _ _ hchi hpsi⟩

end OpenAIReview.CoupledResidue

#lint+ in OpenAIReview.CoupledResidue

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    unless (n.toString.splitOn "OpenAIReview.CoupledResidue").length > 1 do continue
    declarations := declarations + 1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems + 1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations > 0 do throwError "Empty coupled residue audit."
  logInfo m!"Coupled residue audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/quasi-rh-coupled-residue"
  IO.FS.writeFile ".lake/quasi-rh-coupled-residue/axioms.json"
    (Json.mkObj [("scope",toJson "actual finite residue matching; no full-probe or zero-source estimate"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
