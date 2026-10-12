/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.QuasiRHCalibratedMatchingAudit
import Lean.Util.CollectAxioms

/-!
# A necessary prime divisor of the actual calibrated row period

The native single-prime cofactor character, with its exact calibration and
matching-prime puncture, cannot have a full additive period that omits the
cofactor prime.  The proof retains nonunit zeros and uses a genuine CRT atom.
This does not determine the entire minimum conductor, bound an incomplete
annulus, or exclude collective cancellation across different cofactors.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2048
noncomputable section
open scoped Classical
namespace OpenAIReview.MinimalPeriod
open OAI OAI.CanonicalRowCompletion OAI.CompletedGauss OAI.ConcretePrimeRowBridge
open OAI.GaussianShiftedPartition
open OAI.CubicEisenstein hiding O
open OAI.SevenEighths.ProbePhysical
open OpenAIReview.CalibratedMatching
local notation "O" => OAI.ActualEisensteinCubic.O

/-- Native pointwise row; both multiplicative phases and all nonunit zeros remain. -/
def puncturedRow (C : CalibrationData) (b p m : O) : ℂ :=
  if m ∈ (Ideal.span {p} : Ideal O) then 0 else
    cofactorCharacter C (Ideal.span {b}) m

/-- The actual sextic prime row vanishes exactly on the prime ideal. -/
theorem prime_row_zero_iff (b m : O)
    [(Ideal.span {b} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ (Ideal.span {b} : Ideal O)) :
    idealRowHom m (Ideal.span {b}) = 0 ↔ m ∈ (Ideal.span {b} : Ideal O) := by
  let : Field (O ⧸ (Ideal.span {b} : Ideal O)) := Ideal.Quotient.field _
  rw [idealRowHom_prime _ _ hg, MulChar.apply_eq_zero_iff, isUnit_iff_ne_zero,
    not_not, Ideal.Quotient.eq_zero_iff_mem]

/-- Exact zero set, including calibration nonunits and the puncture. -/
theorem puncturedRow_zero_iff (C : CalibrationData) (b p m : O)
    [(Ideal.span {b} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ (Ideal.span {b} : Ideal O)) :
    puncturedRow C b p m = 0 ↔
      m ∈ (Ideal.span {p} : Ideal O) ∨
      ¬ IsUnit (Ideal.Quotient.mk (Ideal.span {C.generator}) m) ∨
      m ∈ (Ideal.span {b} : Ideal O) := by
  by_cases hm : m ∈ (Ideal.span {p} : Ideal O)
  · simp [puncturedRow, hm]
  · rw [puncturedRow, ite_eq_right hm, cofactorCharacter, mul_eq_zero,
      prime_row_zero_iff b m hg]
    simp only [hm, false_or]
    change C.residue (Ideal.Quotient.mk (Ideal.span {C.generator}) m) = 0 ∨ _ ↔ _
    rw [MulChar.apply_eq_zero_iff]

/-- CRT with genuine principal ideals; no free residue phases are substituted. -/
theorem exists_principal_crt (b c : O) (hcop : IsCoprime b c)
    (a : O ⧸ (Ideal.span {b} : Ideal O))
    (v : O ⧸ (Ideal.span {c} : Ideal O)) :
    ∃ n : O, Ideal.Quotient.mk (Ideal.span {b}) n = a ∧
      Ideal.Quotient.mk (Ideal.span {c}) n = v := by
  let e := Ideal.quotientMulEquivQuotientProd
    (Ideal.span {b} : Ideal O) (Ideal.span {c})
    ((Ideal.isCoprime_span_singleton_iff b c).mpr hcop)
  obtain ⟨n, hn⟩ := Ideal.Quotient.mk_surjective (e.symm (a,v))
  have he : e (Ideal.Quotient.mk
      ((Ideal.span {b} : Ideal O) * Ideal.span {c}) n) = (a,v) := by
    rw [hn, e.apply_symm_apply]
  refine ⟨n, ?_, ?_⟩
  · simpa [e] using congrArg Prod.fst he
  · simpa [e] using congrArg Prod.snd he

/-- If a translate is not divisible by the cofactor prime, CRT constructs
an exact zero atom whose translate is an actual nonzero calibrated atom. -/
theorem exists_zero_nonzero_translate (C : CalibrationData) (b p r : O)
    [(Ideal.span {b} : Ideal O).IsMaximal]
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ (Ideal.span {b} : Ideal O))
    (hcop : IsCoprime b (C.generator*p))
    (hr : r ∉ (Ideal.span {b} : Ideal O)) :
    ∃ m : O, puncturedRow C b p m = 0 ∧ puncturedRow C b p (m+r) ≠ 0 := by
  obtain ⟨n, hnb, hnc⟩ := exists_principal_crt b (C.generator*p) hcop
    (Ideal.Quotient.mk (Ideal.span {b}) r) 1
  have hnbmem : n-r ∈ (Ideal.span {b} : Ideal O) := Ideal.Quotient.eq.mp hnb
  have hnc1 : Ideal.Quotient.mk (Ideal.span {C.generator*p}) n =
      Ideal.Quotient.mk (Ideal.span {C.generator*p}) 1 := by simpa using hnc
  have hdiv : C.generator*p ∣ n-1 :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hnc1)
  have hnC : Ideal.Quotient.mk (Ideal.span {C.generator}) n = 1 := by
    simpa using (Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr
      ((dvd_mul_right C.generator p).trans hdiv)))
  have hnP : Ideal.Quotient.mk (Ideal.span {p}) n = 1 := by
    simpa using (Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr
      ((dvd_mul_left p C.generator).trans hdiv)))
  have hnp : n ∉ (Ideal.span {p} : Ideal O) := by
    intro hn
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hn
    rw [hnP] at hz
    exact one_ne_zero hz
  have hnnB : n ∉ (Ideal.span {b} : Ideal O) := by
    intro hn
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hn
    rw [hnb] at hz
    exact hr (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hC : C.residueMonoid n = 1 := by
    change C.residue (Ideal.Quotient.mk (Ideal.span {C.generator}) n) = 1
    rw [hnC, map_one]
  have hnrow : puncturedRow C b p n ≠ 0 := by
    simp only [puncturedRow, ite_eq_right hnp, cofactorCharacter, hC, one_mul]
    exact mt (prime_row_zero_iff b n hg).mp hnnB
  refine ⟨n-r, (puncturedRow_zero_iff C b p (n-r) hg).mpr
    (Or.inr (Or.inr hnbmem)), ?_⟩
  simpa only [sub_add_cancel] using hnrow

/-- Even preservation of the full nonunit zero locus retains the cofactor prime. -/
theorem zero_locus_period_mem_cofactor (C : CalibrationData) (b p r : O)
    [(Ideal.span {b} : Ideal O).IsMaximal]
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ (Ideal.span {b} : Ideal O))
    (hcop : IsCoprime b (C.generator*p))
    (hperiod : ∀ m : O, puncturedRow C b p (m+r) = 0 ↔ puncturedRow C b p m = 0) :
    r ∈ (Ideal.span {b} : Ideal O) := by
  by_contra hr
  obtain ⟨m, hm, hmr⟩ := exists_zero_nonzero_translate C b p r hg hcop hr
  exact hmr ((hperiod m).mpr hm)

/-- The two genuine prime roles have the same zero locus, although their
nonzero sextic phases need not agree. -/
theorem prime_zero_locus_swap (C : CalibrationData) (b p m : O)
    [(Ideal.span {b} : Ideal O).IsMaximal]
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hgb : goodLambda ∉ (Ideal.span {b} : Ideal O))
    (hgp : goodLambda ∉ (Ideal.span {p} : Ideal O)) :
    puncturedRow C b p m = 0 ↔ puncturedRow C p b m = 0 := by
  rw [puncturedRow_zero_iff C b p m hgb, puncturedRow_zero_iff C p b m hgp]
  tauto

/-- Every full additive period of this actual row retains the cofactor prime. -/
theorem translation_period_mem_cofactor (C : CalibrationData) (b p r : O)
    [(Ideal.span {b} : Ideal O).IsMaximal]
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ (Ideal.span {b} : Ideal O))
    (hcop : IsCoprime b (C.generator*p))
    (hperiod : ∀ m : O, puncturedRow C b p (m+r) = puncturedRow C b p m) :
    r ∈ (Ideal.span {b} : Ideal O) := by
  by_contra hr
  obtain ⟨m, hm, hmr⟩ := exists_zero_nonzero_translate C b p r hg hcop hr
  exact hmr ((hperiod m).trans hm)

/-- The necessary period divisibility, stated in the native integer ring. -/
theorem translation_period_dvd_cofactor (C : CalibrationData) (b p r : O)
    [(Ideal.span {b} : Ideal O).IsMaximal]
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ (Ideal.span {b} : Ideal O))
    (hcop : IsCoprime b (C.generator*p))
    (hperiod : ∀ m : O, puncturedRow C b p (m+r) = puncturedRow C b p m) :
    b ∣ r :=
  Ideal.mem_span_singleton.mp (translation_period_mem_cofactor C b p r hg hcop hperiod)

/-- The puncture prime also divides a full row period; swapping is used only
for the exact zero locus, never for the complex row phases. -/
theorem translation_period_dvd_puncture (C : CalibrationData) (b p r : O)
    [(Ideal.span {b} : Ideal O).IsMaximal]
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hgb : goodLambda ∉ (Ideal.span {b} : Ideal O))
    (hgp : goodLambda ∉ (Ideal.span {p} : Ideal O))
    (hcop : IsCoprime p (C.generator*b))
    (hperiod : ∀ m : O, puncturedRow C b p (m+r) = puncturedRow C b p m) :
    p ∣ r := by
  apply Ideal.mem_span_singleton.mp
  apply zero_locus_period_mem_cofactor C p b r hgp hcop
  intro m
  rw [← prime_zero_locus_swap C b p (m+r) hgb hgp,
    ← prime_zero_locus_swap C b p m hgb hgp, hperiod m]

/-- Both growing prime factors, not just the calibration, survive every full period. -/
theorem translation_period_dvd_product (C : CalibrationData) (b p r : O)
    [(Ideal.span {b} : Ideal O).IsMaximal]
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hgb : goodLambda ∉ (Ideal.span {b} : Ideal O))
    (hgp : goodLambda ∉ (Ideal.span {p} : Ideal O))
    (hcopB : IsCoprime b (C.generator*p))
    (hcopP : IsCoprime p (C.generator*b))
    (hperiod : ∀ m : O, puncturedRow C b p (m+r) = puncturedRow C b p m) :
    b*p ∣ r :=
  hcopB.of_mul_right_right.mul_dvd
    (translation_period_dvd_cofactor C b p r hgb hcopB hperiod)
    (translation_period_dvd_puncture C b p r hgb hgp hcopP hperiod)

/-- A full ideal of additive periods also retains this native prime divisor. -/
theorem period_ideal_le_cofactor (C : CalibrationData) (b p : O) (Q : Ideal O)
    [(Ideal.span {b} : Ideal O).IsMaximal]
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ (Ideal.span {b} : Ideal O))
    (hcop : IsCoprime b (C.generator*p))
    (hperiod : ∀ m n : O, m-n ∈ Q → puncturedRow C b p m = puncturedRow C b p n) :
    Q ≤ (Ideal.span {b} : Ideal O) := by
  intro r hr
  apply translation_period_mem_cofactor C b p r hg hcop
  intro m
  apply hperiod
  simpa only [add_sub_cancel_left] using hr

/-- Nonzero period elements cannot have norm smaller than the actual cofactor prime. -/
theorem period_norm_lower (C : CalibrationData) (b p r : O)
    [(Ideal.span {b} : Ideal O).IsMaximal]
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ (Ideal.span {b} : Ideal O))
    (hcop : IsCoprime b (C.generator*p)) (hr : r ≠ 0)
    (hperiod : ∀ m : O, puncturedRow C b p (m+r) = puncturedRow C b p m) :
    elementNorm b ≤ elementNorm r := by
  obtain ⟨c, hrc⟩ := translation_period_dvd_cofactor C b p r hg hcop hperiod
  have hc : c ≠ 0 := by
    intro hz
    apply hr
    rw [hrc, hz, mul_zero]
  have hn : 1 ≤ (Ideal.span {c} : Ideal O).absNorm :=
    Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hc))
  have hc1 : (1 : ℝ) ≤ elementNorm c := by
    unfold elementNorm
    exact_mod_cast hn
  have hb0 : (0 : ℝ) ≤ elementNorm b := by unfold elementNorm; positivity
  rw [hrc, elementNorm_mul]
  nlinarith

/-- This lower bound retains exactly the two native growing period factors. -/
theorem period_product_norm_lower (C : CalibrationData) (b p r : O)
    [(Ideal.span {b} : Ideal O).IsMaximal]
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hgb : goodLambda ∉ (Ideal.span {b} : Ideal O))
    (hgp : goodLambda ∉ (Ideal.span {p} : Ideal O))
    (hcopB : IsCoprime b (C.generator*p))
    (hcopP : IsCoprime p (C.generator*b)) (hr : r ≠ 0)
    (hperiod : ∀ m : O, puncturedRow C b p (m+r) = puncturedRow C b p m) :
    elementNorm b * elementNorm p ≤ elementNorm r := by
  obtain ⟨c, hrc⟩ := translation_period_dvd_product C b p r hgb hgp hcopB hcopP hperiod
  have hc : c ≠ 0 := by
    intro hz
    apply hr
    rw [hrc, hz, mul_zero]
  have hn : 1 ≤ (Ideal.span {c} : Ideal O).absNorm :=
    Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hc))
  have hc1 : (1 : ℝ) ≤ elementNorm c := by
    unfold elementNorm
    exact_mod_cast hn
  have h0 : (0 : ℝ) ≤ elementNorm b * elementNorm p := by
    unfold elementNorm
    positivity
  rw [hrc, elementNorm_mul, elementNorm_mul]
  nlinarith

/-- A nonzero constant matching Gauss prefactor cannot hide the period obstruction. -/
theorem scaled_translation_period_dvd (C : CalibrationData) (b p r : O) (c : ℂ)
    [(Ideal.span {b} : Ideal O).IsMaximal]
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ (Ideal.span {b} : Ideal O))
    (hcop : IsCoprime b (C.generator*p)) (hc : c ≠ 0)
    (hperiod : ∀ m : O, c * puncturedRow C b p (m+r) = c * puncturedRow C b p m) :
    b ∣ r := by
  apply translation_period_dvd_cofactor C b p r hg hcop
  intro m
  exact mul_left_cancel₀ hc (hperiod m)

/-- Direct endpoint for the actual calibrated numerator times its actual
additive Gauss row.  Every matching valuation and nonunit atom is retained. -/
theorem actual_matching_period_dvd (C : CalibrationData) (b p r A : O)
    (hp : p ≠ 0)
    [(Ideal.span {b} : Ideal O).IsMaximal]
    [(Ideal.span {p} : Ideal O).IsMaximal]
    [Fintype (O ⧸ (Ideal.span {p} : Ideal O))]
    (hgb : goodLambda ∉ (Ideal.span {b} : Ideal O))
    (hgp : goodLambda ∉ (Ideal.span {p} : Ideal O))
    (hc : ringChar (O ⧸ (Ideal.span {p} : Ideal O)) ≠ 2)
    (hcop : IsCoprime b (C.generator*p)) (t : ℕ)
    (hA : (Ideal.span {A} : Ideal O) = (Ideal.span {p})^(6*t+1)*Ideal.span {b})
    (hperiod : ∀ m : O,
      calibratedNumerator C A (m+r) * sexticGauss p hp (-(m+r)) =
        calibratedNumerator C A m * sexticGauss p hp (-m)) :
    b ∣ r := by
  apply scaled_translation_period_dvd C b p r
    (actualSextic (Ideal.span {p}) hgp (-1) *
      gaussSum (actualSextic (Ideal.span {p}) hgp) (quotientTrace p hp)) hgb hcop
    (OpenAIReview.CoupledSummand.actual_matching_constant_ne_zero p hp hgp hc)
  intro m
  simpa only [calibrated_matching_atom C p hp hgp t (Ideal.span {b}) A _ hA,
    puncturedRow] using hperiod m

/-- In the native calibrated matching row both growing prime factors remain
necessary; only a fixed calibration factor may be absent from this lower bound. -/
theorem actual_matching_period_dvd_product (C : CalibrationData) (b p r A : O)
    (hp : p ≠ 0)
    [(Ideal.span {b} : Ideal O).IsMaximal]
    [(Ideal.span {p} : Ideal O).IsMaximal]
    [Fintype (O ⧸ (Ideal.span {p} : Ideal O))]
    (hgb : goodLambda ∉ (Ideal.span {b} : Ideal O))
    (hgp : goodLambda ∉ (Ideal.span {p} : Ideal O))
    (hc : ringChar (O ⧸ (Ideal.span {p} : Ideal O)) ≠ 2)
    (hcopB : IsCoprime b (C.generator*p))
    (hcopP : IsCoprime p (C.generator*b)) (t : ℕ)
    (hA : (Ideal.span {A} : Ideal O) = (Ideal.span {p})^(6*t+1)*Ideal.span {b})
    (hperiod : ∀ m : O,
      calibratedNumerator C A (m+r) * sexticGauss p hp (-(m+r)) =
        calibratedNumerator C A m * sexticGauss p hp (-m)) :
    b*p ∣ r := by
  apply translation_period_dvd_product C b p r hgb hgp hcopB hcopP
  intro m
  apply mul_left_cancel₀
    (OpenAIReview.CoupledSummand.actual_matching_constant_ne_zero p hp hgp hc)
  simpa only [calibrated_matching_atom C p hp hgp t (Ideal.span {b}) A _ hA,
    puncturedRow] using hperiod m

end OpenAIReview.MinimalPeriod

#lint+ in OpenAIReview.MinimalPeriod

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations>0 do throwError "Empty minimum-period audit."
  logInfo m!"Minimum period audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-minimal-period"
  IO.FS.writeFile ".lake/arithmetic-operator-minimal-period/axioms.json"
    (Json.mkObj [("scope",toJson "necessary single-prime cofactor divisibility for genuine full additive periods; no incomplete annular estimate or collective cofactor no-go"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
