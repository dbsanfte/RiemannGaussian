/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.CubicSieve.Sharp
import OAI.NumberTheory.DirichletL.CubicSieve.Gcd
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
Actual sharp cubic energy on the native squarefree ideal ranges. Coefficients
are fixed across rows. Row and column contractions are separate: no arbitrary
pair-dependent mask is asserted. The residue-to-cubic bridge is not asserted.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0
noncomputable section
open scoped Classical BigOperators
namespace OpenAIReview.SquareCubicMean
open OAI OAI.SevenEighths.CubicSieve OAI.CompletedGauss

/-- Literal native cubic row equals the imported sieve kernel. -/
theorem cubicRow_eq_idealKernel (I J : Ideal ActualEisensteinCubic.O) :
    cubicRow I (primaryGenerator J) = idealKernel I J := rfl

/-- Separate bounded masks preserve coefficient mass and output energy. -/
theorem masked_energy_le (M N : ℝ) (b c : idealRange N → ℂ)
    (r : idealRange M → ℂ) (hc : ∀ j, ‖c j‖ ≤ 1) (hr : ∀ i, ‖r i‖ ≤ 1) :
    (∑ i : idealRange M, ‖r i * ∑ j : idealRange N,
      cubicRow j.val (primaryGenerator i.val) * (c j * b j)‖ ^ 2) ≤
      sieveNorm M N * ∑ j, ‖b j‖ ^ 2 := by
  have hn : 0 ≤ sieveNorm M N := by
    unfold sieveNorm squaredNorm
    positivity
  calc
    _ ≤ ∑ i : idealRange M, ‖∑ j : idealRange N,
        idealKernel j.val i.val * (c j * b j)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      simp only [cubicRow_eq_idealKernel, norm_mul]
      exact pow_le_pow_left₀ (by positivity)
        (mul_le_of_le_one_left (norm_nonneg _) (hr i)) 2
    _ ≤ sieveNorm M N * ∑ j, ‖c j * b j‖ ^ 2 := ideal_energy_bound M N _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hn
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact pow_le_pow_left₀ (by positivity)
        (mul_le_of_le_one_left (norm_nonneg _) (hc j)) 2

/-- Genuine imported arithmetic estimate, with the full rectangular shape. -/
theorem rectangular_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      ∀ (b c : idealRange N → ℂ) (r : idealRange M → ℂ),
        (∀ j, ‖c j‖ ≤ 1) → (∀ i, ‖r i‖ ≤ 1) →
        (∑ i : idealRange M, ‖r i * ∑ j : idealRange N,
          cubicRow j.val (primaryGenerator i.val) * (c j * b j)‖ ^ 2) ≤
          K * (M * N) ^ ε * (M + N + (M * N) ^ (2/3 : ℝ)) *
            ∑ j, ‖b j‖ ^ 2 := by
  obtain ⟨K, hK, hb⟩ := sieveNorm_sharp ε hε
  refine ⟨K, hK, ?_⟩
  intro M N hM hN b c r hc hr
  exact (masked_energy_le M N b c r hc hr).trans
    (mul_le_mul_of_nonneg_right (hb M N hM hN) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-- Exact balanced exponent payment, including the dyadic upper endpoint 2A. -/
theorem balanced_shape {A ε : ℝ} (hA : 1 ≤ A) :
    A ^ (-(1/3 : ℝ)) * (A * (2*A)) ^ (ε/2) *
      (A + 2*A + (A * (2*A)) ^ (2/3 : ℝ)) ≤
        (5 * (2 : ℝ) ^ (ε/2)) * A ^ (1+ε) := by
  have hA0 : 0 < A := by linarith
  have hAA : (A * (2*A)) ^ (2/3 : ℝ) =
      (2 : ℝ) ^ (2/3 : ℝ) * A ^ (4/3 : ℝ) := by
    rw [show A*(2*A)=2*(A*A) by ring, Real.mul_rpow (by norm_num) (by positivity),
      Real.mul_rpow hA0.le hA0.le, ← Real.rpow_add hA0]
    norm_num
  have h2 : (2 : ℝ) ^ (2/3 : ℝ) ≤ 2 := by
    calc
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := Real.rpow_one _
  have ha : A ≤ A ^ (4/3 : ℝ) := by
    conv_lhs => rw [← Real.rpow_one A]
    exact Real.rpow_le_rpow_of_exponent_le hA (by norm_num)
  have hs : A + 2*A + (A*(2*A))^(2/3 : ℝ) ≤ 5*A^(4/3 : ℝ) := by
    rw [hAA]
    nlinarith [mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hA0.le (4/3 : ℝ))]
  calc
    _ ≤ A ^ (-(1/3 : ℝ)) * (A * (2*A)) ^ (ε/2) * (5*A^(4/3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by
      rw [show A*(2*A)=2*(A*A) by ring, Real.mul_rpow (by norm_num) (by positivity),
        Real.mul_rpow hA0.le hA0.le]
      calc
        _ = (5*(2 : ℝ)^(ε/2)) *
            (A^(-(1/3 : ℝ)) * A^(ε/2) * A^(ε/2) * A^(4/3 : ℝ)) := by ring
        _ = _ := by
          rw [← Real.rpow_add hA0, ← Real.rpow_add hA0, ← Real.rpow_add hA0]
          congr 2
          ring

/-- Balanced actual cubic row energy for arbitrary fixed complex coefficients.
Column masks may encode any prescribed subset, including a dyadic annulus. -/
theorem balanced_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 1 ≤ A →
      ∀ (b c : idealRange (2*A) → ℂ) (r : idealRange A → ℂ),
        (∀ j, ‖c j‖ ≤ 1) → (∀ i, ‖r i‖ ≤ 1) →
        A ^ (-(1/3 : ℝ)) *
          (∑ i : idealRange A, ‖r i * ∑ j : idealRange (2*A),
            cubicRow j.val (primaryGenerator i.val) * (c j * b j)‖ ^ 2) ≤
          K * A ^ (1+ε) * ∑ j, ‖b j‖ ^ 2 := by
  obtain ⟨K, hK, hb⟩ := rectangular_energy (ε/2) (by positivity)
  refine ⟨K * (5*(2 : ℝ)^(ε/2)), by positivity, ?_⟩
  intro A hA b c r hc hr
  have he := hb A (2*A) hA (by linarith) b c r hc hr
  have hs := balanced_shape (ε := ε) hA
  calc
    _ ≤ A ^ (-(1/3 : ℝ)) *
        (K * (A*(2*A))^(ε/2) * (A+2*A+(A*(2*A))^(2/3 : ℝ)) * ∑ j, ‖b j‖^2) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = K * (A^(-(1/3 : ℝ)) * (A*(2*A))^(ε/2) *
        (A+2*A+(A*(2*A))^(2/3 : ℝ))) * ∑ j, ‖b j‖^2 := by ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hs hK.le
      have hh' := mul_le_mul_of_nonneg_right hh (show 0 ≤ ∑ j : idealRange (2*A), ‖b j‖^2 from Finset.sum_nonneg (fun j _ => sq_nonneg ‖b j‖))
      convert hh' using 1; ring

/-- Coefficient mass may be any stated bound, including C or C log A.
The output constant is uniform over all fixed vectors and separate masks. -/
theorem balanced_energy_mass (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ A B : ℝ, 1 ≤ A →
      ∀ (b c : idealRange (2*A) → ℂ) (r : idealRange A → ℂ),
        (∀ j, ‖c j‖ ≤ 1) → (∀ i, ‖r i‖ ≤ 1) →
        (∑ j, ‖b j‖^2) ≤ B →
        A ^ (-(1/3 : ℝ)) *
          (∑ i : idealRange A, ‖r i * ∑ j : idealRange (2*A),
            cubicRow j.val (primaryGenerator i.val) * (c j * b j)‖ ^ 2) ≤
          K * A ^ (1+ε) * B := by
  obtain ⟨K, hK, hb⟩ := balanced_energy ε hε
  refine ⟨K, hK, ?_⟩
  intro A B hA b c r hc hr hmass
  exact (hb A hA b c r hc hr).trans
    (mul_le_mul_of_nonneg_left hmass (by positivity))

/-- The nonbalanced actual mean retains the exact cubic shape. Only nonempty
native scale hypotheses are required; no D or K losses are silently discarded. -/
theorem normalized_rectangular_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ A M N : ℝ, 1 ≤ A → 1 ≤ M → 1 ≤ N →
      ∀ (b c : idealRange N → ℂ) (r : idealRange M → ℂ),
        (∀ j, ‖c j‖ ≤ 1) → (∀ i, ‖r i‖ ≤ 1) →
        A ^ (-(1/3 : ℝ)) *
          (∑ i : idealRange M, ‖r i * ∑ j : idealRange N,
            cubicRow j.val (primaryGenerator i.val) * (c j * b j)‖ ^ 2) ≤
          K * A ^ (-(1/3 : ℝ)) * (M*N)^ε *
            (M+N+(M*N)^(2/3 : ℝ)) * ∑ j, ‖b j‖^2 := by
  obtain ⟨K, hK, hb⟩ := rectangular_energy ε hε
  refine ⟨K, hK, ?_⟩
  intro A M N hA hM hN b c r hc hr
  have hh := mul_le_mul_of_nonneg_left (hb M N hM hN b c r hc hr)
    (show 0 ≤ A ^ (-(1/3 : ℝ)) from Real.rpow_nonneg (by linarith) _)
  convert hh using 1; ring

end OpenAIReview.SquareCubicMean
#lint+ in OpenAIReview.SquareCubicMean

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut details : Array Json := #[]
  for (n, ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations + 1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems + 1
    details := details.push (Json.mkObj [("declaration", toJson n.toString),
      ("isTheorem", toJson ci.isTheorem), ("axioms", toJson (axs.map Name.toString))])
  unless declarations > 0 do throwError "Empty native cubic mean audit."
  logInfo m!"Native cubic mean audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-square-cubic-mean"
  IO.FS.writeFile ".lake/arithmetic-operator-square-cubic-mean/axioms.json"
    (Json.mkObj [("scope", toJson "actual imported sharp cubic sieve for squarefree ideals; fixed coefficients and separate row/column masks; no rho bridge"),
      ("namespaceLinters", toJson (15 : Nat)), ("onlyStandardAxioms", toJson true),
      ("allLocalModuleProvenance", toJson true),
      ("declarations", toJson declarations), ("theoremsIncludingHelpers", toJson theorems),
      ("details", Json.arr details)]).pretty
