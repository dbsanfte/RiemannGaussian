/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Detector.PhysicalRows
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# A lossless finite border for the literal joined native row

The prescribed spectral Mobius vector is retained, together with actual physical
weights, spectral Gauss coefficients, all cube orders, masks and corrections.
The border determinant is exactly the original finite signed statistic. Bare
column-unit determinant/Gram invariance supplies no estimate on that statistic.
No global source, common integral Frobenius closure or new saving is asserted.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open scoped BigOperators Classical
namespace OpenAIReview.BorderedStatistic
open OAI OAI.ActualEisensteinCubic OAI.CompletedGauss
  OAI.SevenEighths OAI.SevenEighths.ProbePhysical OAI.SevenEighths.ProbeRow
local notation "Id" => Ideal OAI.ActualEisensteinCubic.O

/-- A rectangular kernel and its two prescribed vectors, in one square border. -/
def finiteBorder {n m : ℕ} (K : Matrix (Fin n) (Fin m) ℂ)
    (u : Fin n → ℂ) (v : Fin m → ℂ) :
    Matrix (Fin n ⊕ (Fin m ⊕ Fin 1)) (Fin n ⊕ (Fin m ⊕ Fin 1)) ℂ :=
  Matrix.fromBlocks 1 (fun i j => Sum.elim (fun j => K i j) (fun _ => 0) j)
    (fun a i => Sum.elim (fun _ => 0) (fun _ => u i) a)
    (Matrix.fromBlocks 1 (fun j _ => v j) 0 0)

/-- Two exact Schur eliminations recover the signed bilinear statistic. -/
theorem finiteBorder_det {n m : ℕ} (K : Matrix (Fin n) (Fin m) ℂ)
    (u : Fin n → ℂ) (v : Fin m → ℂ) :
    (finiteBorder K u v).det = ∑ i, ∑ j, u i * K i j * v j := by
  unfold finiteBorder
  erw [Matrix.det_fromBlocks_one₁₁]
  have hblock :
      Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) (fun j (_ : Fin 1) => v j) 0 0 -
        (Matrix.of (fun (a : Fin m ⊕ Fin 1) (i : Fin n) => Sum.elim (fun _ => 0) (fun _ => u i) a)) *
          (Matrix.of (fun (i : Fin n) (a : Fin m ⊕ Fin 1) => Sum.elim (fun j => K i j) (fun _ => 0) a)) =
      Matrix.fromBlocks 1 (fun j (_ : Fin 1) => v j)
        (fun (_ : Fin 1) j => -(∑ i, u i * K i j)) 0 := by
    ext a b
    cases a <;> cases b <;> simp [Matrix.mul_apply, Matrix.fromBlocks]
  erw [hblock, Matrix.det_fromBlocks_one₁₁, Matrix.det_fin_one]
  erw [Matrix.sub_apply, Matrix.zero_apply, Matrix.mul_apply]
  simp only [zero_sub, neg_mul, Finset.sum_neg_distrib, neg_neg]
  simp_rw [Finset.sum_mul]
  exact Finset.sum_comm


/-- A genuine actual physical/spectral finite join, with no deleted local factor. -/
def nativeFiniteJoin {n m : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Id) (W0 W1 : ℝ → ℂ) (X Y : ℝ) (t : ℂ)
    (r : Fin n → PhysicalRowIndex) (c : Fin m → Id × Id) : ℂ :=
  ∑ i, ∑ j, physicalRowWeight C W0 W1 X Y (r i) *
    spectralSummand C.excluded D (physicalRowMonoid η C (r i)) t (c j).1 (c j).2

/-- Actual squarefree spectral Mobius sign; zero off its supported population. -/
def nativeMu (I : Id) : ℂ := (UniqueFactorizationMonoid.moebius I : ℂ)

/-- The squarefree Gauss slot annihilates the nonsquarefree Mobius-zero population. -/
theorem nativeMu_sq_spectral (S : Finset Id) (D I J : Id)
    (Ψ : OAI.ActualEisensteinCubic.O →* ℂ) (t : ℂ) :
    nativeMu I ^ 2 * spectralSummand S D Ψ t I J = spectralSummand S D Ψ t I J := by
  by_cases hs : Squarefree I
  · have hi : UniqueFactorizationMonoid.moebius I ^ 2 = (1 : ℤ) := by
      rw [hs.moebius_eq, ← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    have hc : nativeMu I ^ 2 = 1 := by
      unfold nativeMu
      exact_mod_cast hi
    rw [hc, one_mul]
  · simp [spectralSummand, columnWeight, squarefreeGaussCoefficient, hs]

/-- Only the actual Mobius sign is peeled; every native coefficient remains literal. -/
def nativeKernel {n m : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Id) (t : ℂ) (r : Fin n → PhysicalRowIndex) (c : Fin m → Id × Id) :
    Matrix (Fin n) (Fin m) ℂ :=
  fun i j => nativeMu (c j).1 *
    spectralSummand C.excluded D (physicalRowMonoid η C (r i)) t (c j).1 (c j).2

/-- The border keeps the actual spectral Mobius vector and the actual physical row. -/
def nativeBorder {n m : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Id) (W0 W1 : ℝ → ℂ) (X Y : ℝ) (t : ℂ)
    (r : Fin n → PhysicalRowIndex) (c : Fin m → Id × Id) :=
  finiteBorder (nativeKernel η C D t r c)
    (fun i => physicalRowWeight C W0 W1 X Y (r i)) (fun j => nativeMu (c j).1)

/-- Exact native border collapse: no new estimate or source constraint is created. -/
theorem nativeBorder_det {n m : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Id) (W0 W1 : ℝ → ℂ) (X Y : ℝ) (t : ℂ)
    (r : Fin n → PhysicalRowIndex) (c : Fin m → Id × Id) :
    (nativeBorder η C D W0 W1 X Y t r c).det =
      nativeFiniteJoin η C D W0 W1 X Y t r c := by
  rw [nativeBorder, finiteBorder_det]
  unfold nativeFiniteJoin nativeKernel
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have he := nativeMu_sq_spectral C.excluded D (c j).1 (c j).2
    (physicalRowMonoid η C (r i)) t
  calc
    _ = physicalRowWeight C W0 W1 X Y (r i) *
        (nativeMu (c j).1 ^ 2 * spectralSummand C.excluded D
          (physicalRowMonoid η C (r i)) t (c j).1 (c j).2) := by ring
    _ = _ := by rw [he]

/-- Bare square determinants retain column phases only as one scalar product. -/
theorem columnPhase_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ) :
    (A * Matrix.diagonal d).det = A.det * ∏ i, d i := by
  rw [Matrix.det_mul, Matrix.det_diagonal]

/-- Modulus-one column phases, including every supported Mobius sign, are invisible here. -/
theorem columnPhase_norm_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → ℂ) (hd : ∀ i, ‖d i‖ = 1) :
    ‖(A * Matrix.diagonal d).det‖ = ‖A.det‖ := by
  rw [columnPhase_det, norm_mul, norm_prod]
  simp [hd]

/-- The actual supported Mobius column is a modulus-one diagonal. -/
theorem nativeMu_norm (I : Id) (hs : Squarefree I) : ‖nativeMu I‖ = 1 := by
  unfold nativeMu
  rw [hs.moebius_eq, Int.cast_pow, Int.cast_neg, Int.cast_one, norm_pow]
  norm_num

/-- Bare determinant norm cannot distinguish the prescribed native Mobius signs. -/
theorem nativeMu_norm_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (I : Fin n → Id) (hs : ∀ i, Squarefree (I i)) :
    ‖(A * Matrix.diagonal (fun i => nativeMu (I i))).det‖ = ‖A.det‖ := by
  exact columnPhase_norm_det A _ (fun i => nativeMu_norm _ (hs i))

end OpenAIReview.BorderedStatistic

#lint+ in OpenAIReview.BorderedStatistic

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations + 1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems + 1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations > 0 do throwError "Empty native border audit."
  logInfo m!"Native-border audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-bordered-gauss-preflight"
  IO.FS.writeFile ".lake/arithmetic-operator-bordered-gauss-preflight/axioms.json"
    (Json.mkObj [("scope",toJson "literal finite physicalRowWeight/spectralSummand border with actual Mobius; determinant collapse and column-unit norm invariance only"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),("declarations",toJson declarations),
      ("theoremsIncludingGeneratedHelpers",toJson theorems),("declarationAxioms",Json.arr reports)]).pretty
