/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.QuasiRHCoupledSummandAudit
import OAI.NumberTheory.DirichletL.Detector.GaussianSlots
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Exact shared-prime cube support in the native compact annulus

Both ideal slots and the actual complex height/twist are kept. If a
matching prime divides both slots, their total physical norm is at least
the fourth power of its norm. The native compact window is then exactly
zero when that norm exceeds twice the moving length.

This removes only positive SAME-prime cube incidences. The ordinary
cube-order-zero cofactor channel is not removed or estimated. No signed
whole-row saving, hypothetical-zero source limit, or new contour follows.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2048
noncomputable section
open scoped BigOperators Classical Topology

namespace OpenAIReview.MatchingCubeGeometry
open OAI OAI.CompletedGauss OAI.SevenEighths.ProbePhysical
open Filter
local notation "O" => OAI.ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem norm_le_of_ideal_dvd (P A : Id) (hA : A ≠ 0) (hPA : P ∣ A) :
    (Ideal.absNorm P : ℝ) ≤ Ideal.absNorm A := by
  have hd := Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hPA)
  have hp : 0 < Ideal.absNorm A :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hA)
  exact_mod_cast Nat.le_of_dvd hp hd

/-- Genuine ideal divisibility, not a prescribed continuous share model. -/
theorem shared_prime_total_norm (P I J : Id) (hI : I ≠ 0) (hJ : J ≠ 0)
    (hPI : P ∣ I) (hPJ : P ∣ J) :
    (Ideal.absNorm P : ℝ)^4 ≤
      (Ideal.absNorm I : ℝ)*(Ideal.absNorm J : ℝ)^3 := by
  have hi := norm_le_of_ideal_dvd P I hI hPI
  have hj := norm_le_of_ideal_dvd P J hJ hPJ
  have hp : 0 ≤ (Ideal.absNorm P : ℝ) := by positivity
  calc
    _ = (Ideal.absNorm P : ℝ)*(Ideal.absNorm P : ℝ)^3 := by ring
    _ ≤ _ := by gcongr

theorem physical_argument_ge_two (P I J : Id) (hI : I ≠ 0) (hJ : J ≠ 0)
    (hPI : P ∣ I) (hPJ : P ∣ J) {X : ℝ} (hX : 0 < X)
    (hlarge : 2*X ≤ (Ideal.absNorm P : ℝ)^4) :
    2 ≤ (Ideal.absNorm I : ℝ)*(Ideal.absNorm J : ℝ)^3/X := by
  rw [le_div_iff₀ hX]
  exact hlarge.trans (shared_prime_total_norm P I J hI hJ hPI hPJ)

/-- Both Fourier/height phases remain; compact support kills the atom first. -/
theorem actual_shared_cube_atom_zero (Ψ : O →* ℂ) (P I J : Id)
    (hI : I ≠ 0) (hJ : J ≠ 0) (hPI : P ∣ I) (hPJ : P ∣ J)
    (t X : ℝ) (hX : 0 < X) (hlarge : 2*X ≤ (Ideal.absNorm P : ℝ)^4) :
    summand Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) X I J = 0 := by
  have ha := physical_argument_ge_two P I J hI hJ hPI hPJ hX hlarge
  unfold summand Vstar CompletedHeight.normTwistedSource
  rw [gaussianFixedWindow_large _ ha]
  ring

/-- An arbitrary literal mark is retained, rather than completed. -/
theorem actual_shared_cube_marked_atom_zero (Ψ : O →* ℂ) (P I J : Id)
    (hI : I ≠ 0) (hJ : J ≠ 0) (hPI : P ∣ I) (hPJ : P ∣ J)
    (d : Id → ℂ) (t X : ℝ) (hX : 0 < X)
    (hlarge : 2*X ≤ (Ideal.absNorm P : ℝ)^4) :
    summand Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) X I J *
      d (I*J^3) = 0 := by
  rw [actual_shared_cube_atom_zero Ψ P I J hI hJ hPI hPJ t X hX hlarge, zero_mul]

/-- The matching column retains all J not divisible by the matched prime.
This is not a statement that J itself must be one. -/
theorem finite_matching_column_eq_unshared (Ψ : O →* ℂ) (P I : Id)
    (hI : I ≠ 0) (hPI : P ∣ I) (F : Finset Id)
    (hF : ∀ J ∈ F, J ≠ 0) (d : Id → ℂ) (t X : ℝ) (hX : 0 < X)
    (hlarge : 2*X ≤ (Ideal.absNorm P : ℝ)^4) :
    (∑ J ∈ F, summand Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t)
      X I J * d (I*J^3)) =
    ∑ J ∈ F, if P ∣ J then 0 else
      summand Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t)
        X I J * d (I*J^3) := by
  apply Finset.sum_congr rfl
  intro J hJ
  by_cases hd : P ∣ J
  · rw [ite_eq_left hd, actual_shared_cube_marked_atom_zero Ψ P I J hI (hF J hJ)
      hPI hd d t X hX hlarge]
  · rw [ite_eq_right hd]

theorem native_shared_cube_exponent_gap (d : ℝ) :
    4*((23:ℝ)/48-d)-((7:ℝ)/6-d) = 3/4-3*d := by ring

theorem native_shared_cube_gap_ge_quarter {d : ℝ} (hd : d ≤ 1/6) :
    1/4 ≤ 4*((23:ℝ)/48-d)-((7:ℝ)/6-d) := by linarith

/-- Explicit annular constants are allowed. This is a geometric threshold,
not a population count or an estimate of the retained unshared column. -/
theorem eventually_native_shared_cube_threshold (d c C : ℝ) (hc : 0 < c)
    (hd : d ≤ 1/6) :
    ∀ᶠ Z : ℝ in atTop,
      2*(C*Z^((7:ℝ)/6-d)) ≤ (c*Z^((23:ℝ)/48-d))^4 := by
  let gap : ℝ := 4*((23:ℝ)/48-d)-((7:ℝ)/6-d)
  have hg : 0 < gap := by
    dsimp [gap]
    linarith [native_shared_cube_gap_ge_quarter hd]
  have ht := tendsto_rpow_atTop (y := gap) hg
  filter_upwards [eventually_gt_atTop (0:ℝ),
    ht.eventually_ge_atTop (2*C/c^4)] with Z hZ hbound
  have hc4 : 0 < c^4 := by positivity
  have hZb : 0 < Z^((7:ℝ)/6-d) := Real.rpow_pos_of_pos hZ _
  have hm : 2*C ≤ c^4*Z^gap := by
    simpa only [mul_comm] using (div_le_iff₀ hc4).mp hbound
  have hid : (c*Z^((23:ℝ)/48-d))^4 =
      (c^4*Z^gap)*Z^((7:ℝ)/6-d) := by
    rw [mul_pow, ←Real.rpow_mul_natCast hZ.le]
    rw [mul_assoc, ←Real.rpow_add hZ]
    congr 2
    dsimp [gap]
    ring
  rw [hid]
  nlinarith [mul_le_mul_of_nonneg_right hm hZb.le]

/-- The native annular scale inequalities give exact deletion of every
positive shared-prime cube incidence, uniformly in the retained finite
column and every complex coefficient/mark/height. No unrelated cube
incidences are deleted. -/
theorem eventually_native_matching_column_unshared (d c C : ℝ) (hc : 0 < c)
    (hd : d ≤ 1/6) :
    ∀ᶠ Z : ℝ in atTop,
      ∀ P I : Id, ∀ F : Finset Id, ∀ Ψ : O →* ℂ, ∀ mark : Id → ℂ,
      ∀ t X : ℝ, I ≠ 0 → P ∣ I → (∀ J ∈ F, J ≠ 0) → 0 < X →
      c*Z^((23:ℝ)/48-d) ≤ (Ideal.absNorm P : ℝ) →
      X ≤ C*Z^((7:ℝ)/6-d) →
      (∑ J ∈ F, summand Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t)
        X I J * mark (I*J^3)) =
      ∑ J ∈ F, if P ∣ J then 0 else
        summand Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t)
          X I J * mark (I*J^3) := by
  filter_upwards [eventually_gt_atTop (0:ℝ),
    eventually_native_shared_cube_threshold d c C hc hd] with Z hZ hthreshold
  intro P I F Ψ mark t X hI hPI hF hX hP hXupper
  have hp0 : 0 ≤ c*Z^((23:ℝ)/48-d) := by positivity
  have hpow : (c*Z^((23:ℝ)/48-d))^4 ≤ (Ideal.absNorm P : ℝ)^4 := by
    gcongr
  have hlarge : 2*X ≤ (Ideal.absNorm P : ℝ)^4 := by
    linarith
  exact finite_matching_column_eq_unshared Ψ P I hI hPI F hF mark t X hX hlarge

end OpenAIReview.MatchingCubeGeometry

#lint+ in OpenAIReview.MatchingCubeGeometry

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
  unless declarations>0 do throwError "Empty native matching cube geometry audit."
  logInfo m!"Matching cube geometry audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-matching-cube-geometry"
  IO.FS.writeFile ".lake/arithmetic-operator-matching-cube-geometry/axioms.json"
    (Json.mkObj [("scope",toJson "exact compact-annulus vanishing of positive shared-prime cube incidences; unshared column unpaid; no whole-row signed bound or actual-zero source limit"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
