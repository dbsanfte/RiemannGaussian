/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.QuasiRHCoupledResidueAudit
import OAI.NumberTheory.DirichletL.Descent.Completion
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Finite cube inverse and its surviving matching prime column

The squarefree `I` coefficient is the actual Gauss coefficient, not Möbius.
Möbius belongs to the outer `H` cube inverse.  This leaf joins all finite
local `J` powers before estimating: the correctly shifted `H=P` row cancels
every positive `J` power but retains the `J=1` ordinary-prime column.
Every literal total-index weight and full complex phase is retained.
Equal unshifted truncations have an explicit last boundary; no estimate
for that boundary, a Gaussian cutoff, or a hypothetical-zero source is
inferred from the finite identity.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2048
noncomputable section
open scoped BigOperators Classical

namespace OpenAIReview.InverseMatching
open OAI OpenAIReview.CoupledResidue
open OAI.CanonicalRowCompletion OAI.ConcretePrimeRowBridge OAI.CubicEisenstein
open OAI.CompletedGauss OAI.SevenEighths.ProbePhysical OAI.GaussianShiftedPartition

local notation "O" => OAI.ActualEisensteinCubic.O

/-- The exact local completed ideal index, including the unit endpoint. -/
def completedIndex (P : Ideal O) (i j : ℕ) : Ideal O := P^i * (P^j)^3

/-- The local completed index has valuation `i+3j`. -/
theorem completedIndex_eq (P : Ideal O) (i j : ℕ) :
    completedIndex P i j = P^(i+3*j) := by
  simp only [completedIndex, ← pow_mul, ← pow_add, Nat.mul_comm j 3]

/-- The actual completed local row joined to the actual additive Gauss row. -/
def completedAtom (p : O) (hp : p ≠ 0) (i j : ℕ) (m : O) : ℂ :=
  idealRowHom m (completedIndex (Ideal.span {p}) i j) * sexticGauss p hp (-m)

/-- At cube order zero the squarefree prime column is unchanged. -/
theorem completedAtom_prime_zero (p : O) (hp : p ≠ 0) (m : O) :
    completedAtom p hp 1 0 m = idealRowHom m (Ideal.span {p}) * sexticGauss p hp (-m) := by
  simp only [completedAtom, completedIndex, pow_one, pow_zero, one_pow, mul_one]

/-- A nonprincipal character makes the additive atom at the zero residue exactly zero. -/
theorem additiveRow_zero {F : Type*} [Field F] [Fintype F]
    (chi : MulChar F ℂ) (psi : AddChar F ℂ) (hchi : chi ≠ 1) :
    additiveRow chi psi 0 = 0 := by
  simp only [additiveRow, gaussSum, AddChar.mulShift_apply, neg_zero, zero_mul,
    AddChar.map_zero_eq_one, mul_one]
  exact chi.sum_eq_zero_of_ne_one hchi

/-- Character power and scalar power agree after joining the zero additive atom,
even for exponent zero. -/
theorem power_join {F : Type*} [Field F] [Fintype F]
    (chi : MulChar F ℂ) (psi : AddChar F ℂ) (hchi : chi ≠ 1) (e : ℕ) (x : F) :
    (chi x)^e * additiveRow chi psi x = (chi^e) x * additiveRow chi psi x := by
  by_cases he : e = 0
  · subst e
    by_cases hx : x = 0
    · subst x
      rw [additiveRow_zero chi psi hchi]
      simp
    · have hu : IsUnit x := isUnit_iff_ne_zero.mpr hx
      simp only [pow_zero, one_mul, MulChar.one_apply hu]
  · rw [MulChar.pow_apply' chi he]

/-- Actual ideal multiplication and cube powers retain their native residue row. -/
theorem completedAtom_residue (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    [Fintype (O ⧸ Ideal.span {p})]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (i j : ℕ) (m : O) :
    completedAtom p hp i j m =
      (actualSextic (Ideal.span {p}) hg ^ (i+3*j)) (Ideal.Quotient.mk _ m) *
        additiveRow (actualSextic (Ideal.span {p}) hg) (quotientTrace p hp)
          (Ideal.Quotient.mk _ m) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  rw [completedAtom, completedIndex_eq, map_pow, idealRowHom_prime _ _ hg,
    actual_gauss p hp hg m]
  exact power_join _ _ (actual_character_nonprincipal p hg hc) _ _

/-- Full actual residue period for the squarefree/cube index, retaining every
nonunit and the unit-index endpoint. -/
theorem completed_period (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    [Fintype (O ⧸ Ideal.span {p})]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (i j : ℕ) (hi : i ≤ 1) :
    (∑ x : O ⧸ Ideal.span {p}, completedAtom p hp i j (representative p x)) =
      if i=1 ∧ j%2=0 then
        ((Fintype.card (O ⧸ Ideal.span {p}) : ℂ)-1) *
          actualSextic (Ideal.span {p}) hg (-1) *
            gaussSum (actualSextic (Ideal.span {p}) hg) (quotientTrace p hp)
      else 0 := by
  simp_rw [completedAtom_residue p hp hg hc i j, representative_spec]
  rw [actual_valuation_period p hp hg hc]
  simp only [completed_valuation_gate hi]

/-- The finite `J` polynomial keeps exactly its even subsequence when `I=P`.
All complex coefficients can encode native cutoff and exterior phases. -/
theorem completed_polynomial (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    [Fintype (O ⧸ Ideal.span {p})]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (i : ℕ) (hi : i ≤ 1) (J : Finset ℕ) (w : ℕ → ℂ) :
    (∑ j ∈ J, w j * ∑ x : O ⧸ Ideal.span {p},
      completedAtom p hp i j (representative p x)) =
      if i=1 then
        (((Fintype.card (O ⧸ Ideal.span {p}) : ℂ)-1) *
          actualSextic (Ideal.span {p}) hg (-1) *
            gaussSum (actualSextic (Ideal.span {p}) hg) (quotientTrace p hp)) *
              ∑ j ∈ J.filter (fun j => j%2=0), w j
      else 0 := by
  simp_rw [completed_period p hp hg hc i _ hi]
  by_cases hi1 : i=1
  · subst i
    rw [ite_eq_left rfl, Finset.mul_sum]
    simp only [true_and, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j%2=0 <;> simp [hj, mul_comm]
  · simp [hi1]

/-- Exact finite cube telescoping uses the SAME total-index weight on each
shifted copy, without bounding any coefficient. -/
theorem finite_cube_telescoping (c : ℂ) (w f : ℕ → ℂ) (K : ℕ) :
    (∑ j ∈ Finset.range (K+1), c^j * w j * f j) -
      c * ∑ j ∈ Finset.range K, c^j * w (j+1) * f (j+1) = w 0 * f 0 := by
  have hs : c * ∑ j ∈ Finset.range K, c^j * w (j+1) * f (j+1) =
      ∑ j ∈ Finset.range K, c^(j+1) * w (j+1) * f (j+1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_succ]
    ring
  rw [hs, Finset.sum_range_succ']
  simp only [pow_zero, one_mul]
  ring

/-- Equal unshifted lengths leave an exact last boundary, which is not paid. -/
theorem finite_cube_equal_cutoff (c : ℂ) (w f : ℕ → ℂ) (K : ℕ) :
    (∑ j ∈ Finset.range (K+1), c^j * w j * f j) -
      c * ∑ j ∈ Finset.range (K+1), c^j * w (j+1) * f (j+1) =
        w 0 * f 0 - c^(K+1) * w (K+1) * f (K+1) := by
  rw [Finset.sum_range_succ (fun j => c^j * w (j+1) * f (j+1)) K,
    mul_add]
  have ht := finite_cube_telescoping c w f K
  rw [← sub_sub]
  rw [ht, pow_succ]
  ring

/-- Möbius is exactly minus one on the OUTER prime ideal, not on the `I` column. -/
theorem outer_prime_mobius (P : Ideal O) (hP : Prime P) :
    (UniqueFactorizationMonoid.moebius P : ℂ) = -1 := by
  rw [hP.irreducible.moebius_eq]
  norm_num

/-- The outer `H=P` Möbius coefficient has the same negative sign at every
residual `J=P^j`; it does not alternate in `j`. -/
theorem outer_prime_shift (Psi : O →* ℂ) (P : Ideal O) (hP : Prime P) (j : ℕ) :
    (UniqueFactorizationMonoid.moebius P : ℂ) * cubeWeight Psi P *
      cubeWeight Psi (P^j) = -(cubeWeight Psi P)^(j+1) := by
  rw [outer_prime_mobius P hP, map_pow, pow_succ]
  ring

/-- The finite local outer Möbius inverse retains the prime column exactly,
for every literal total-index weight and every native numerator. -/
def inverseAtom (Psi : O →* ℂ) (p : O) (hp : p ≠ 0)
    (K : ℕ) (w : ℕ → O → ℂ) (m : O) : ℂ :=
  (∑ j ∈ Finset.range (K+1), (cubeWeight Psi (Ideal.span {p}))^j *
    w j m * completedAtom p hp 1 j m) +
  (UniqueFactorizationMonoid.moebius (Ideal.span {p}) : ℂ) *
    cubeWeight Psi (Ideal.span {p}) *
      ∑ j ∈ Finset.range K, (cubeWeight Psi (Ideal.span {p}))^j *
        w (j+1) m * completedAtom p hp 1 (j+1) m

/-- Every positive cube power cancels, but the ordinary-prime atom survives. -/
theorem inverseAtom_eq (Psi : O →* ℂ) (p : O) (hp : p ≠ 0)
    (hP : Prime (Ideal.span {p} : Ideal O))
    (K : ℕ) (w : ℕ → O → ℂ) (m : O) :
    inverseAtom Psi p hp K w m =
      w 0 m * idealRowHom m (Ideal.span {p}) * sexticGauss p hp (-m) := by
  rw [inverseAtom, outer_prime_mobius _ hP]
  simp only [neg_mul, one_mul, ← sub_eq_add_neg]
  rw [finite_cube_telescoping, completedAtom_prime_zero]
  ring

/-- Exact masked finite join after cube inversion: the remaining weight is
one signed sum over actual nonunits removed, with its actual Gauss phase. -/
theorem inverse_masked_matching (Psi : O →* ℂ) (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    [Fintype (O ⧸ Ideal.span {p})]
    (hg : goodLambda ∉ Ideal.span {p}) (hP : Prime (Ideal.span {p} : Ideal O))
    (K : ℕ) (w : ℕ → O → ℂ) (B : Finset O) :
    (∑ m ∈ B, inverseAtom Psi p hp K w m) =
      (actualSextic (Ideal.span {p}) hg (-1) *
        gaussSum (actualSextic (Ideal.span {p}) hg) (quotientTrace p hp)) *
          ∑ m ∈ B.filter (fun m => m ∉ Ideal.span {p}), w 0 m := by
  simp_rw [inverseAtom_eq Psi p hp hP K w]
  simpa only [Nat.mul_zero, pow_zero, one_pow, mul_one] using
    actual_masked_matching p hp hg 0 B (w 0)

/-- The actual normalized full inverse period, with all completed powers joined. -/
def normalizedInversePeriod (Psi : O →* ℂ) (p : O) (hp : p ≠ 0)
    [Fintype (O ⧸ Ideal.span {p})] (K : ℕ) (w : ℕ → O → ℂ) : ℂ :=
  (Fintype.card (O ⧸ Ideal.span {p}) : ℂ)⁻¹ *
    (Real.sqrt (Fintype.card (O ⧸ Ideal.span {p})) : ℂ)⁻¹ *
      ∑ x : O ⧸ Ideal.span {p}, inverseAtom Psi p hp K w (representative p x)

/-- Total-index weights equal to one at the prime endpoint retain exactly the
actual normalized matching Gauss channel after every cube cancellation. -/
theorem normalizedInversePeriod_eq (Psi : O →* ℂ) (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    [Fintype (O ⧸ Ideal.span {p})]
    (hg : goodLambda ∉ Ideal.span {p}) (hP : Prime (Ideal.span {p} : Ideal O))
    (K : ℕ) (w : ℕ → O → ℂ) (hw : ∀ m, w 0 m = 1) :
    normalizedInversePeriod Psi p hp K w =
      normalizedMean (actualSextic (Ideal.span {p}) hg) (quotientTrace p hp) := by
  unfold normalizedInversePeriod normalizedMean
  congr 2
  funext x
  rw [inverseAtom_eq Psi p hp hP K w, hw, one_mul,
    idealRowHom_prime _ _ hg, actual_gauss p hp hg, representative_spec]

/-- The joined Möbius-inverse period is not small: its norm is the same exact
local matching mass, independently of the cube power or its complex weight. -/
theorem norm_normalizedInversePeriod (Psi : O →* ℂ) (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    [Fintype (O ⧸ Ideal.span {p})]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hP : Prime (Ideal.span {p} : Ideal O))
    (K : ℕ) (w : ℕ → O → ℂ) (hw : ∀ m, w 0 m = 1) :
    ‖normalizedInversePeriod Psi p hp K w‖ =
      1-(Fintype.card (O ⧸ Ideal.span {p}) : ℝ)⁻¹ := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  rw [normalizedInversePeriod_eq Psi p hp hg hP K w hw]
  exact norm_normalizedMean _ _ (actual_character_nonprincipal p hg hc)
    (OAI.GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp)

/-- Squarefree `I`, all cube powers and actual outer Möbius cancellation alone
cannot imply mean zero: the surviving normalized prime channel is at least half. -/
theorem normalizedInversePeriod_lower (Psi : O →* ℂ) (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    [Fintype (O ⧸ Ideal.span {p})]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hP : Prime (Ideal.span {p} : Ideal O))
    (K : ℕ) (w : ℕ → O → ℂ) (hw : ∀ m, w 0 m = 1) :
    (1/2 : ℝ) ≤ ‖normalizedInversePeriod Psi p hp K w‖ := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  rw [normalizedInversePeriod_eq Psi p hp hg hP K w hw]
  exact normalizedMean_lower _ _ (actual_character_nonprincipal p hg hc)
    (OAI.GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp)

/-- The finite signed matching identity also permits the actual numerator-dependent
base row, with no fixed-character or fixed-cube-coefficient assumption. -/
theorem inverse_row_masked_matching (Psi : O → (O →* ℂ)) (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    [Fintype (O ⧸ Ideal.span {p})]
    (hg : goodLambda ∉ Ideal.span {p}) (hP : Prime (Ideal.span {p} : Ideal O))
    (K : ℕ) (w : ℕ → O → ℂ) (B : Finset O) :
    (∑ m ∈ B, inverseAtom (Psi m) p hp K w m) =
      (actualSextic (Ideal.span {p}) hg (-1) *
        gaussSum (actualSextic (Ideal.span {p}) hg) (quotientTrace p hp)) *
          ∑ m ∈ B.filter (fun m => m ∉ Ideal.span {p}), w 0 m := by
  calc
    _ = ∑ m ∈ B, w 0 m * idealRowHom m (Ideal.span {p}) * sexticGauss p hp (-m) := by
      apply Finset.sum_congr rfl
      intro m _
      exact inverseAtom_eq (Psi m) p hp hP K w m
    _ = _ := by
      simpa only [Nat.mul_zero, pow_zero, one_pow, mul_one] using
        actual_masked_matching p hp hg 0 B (w 0)

/-- The normalized complete period with the actual base row allowed to vary
with each numerator; every local cube coefficient varies along with it. -/
def normalizedRowInversePeriod (Psi : O → (O →* ℂ)) (p : O) (hp : p ≠ 0)
    [Fintype (O ⧸ Ideal.span {p})] (K : ℕ) (w : ℕ → O → ℂ) : ℂ :=
  (Fintype.card (O ⧸ Ideal.span {p}) : ℂ)⁻¹ *
    (Real.sqrt (Fintype.card (O ⧸ Ideal.span {p})) : ℂ)⁻¹ *
      ∑ x : O ⧸ Ideal.span {p},
        inverseAtom (Psi (representative p x)) p hp K w (representative p x)

/-- Pointwise cube inversion removes the dependence of the surviving complete
matching period on the numerator-dependent base row. -/
theorem normalizedRowInversePeriod_eq (Psi : O → (O →* ℂ)) (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    [Fintype (O ⧸ Ideal.span {p})]
    (hg : goodLambda ∉ Ideal.span {p}) (hP : Prime (Ideal.span {p} : Ideal O))
    (K : ℕ) (w : ℕ → O → ℂ) (hw : ∀ m, w 0 m = 1) :
    normalizedRowInversePeriod Psi p hp K w =
      normalizedMean (actualSextic (Ideal.span {p}) hg) (quotientTrace p hp) := by
  unfold normalizedRowInversePeriod normalizedMean
  congr 2
  funext x
  rw [inverseAtom_eq (Psi (representative p x)) p hp hP K w, hw, one_mul,
    idealRowHom_prime _ _ hg, actual_gauss p hp hg, representative_spec]

/-- Exact retained matching mass for numerator-dependent rows and cube phases. -/
theorem norm_normalizedRowInversePeriod (Psi : O → (O →* ℂ)) (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    [Fintype (O ⧸ Ideal.span {p})]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hP : Prime (Ideal.span {p} : Ideal O))
    (K : ℕ) (w : ℕ → O → ℂ) (hw : ∀ m, w 0 m = 1) :
    ‖normalizedRowInversePeriod Psi p hp K w‖ =
      1-(Fintype.card (O ⧸ Ideal.span {p}) : ℝ)⁻¹ := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  rw [normalizedRowInversePeriod_eq Psi p hp hg hP K w hw]
  exact norm_normalizedMean _ _ (actual_character_nonprincipal p hg hc)
    (OAI.GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp)

/-- Allowing the genuine base row to depend on the numerator does not make
the locally surviving matching prime channel mean zero. -/
theorem normalizedRowInversePeriod_lower (Psi : O → (O →* ℂ)) (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    [Fintype (O ⧸ Ideal.span {p})]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hP : Prime (Ideal.span {p} : Ideal O))
    (K : ℕ) (w : ℕ → O → ℂ) (hw : ∀ m, w 0 m = 1) :
    (1/2 : ℝ) ≤ ‖normalizedRowInversePeriod Psi p hp K w‖ := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  rw [normalizedRowInversePeriod_eq Psi p hp hg hP K w hw]
  exact normalizedMean_lower _ _ (actual_character_nonprincipal p hg hc)
    (OAI.GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp)

end OpenAIReview.InverseMatching

#lint+ in OpenAIReview.InverseMatching

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
  unless declarations > 0 do throwError "Empty inverse matching audit."
  logInfo m!"Inverse matching audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-inverse-matching"
  IO.FS.writeFile ".lake/arithmetic-operator-inverse-matching/axioms.json"
    (Json.mkObj [("scope",toJson "finite actual cube inverse; surviving prime matching; no native global source bound"),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
