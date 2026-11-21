import Mathlib
import Formalism.StatementOC

/-! The declarations used at the principal cyclic level, taken from the pinned
Alpöge sources PrimePairSizeCondition, Analytic, ExplicitFormulaErrorOfHostConditions,
and Window. The full modules can be used in the author's project at the same import path. -/

noncomputable section
namespace Formalism.HC

structure PChar where
  N : ℕ
  [ne : NeZero N]
  χ : DirichletCharacter ℂ N
  prim : χ.IsPrimitive

attribute [instance] PChar.ne

namespace PChar

def val (ψ : PChar) (a : ℕ) : ℂ := ψ.χ (a : ZMod ψ.N)

def one : PChar := ⟨1, 1, DirichletCharacter.isPrimitive_one_level_one⟩

def inv (ψ : PChar) : PChar :=
  ⟨ψ.N, ψ.χ⁻¹, by
    have h : ψ.χ.conductor = ψ.N := ψ.prim
    exact (DirichletCharacter.conductor_inv ψ.χ).trans h⟩

theorem inv_inv (ψ : PChar) : ψ.inv.inv = ψ := by
  cases ψ
  simp only [inv]
  congr 1
  exact _root_.inv_inv _

def of {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : PChar :=
  @PChar.mk χ.conductor ⟨χ.conductor_ne_zero⟩ χ.primitiveCharacter χ.primitiveCharacter_isPrimitive

def IsReal (ψ : PChar) : Prop := ∀ a : ZMod ψ.N, (ψ.χ a).im = 0

end PChar

structure KSet where
  KEPT : Finset PChar
  one_mem : PChar.one ∈ KEPT
  inv_mem : ∀ ψ ∈ KEPT, ψ.inv ∈ KEPT

  psK : Option PChar
  psK_spec : ∀ ψ, psK = some ψ → ψ ∈ KEPT ∧ ψ.χ.Odd ∧ ψ.IsReal

namespace An

abbrev abelian₂ (n : ℕ) : ℝ := (ArithmeticFunction.vonMangoldt n : ℝ)

def logDerivativeAtOne {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℂ :=
  deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1

def G (y : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, abelian₂ n * max (y / n - 1) 0) -
    y * (Real.log y - 1 - Real.eulerMascheroniConstant)

def sumLamChi {N : ℕ} (χ : DirichletCharacter ℂ N) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (abelian₂ n : ℂ) * χ (n : ZMod N) * ((max (y / n - 1) 0 : ℝ) : ℂ)

open Classical in

def gChi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) : ℂ :=
  if χ = 1 then ((G y : ℝ) : ℂ) else sumLamChi χ y + (y : ℂ) * logDerivativeAtOne χ

end An

structure Level extends KSet where
  o : ℕ

namespace Level

variable (Λ : Level)

open Classical in

def Nt : Finset PChar := Λ.KEPT.erase PChar.one

open Classical in

def wt (ψ : PChar) : ℝ := if Λ.psK = some ψ then 1 else (3 * (Λ.o : ℝ) + 1)⁻¹

def Gm (y : ℝ) : ℝ := Formalism.Gz y + ∑ ψ ∈ Λ.Nt, Λ.wt ψ * (An.gChi ψ.χ y).re

end Level

private theorem pchar_mk_eq_one_of_level_eq_one {d : ℕ} [NeZero d] (ψ : DirichletCharacter ℂ d) (h : ψ.IsPrimitive)
    (he : d = 1) : PChar.mk d ψ h = PChar.one := by
  subst he
  obtain rfl := DirichletCharacter.level_one ψ
  rfl

theorem PChar.of_one (M : ℕ) [NeZero M] : PChar.of (1 : DirichletCharacter ℂ M) = PChar.one := by
  haveI : NeZero (1 : DirichletCharacter ℂ M).conductor :=
    ⟨(1 : DirichletCharacter ℂ M).conductor_ne_zero⟩
  exact pchar_mk_eq_one_of_level_eq_one _ _ DirichletCharacter.conductor_one

private theorem pchar_mk_eq_of_changeLevel_eq_of_level_eq {M d e : ℕ} [NeZero M] [NeZero d] [NeZero e]
    (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ d) (φ : DirichletCharacter ℂ e)
    (hd : d ∣ M) (he' : e ∣ M) (hde : d = e) (hψ : DirichletCharacter.changeLevel hd ψ = χ)
    (hφ : DirichletCharacter.changeLevel he' φ = χ) (p1 : ψ.IsPrimitive) (p2 : φ.IsPrimitive) :
    PChar.mk d ψ p1 = PChar.mk e φ p2 := by
  subst hde
  have hq : ψ = φ := DirichletCharacter.changeLevel_injective hd (hψ.trans hφ.symm)
  subst hq
  rfl

private theorem conductor_inv_dvd_conductor {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) :
    χ⁻¹.conductor ∣ χ.conductor := by
  apply DirichletCharacter.conductor_dvd_of_mem_conductorSet
  exact ⟨χ.conductor_dvd_level, χ.primitiveCharacter⁻¹,
    by rw [map_inv, DirichletCharacter.changeLevel_primitiveCharacter]⟩

private theorem conductor_inv_eq_conductor {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) :
    χ⁻¹.conductor = χ.conductor := by
  apply Nat.dvd_antisymm (conductor_inv_dvd_conductor χ)
  simpa using conductor_inv_dvd_conductor χ⁻¹

theorem PChar.of_inv {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) : PChar.of χ⁻¹ = (PChar.of χ).inv := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  haveI : NeZero χ⁻¹.conductor := ⟨χ⁻¹.conductor_ne_zero⟩
  exact pchar_mk_eq_of_changeLevel_eq_of_level_eq χ⁻¹ χ⁻¹.primitiveCharacter χ.primitiveCharacter⁻¹ χ⁻¹.conductor_dvd_level
    χ.conductor_dvd_level (conductor_inv_eq_conductor χ) χ⁻¹.changeLevel_primitiveCharacter
    (by rw [map_inv, DirichletCharacter.changeLevel_primitiveCharacter]) _ _

open Classical in

def Level.ofSub {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) : Level where
  KEPT := (Finset.univ.filter fun χ : DirichletCharacter ℂ M => χ ∈ Ξ).image PChar.of
  one_mem := Finset.mem_image.2 ⟨1, Finset.mem_filter.2 ⟨Finset.mem_univ _, Ξ.one_mem⟩, PChar.of_one M⟩
  inv_mem := by
    intro ψ h
    obtain ⟨χ, h1, rfl⟩ := Finset.mem_image.1 h
    exact Finset.mem_image.2 ⟨χ⁻¹, Finset.mem_filter.2 ⟨Finset.mem_univ _, Ξ.inv_mem (Finset.mem_filter.1 h1).2⟩, PChar.of_inv χ⟩
  psK := none
  psK_spec := fun _ h => by cases h
  o := Nat.card Ξ

theorem Level.mem_ofSub {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (ψ : PChar) :
    ψ ∈ (Level.ofSub Ξ).KEPT ↔ ∃ χ ∈ Ξ, PChar.of χ = ψ := by
  classical
  simp [Level.ofSub]

def Level.cyc (ψ : PChar) : Level := Level.ofSub (Subgroup.zpowers ψ.χ)

def HasWindows (S : Set ℝ) (la : ℝ) : Prop :=
  ∀ y : ℝ, ∃ Y : ℝ, y ≤ Y ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ la → x ∈ S

end Formalism.HC
end
