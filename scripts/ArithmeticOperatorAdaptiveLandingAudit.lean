/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorGammaTwistAudit
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Adaptive half-square landing: an exact scalar collapse

The literal incomplete interval `(k²,k(k+1)]` lands at `k(k+1)`.
Prime-power support is essential: general composite divisors may split
between the two coprime factors. No signed estimate or analytic source
transfer is asserted. Positive lags delete the landing endpoint exactly.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical
namespace RiemannGaussian.ArithmeticOperatorAdaptiveLandingAudit

/-- Number of denominator incidences in the actual incomplete block. -/
def landingCount (k d : ℕ) : ℕ :=
  ((Finset.Ioc (k^2) (k*(k+1))).filter (fun n => d ∣ n)).card

/-- The literal incomplete count is its exact floor difference. -/
theorem landingCount_eq (k d : ℕ) :
    landingCount k d = k*(k+1)/d-k^2/d := by
  have he : (Finset.Ioc (k^2) (k*(k+1))).filter (fun n => d ∣ n) =
      ((Finset.Ioc 0 (k*(k+1))).filter (fun n => d ∣ n)) \
        ((Finset.Ioc 0 (k^2)).filter (fun n => d ∣ n)) := by
    ext n
    simp only [Finset.mem_filter,Finset.mem_Ioc,Finset.mem_sdiff]
    have hh : k^2 ≤ k*(k+1) := by nlinarith
    omega
  have hsub : ((Finset.Ioc 0 (k^2)).filter (fun n => d ∣ n)) ⊆
      ((Finset.Ioc 0 (k*(k+1))).filter (fun n => d ∣ n)) := by
    intro n hn
    simp only [Finset.mem_filter,Finset.mem_Ioc] at hn ⊢
    exact ⟨⟨hn.1.1,hn.1.2.trans (by nlinarith)⟩,hn.2⟩
  rw [landingCount,he,Finset.card_sdiff,Finset.inter_eq_left.mpr hsub]
  simp only [Nat.Ioc_filter_dvd_card_eq_div]

/-- A prime power cannot split between adjacent coprime factors. -/
theorem primePower_lands {k d : ℕ} (hd : IsPrimePow d) :
    d ∣ k*(k+1) ↔ d ∣ k ∨ d ∣ k+1 :=
  ((Nat.coprime_self_add_right.mpr (Nat.coprime_one_right k))).isPrimePow_dvd_mul hd

/-- An exact incomplete-block count, with no CRT boundary payment. -/
theorem landingCount_of_dvd_left {k d : ℕ} (hd : d ∣ k) :
    landingCount k d = k/d := by
  rw [landingCount_eq]
  have he : k*(k+1)=k^2+k := by ring
  rw [he,Nat.add_div_of_dvd_left hd,Nat.add_sub_cancel_left]

/-- The other adjacent factor contributes the next quotient, not a density. -/
theorem landingCount_of_dvd_right {k d : ℕ} (hk : 0<k) (hd1 : 1<d)
    (hd : d ∣ k+1) : landingCount k d = (k+1)/d := by
  have hd0 : 0<d := by omega
  have ha : d ∣ (k-1)*(k+1) := dvd_mul_of_dvd_right hd (k-1)
  have he : (k-1)*(k+1)+1=k^2 := by
    have hk' : k-1+1=k := by omega
    nlinarith
  have hm : k*(k+1)=(k-1)*(k+1)+(k+1) := by
    have hk' : k-1+1=k := by omega
    nlinarith
  have hsq : k^2/d=((k-1)*(k+1))/d := by
    rw [←he,Nat.add_div_of_dvd_right ha,Nat.div_eq_of_lt hd1]
    omega
  rw [landingCount_eq,hsq,hm,Nat.add_div_of_dvd_left hd]
  exact Nat.add_sub_cancel_left _ _

/-- Every divisor of the landing point contributes the endpoint once. -/
def positiveLandingCount (k d : ℕ) : ℕ :=
  landingCount k d-if d ∣ k*(k+1) then 1 else 0

/-- Removing zero lag means removing precisely the actual landing point. -/
theorem positiveLandingCount_eq (k d : ℕ) (hk : 0<k) :
    positiveLandingCount k d =
      ((Finset.Ioo (k^2) (k*(k+1))).filter (fun n => d ∣ n)).card := by
  rw [←Finset.Ioc_erase_right,Finset.filter_erase]
  by_cases hd : d ∣ k*(k+1)
  · have hm : k*(k+1) ∈ (Finset.Ioc (k^2) (k*(k+1))).filter (fun n => d ∣ n) := by
      simp only [Finset.mem_filter,Finset.mem_Ioc]
      exact ⟨⟨by nlinarith,le_rfl⟩,hd⟩
    rw [Finset.card_erase_of_mem hm]
    simp only [positiveLandingCount,hd,ite_true,landingCount]
  · have hm : k*(k+1) ∉ (Finset.Ioc (k^2) (k*(k+1))).filter (fun n => d ∣ n) := by
      simp only [Finset.mem_filter,Finset.mem_Ioc]
      tauto
    rw [Finset.erase_eq_of_notMem hm]
    simp only [positiveLandingCount,hd,ite_false,Nat.sub_zero,landingCount]

/-- The signed finite packet retains arbitrary phases on all prime powers. -/
def landingPacket (S : Finset ℕ) (w : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ d∈S, if d ∣ k*(k+1) then w d*(landingCount k d : ℂ) else 0

/-- One scalar divisor convolution leg with the same literal denominators. -/
def convolutionLeg (S : Finset ℕ) (w : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ d∈S, if d ∣ k then w d*((k/d : ℕ) : ℂ) else 0

/-- The adaptive additive/divisibility join collapses before any norm.
The hypothesis permits all actual prime powers, not only primes. -/
theorem landingPacket_eq (S : Finset ℕ) (w : ℕ → ℂ)
    (hw : ∀ d∈S, ¬IsPrimePow d → w d=0) {k : ℕ} (hk : 0<k) :
    landingPacket S w k = convolutionLeg S w k+convolutionLeg S w (k+1) := by
  unfold landingPacket convolutionLeg
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hp : IsPrimePow d
  · have hn : ¬(d ∣ k ∧ d ∣ k+1) := by
      intro hh
      have ho : d ∣ 1 := by
        exact (Nat.dvd_add_iff_right hh.1).mpr hh.2
      have := Nat.le_of_dvd (by decide : 0<1) ho
      exact (not_le_of_gt hp.one_lt) this
    by_cases hl : d ∣ k
    · have hr : ¬d ∣ k+1 := fun h => hn ⟨hl,h⟩
      simp only [hl,hr,(primePower_lands hp).mpr (Or.inl hl),ite_true,ite_false,
        landingCount_of_dvd_left hl,add_zero]
    · by_cases hr : d ∣ k+1
      · simp only [hl,hr,(primePower_lands hp).mpr (Or.inr hr),ite_true,ite_false,
          landingCount_of_dvd_right hk hp.one_lt hr,zero_add]
      · have hno : ¬d ∣ k*(k+1) := by simpa only [primePower_lands hp,hl,hr,or_self] using
          (show ¬False from not_false)
        simp only [hl,hr,hno,ite_false,add_zero]
  · simp only [hw d hd hp,zero_mul,ite_self,add_zero]

/-- Actual Mangoldt coefficients satisfy the required support, with no
restriction on their literal prime-power phase. -/
theorem mangoldt_phase_support (phase : ℕ → ℂ) (d : ℕ) (hd : ¬IsPrimePow d) :
    (ArithmeticFunction.vonMangoldt d : ℂ)*phase d=0 := by
  rw [(ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hd)]
  simp

/-- Composite splitting is a real obstruction to dropping the support gate. -/
theorem composite_counterexample : landingCount 2 6=1 ∧ ¬6 ∣ 2 ∧ ¬6 ∣ 2+1 := by
  decide

end RiemannGaussian.ArithmeticOperatorAdaptiveLandingAudit

#lint+ in RiemannGaussian.ArithmeticOperatorAdaptiveLandingAudit

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
  logInfo m!"Adaptive landing: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.writeFile ".lake/arithmetic-operator-next-interaction-gate/axioms.json"
    (Json.mkObj [("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
