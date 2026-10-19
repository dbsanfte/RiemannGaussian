/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# A resultant-supported, bounded-root discrepancy budget

Each residue class contributes less than one unit of prefix discrepancy.
If the common prime powers divide one positive resultant and there are
at most two root classes at each prime power, the whole phase-retaining
centered packet has norm at most twice the logarithm of that resultant.
The bound is uniform in the prefix length and in the resultant.

This is a source-rejection criterion for a common-divisor observation,
not an estimate for the original polynomial prime-divisor sum. Native
polynomial support and root-count hypotheses are supplied separately.
Exterior row weights are kept in an explicit total budget.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option warningAsError true
noncomputable section
open Filter
open scoped BigOperators Classical Topology
namespace OpenAIReview.ResultantDiscrepancy

/-- Exact count in one residue class minus its exact period density. -/
def residueError (T d a : ℕ) : ℝ :=
  (T.count (fun n => Nat.ModEq d n a) : ℝ) - (T : ℝ)/d

/-- The bound is independent of the residue, modulus and prefix length. -/
theorem abs_residueError_le (T a : ℕ) {d : ℕ} (hd : 0 < d) :
    |residueError T d a| ≤ 1 := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have ht : (T : ℝ) = (T % d : ℕ) + (d : ℝ)*(T/d : ℕ) := by
    exact_mod_cast (Nat.mod_add_div T d).symm
  have hfrac0 : 0 ≤ ((T % d : ℕ) : ℝ)/(d : ℝ) := by positivity
  have hfrac1 : ((T % d : ℕ) : ℝ)/(d : ℝ) < 1 :=
    (div_lt_one hdR).mpr (by exact_mod_cast Nat.mod_lt T hd)
  have he : (T : ℝ)/(d : ℝ) = (T/d : ℕ) + ((T % d : ℕ) : ℝ)/(d : ℝ) := by
    apply (div_eq_iff hdR.ne').mpr
    field_simp
    nlinarith
  unfold residueError
  rw [Nat.count_modEq_card T hd a, he]
  split_ifs <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith

/-- All root classes are retained before bounding the centered count. -/
def rootError (T d : ℕ) (A : Finset ℕ) : ℝ :=
  ∑ a ∈ A, residueError T d a

/-- The sum over root residues is exactly the literal prefix count,
with the full period density removed once. -/
theorem rootError_eq_count (T d : ℕ) (A : Finset ℕ)
    (hA : ∀ a ∈ A, a < d) :
    rootError T d A =
      (T.count (fun n => n % d ∈ A) : ℝ) - (A.card : ℝ)*T/d := by
  have hc : T.count (fun n => n % d ∈ A) =
      ∑ a ∈ A, T.count (fun n => Nat.ModEq d n a) := by
    simp_rw [Nat.count_eq_card_filter_range]
    rw [← Finset.sum_card_fiberwise_eq_card_filter (Finset.range T) A (fun n => n % d)]
    apply Finset.sum_congr rfl
    intro a ha
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Nat.ModEq,
      Nat.mod_eq_of_lt (hA a ha)]
  have hcast := congrArg (fun n : ℕ => (n : ℝ)) hc
  simp only [Nat.cast_sum] at hcast
  simp only [rootError, residueError, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul]
  rw [← hcast]
  ring

/-- The whole root discrepancy costs its root count, not its period. -/
theorem abs_rootError_le (T : ℕ) {d : ℕ} (hd : 0 < d) (A : Finset ℕ) :
    |rootError T d A| ≤ A.card := by
  calc
    _ ≤ ∑ a ∈ A, |residueError T d a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ A, (1 : ℝ) :=
      Finset.sum_le_sum fun a _ => abs_residueError_le T a hd
    _ = _ := by simp

/-- Literal Mangoldt prime-power weights and a full denominator phase.
Only resultant-supported denominators occur; no base-prime replacement. -/
def packet (T R : ℕ) (roots : ℕ → Finset ℕ) (phase : ℕ → ℂ) : ℂ :=
  ∑ d ∈ R.divisors, (ArithmeticFunction.vonMangoldt d : ℂ)*phase d*
    (rootError T d (roots d) : ℂ)

/-- Every proper prime power is included, and the whole joined packet
has a logarithmic bound. Root counts at non-prime-powers are irrelevant. -/
theorem norm_packet_le_log (T R : ℕ) (roots : ℕ → Finset ℕ) (phase : ℕ → ℂ)
    (hphase : ∀ d ∈ R.divisors, ‖phase d‖ ≤ 1)
    (hroots : ∀ d ∈ R.divisors, ArithmeticFunction.vonMangoldt d ≠ 0 →
      (roots d).card ≤ 2) :
    ‖packet T R roots phase‖ ≤ 2*Real.log R := by
  have hterm (d : ℕ) (hd : d ∈ R.divisors) :
      ‖(ArithmeticFunction.vonMangoldt d : ℂ)*phase d*
        (rootError T d (roots d) : ℂ)‖ ≤
          2*ArithmeticFunction.vonMangoldt d := by
    by_cases hz : ArithmeticFunction.vonMangoldt d = 0
    · simp [hz]
    have hR : 0 < R := Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hR
    have he : |rootError T d (roots d)| ≤ 2 :=
      (abs_rootError_le T hdpos _).trans (by exact_mod_cast hroots d hd hz)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := d))]
    calc
      _ ≤ ArithmeticFunction.vonMangoldt d*1*2 := by
        gcongr
        exact hphase d hd
      _ = _ := by ring
  calc
    _ ≤ ∑ d ∈ R.divisors, ‖(ArithmeticFunction.vonMangoldt d : ℂ)*phase d*
        (rootError T d (roots d) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ R.divisors, 2*ArithmeticFunction.vonMangoldt d :=
      Finset.sum_le_sum hterm
    _ = _ := by rw [← Finset.mul_sum, ArithmeticFunction.vonMangoldt_sum]

/-- A growing exterior family has its actual mass retained. There is
no inference from a fixed-row bound to an unpaid whole-family bound. -/
theorem norm_weighted_packet_le {ι : Type*} (F : Finset ι) (T R : ι → ℕ)
    (roots : ι → ℕ → Finset ℕ) (phase : ι → ℕ → ℂ) (weight : ι → ℂ)
    (hphase : ∀ i ∈ F, ∀ d ∈ (R i).divisors, ‖phase i d‖ ≤ 1)
    (hroots : ∀ i ∈ F, ∀ d ∈ (R i).divisors,
      ArithmeticFunction.vonMangoldt d ≠ 0 → (roots i d).card ≤ 2) :
    ‖∑ i ∈ F, weight i*packet (T i) (R i) (roots i) (phase i)‖ ≤
      2*∑ i ∈ F, ‖weight i‖*Real.log (R i) := by
  calc
    _ ≤ ∑ i ∈ F, ‖weight i*packet (T i) (R i) (roots i) (phase i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ F, ‖weight i‖*(2*Real.log (R i)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_packet_le_log (T i) (R i) (roots i) (phase i)
          (hphase i hi) (hroots i hi)) (norm_nonneg _)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring

/-- A logarithmic resultant budget has zero response at every positive
power scale. Prefix lengths and root phases may change at every stage. -/
theorem tendsto_packet_of_log_bound (r B : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (T R : ℕ → ℕ) (roots : ℕ → ℕ → Finset ℕ)
    (phase : ℕ → ℕ → ℂ)
    (hphase : ∀ J d, d ∈ (R J).divisors → ‖phase J d‖ ≤ 1)
    (hroots : ∀ J d, d ∈ (R J).divisors →
      ArithmeticFunction.vonMangoldt d ≠ 0 → (roots J d).card ≤ 2)
    (hlog : ∀ J, Real.log (R J) ≤ B*((J : ℝ)+1)) :
    Tendsto (fun J : ℕ => (r : ℂ)^J *
      packet (T J) (R J) (roots J) (phase J)) atTop (nhds 0) := by
  have ht := ((tendsto_pow_const_mul_const_pow_of_lt_one 1 hr0 hr1).add
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1)).const_mul (2*B)
  simp only [pow_one, add_zero, mul_zero] at ht
  apply squeeze_zero_norm (a := fun J : ℕ =>
    (2*B)*((J : ℝ)*r^J+r^J)) _ ht
  intro J
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0]
  have hb := norm_packet_le_log (T J) (R J) (roots J) (phase J)
    (hphase J) (hroots J)
  calc
    _ ≤ r^J*(2*(B*((J : ℝ)+1))) := by
      gcongr
      exact hb.trans (mul_le_mul_of_nonneg_left (hlog J) (by norm_num))
    _ = _ := by ring

end OpenAIReview.ResultantDiscrepancy

#lint+ in OpenAIReview.ResultantDiscrepancy

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
  logInfo m!"Resultant discrepancy: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-resultant-discrepancy"
  IO.FS.writeFile ".lake/arithmetic-operator-resultant-discrepancy/axioms.json"
    (Json.mkObj [("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
