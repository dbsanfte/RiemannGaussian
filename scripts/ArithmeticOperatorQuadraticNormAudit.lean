/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorGammaTwistAudit
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Adjacent quadratic norm values have a source-blind common-divisor packet

Only the adjacent gcd statistic is evaluated here. The polynomial prime-only
packet, literal determinant carry-layer transfer, and general root-position
error are not bounded. Every prime-power phase in the gcd statistic is retained.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical Topology
namespace RiemannGaussian.ArithmeticOperatorQuadraticNormAudit
open ArithmeticOperatorGammaTwistAudit SuzukiCarryCorrelation

/-- The irreducible quadratic factor in the gap-three Pascal minor. -/
def quadratic (t : ℕ) : ℕ := 3*t^2+3*t+2

/-- A fixed Bezout relation across adjacent actual polynomial values. -/
theorem adjacent_relation (t : ℕ) :
    (t+2)*quadratic t = t*quadratic (t+1)+4 := by
  unfold quadratic
  ring

/-- All common divisors of adjacent polynomial values divide four. -/
theorem adjacent_common_divisor {t d : ℕ}
    (ha : d ∣ quadratic t) (hb : d ∣ quadratic (t+1)) : d ∣ 4 := by
  have hleft : d ∣ (t+2)*quadratic t := dvd_mul_of_dvd_right ha (t+2)
  have hright : d ∣ t*quadratic (t+1) := dvd_mul_of_dvd_right hb t
  rw [adjacent_relation] at hleft
  exact (Nat.dvd_add_iff_right hright).mpr hleft

/-- No odd prime can divide both adjacent polynomial values. -/
theorem no_common_odd_prime {t p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : p ∣ quadratic t) : ¬p ∣ quadratic (t+1) := by
  intro hb
  have hd := adjacent_common_divisor ha hb
  have : p ∣ 2 := (hp.dvd_mul.mp (show p ∣ 2*2 from hd)).elim id id
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)

/-- Every polynomial value is even. -/
theorem two_dvd_quadratic (t : ℕ) : 2 ∣ quadratic t := by
  apply Nat.dvd_of_mod_eq_zero
  have hr : t%2<2 := Nat.mod_lt t (by decide)
  interval_cases ht : t%2 <;>
    norm_num [quadratic,Nat.add_mod,Nat.mul_mod,Nat.pow_mod,ht]

/-- The four-divisibility condition retains its literal residue location. -/
theorem four_dvd_quadratic_iff (t : ℕ) :
    4 ∣ quadratic t ↔ t%4=1 ∨ t%4=2 := by
  rw [Nat.dvd_iff_mod_eq_zero]
  have hr : t%4<4 := Nat.mod_lt t (by decide)
  interval_cases ht : t%4 <;>
    norm_num [quadratic,Nat.add_mod,Nat.mul_mod,Nat.pow_mod,ht]

/-- The common factor four occurs in exactly one residue class modulo four. -/
theorem four_dvd_gcd_iff (t : ℕ) :
    4 ∣ Nat.gcd (quadratic t) (quadratic (t+1)) ↔ t%4=1 := by
  rw [Nat.dvd_gcd_iff,four_dvd_quadratic_iff,four_dvd_quadratic_iff]
  omega

/-- The actual gcd is two or four, with no forgotten odd factor. -/
theorem adjacent_gcd (t : ℕ) :
    Nat.gcd (quadratic t) (quadratic (t+1)) = if t%4=1 then 4 else 2 := by
  let g := Nat.gcd (quadratic t) (quadratic (t+1))
  have h4 : g ∣ 4 := adjacent_common_divisor (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
  have h2 : 2 ∣ g := Nat.dvd_gcd (two_dvd_quadratic t) (two_dvd_quadratic (t+1))
  have hmem : g ∈ (4:ℕ).divisors := Nat.mem_divisors.mpr ⟨h4,by decide⟩
  have hdiv : (4:ℕ).divisors={1,2,4} := by decide
  rw [hdiv] at hmem
  have hcases : g=1 ∨ g=2 ∨ g=4 := by simpa using hmem
  have hg : g=2 ∨ g=4 := by
    rcases hcases with h | h | h
    · rw [h] at h2; norm_num at h2
    · exact Or.inl h
    · exact Or.inr h
  have he := four_dvd_gcd_iff t
  change (g=if t%4=1 then 4 else 2)
  by_cases ht : t%4=1
  · simp only [ht,ite_true]
    have hd : 4 ∣ g := he.mpr ht
    rcases hg with h | h
    · rw [h] at hd; norm_num at hd
    · exact h
  · simp only [ht,ite_false]
    rcases hg with h | h
    · exact h
    · have hd : 4 ∣ g := by rw [h]
      exact (ht (he.mp hd)).elim

/-- The literal full prime-power-coded common-divisor statistic. -/
def commonPacket (phase : ℕ → ℂ) (t : ℕ) : ℂ :=
  primeLegDivisor phase (Nat.gcd (quadratic t) (quadratic (t+1)))

/-- Every possible common prime-power layer is explicit: two and four. -/
theorem commonPacket_eq (phase : ℕ → ℂ) (t : ℕ) :
    commonPacket phase t = (Real.log 2 : ℂ)*phase 2 +
      if t%4=1 then (Real.log 2 : ℂ)*phase 4 else 0 := by
  have hd2 : (2:ℕ).divisors={1,2} := by decide
  have hd4 : (4:ℕ).divisors={1,2,4} := by decide
  have hl2 := ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  norm_num at hl2
  have hl4 : ArithmeticFunction.vonMangoldt 4=Real.log 2 := by
    rw [show (4:ℕ)=2^2 from rfl,ArithmeticFunction.vonMangoldt_apply_pow (by decide),hl2]
  unfold commonPacket
  rw [adjacent_gcd]
  by_cases ht : t%4=1
  · simp [ht,primeLegDivisor,hd4,hl2,hl4]
  · simp [ht,primeLegDivisor,hd2,hl2]

/-- Exact count of the retained four-layer residue among the first T rows. -/
theorem residue_count (T : ℕ) :
    (∑ t ∈ Finset.range T, if t%4=1 then (1:ℕ) else 0)=(T+2)/4 := by
  induction T with
  | zero => norm_num
  | succ T ih =>
    rw [Finset.sum_range_succ,ih]
    split_ifs <;> omega

/-- Growing aggregation remains an exactly periodic two-layer statistic. -/
theorem sum_commonPacket_eq (phase : ℕ → ℂ) (T : ℕ) :
    (∑ t ∈ Finset.range T, commonPacket phase t) =
      (T:ℂ)*(Real.log 2 : ℂ)*phase 2+
        (((T+2)/4:ℕ):ℂ)*(Real.log 2 : ℂ)*phase 4 := by
  simp_rw [commonPacket_eq]
  rw [Finset.sum_add_distrib]
  have hc : (∑ t ∈ Finset.range T,
      if t%4=1 then (Real.log 2 : ℂ)*phase 4 else 0) =
      (((T+2)/4:ℕ):ℂ)*((Real.log 2 : ℂ)*phase 4) := by
    have he (t : ℕ) :
        (if t%4=1 then (Real.log 2 : ℂ)*phase 4 else 0) =
          ((if t%4=1 then (1:ℕ) else 0):ℂ)*((Real.log 2 : ℂ)*phase 4) := by
      split_ifs <;> simp
    simp_rw [he]
    have hn : (∑ t ∈ Finset.range T, if t%4=1 then (1:ℂ) else 0) =
        (((T+2)/4:ℕ):ℂ) := by exact_mod_cast residue_count T
    norm_num only [Nat.cast_one]
    rw [← Finset.sum_mul,hn]
  rw [hc]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  ring

/-- Remove the exact mean density of both retained prime-power layers. -/
def centeredPacket (phase : ℕ → ℂ) (T : ℕ) : ℂ :=
  (∑ t ∈ Finset.range T, commonPacket phase t)-
    ((T:ℂ)*(Real.log 2 : ℂ)*phase 2+(T:ℂ)/4*(Real.log 2 : ℂ)*phase 4)

/-- The entire centered statistic is a bounded residue-count discrepancy. -/
theorem centeredPacket_eq (phase : ℕ → ℂ) (T : ℕ) :
    centeredPacket phase T =
      ((((T+2)/4:ℕ):ℂ)-(T:ℂ)/4)*(Real.log 2 : ℂ)*phase 4 := by
  unfold centeredPacket
  rw [sum_commonPacket_eq]
  ring

/-- No exterior row mass is lost: the exact growing sum has bounded error. -/
theorem norm_centeredPacket_le (phase : ℕ → ℂ) (T : ℕ)
    (hphase : ‖phase 4‖≤1) : ‖centeredPacket phase T‖≤Real.log 2 := by
  have hn1 : 4*((T+2)/4)≤T+4 := by omega
  have hn2 : T≤4*((T+2)/4)+4 := by omega
  have hr1 : (4:ℝ)*(((T+2)/4:ℕ):ℝ)≤(T:ℝ)+4 := by exact_mod_cast hn1
  have hr2 : (T:ℝ)≤(4:ℝ)*(((T+2)/4:ℕ):ℝ)+4 := by exact_mod_cast hn2
  have habs : |(((T+2)/4:ℕ):ℝ)-(T:ℝ)/4|≤1 := by
    rw [abs_le]
    constructor <;> linarith
  have hnorm : ‖((((T+2)/4:ℕ):ℂ)-(T:ℂ)/4)‖≤1 := by
    have he : (((T+2)/4:ℕ):ℂ)-(T:ℂ)/4 =
        (((((T+2)/4:ℕ):ℝ)-(T:ℝ)/4:ℝ):ℂ) := by push_cast; ring
    rw [he,Complex.norm_real,Real.norm_eq_abs]
    exact habs
  rw [centeredPacket_eq,norm_mul,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (Real.log_nonneg (by norm_num : (1:ℝ)≤2))]
  calc
    _ ≤ 1*Real.log 2*1 := mul_le_mul
      (mul_le_mul_of_nonneg_right hnorm (Real.log_nonneg (by norm_num)))
      hphase (norm_nonneg _) (by positivity)
    _ = Real.log 2 := by ring

/-- Even moving row endpoints and unit codes add no positive-power source.
The two literal phases are retained before density centering. -/
theorem tendsto_scaled_centeredPacket (T : ℕ → ℕ) (phase : ℕ → ℕ → ℂ)
    (hphase : ∀ J, ‖phase J 4‖≤1) {beta : ℝ} (hbeta : 0<beta) :
    Filter.Tendsto (fun J : ℕ =>
      (Real.exp (-2*beta*Real.log 2)^J : ℂ)*centeredPacket (phase J) (T J))
      Filter.atTop (𝓝 0) := by
  let r := Real.exp (-2*beta*Real.log 2)
  have hr0 : 0≤r := (Real.exp_pos _).le
  have hr1 : r<1 := Real.exp_lt_one_iff.mpr
    (mul_neg_of_neg_of_pos (by linarith) (Real.log_pos (by norm_num)))
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const (Real.log 2)
  simp only [zero_mul] at ht
  apply squeeze_zero_norm (a := fun J : ℕ => r^J*Real.log 2) _ ht
  intro J
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul_of_nonneg_left (norm_centeredPacket_le (phase J) (T J) (hphase J))
    (pow_nonneg hr0 J)

end RiemannGaussian.ArithmeticOperatorQuadraticNormAudit

#lint+ in RiemannGaussian.ArithmeticOperatorQuadraticNormAudit

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
  logInfo m!"Quadratic norm adjacency: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.writeFile ".lake/arithmetic-operator-polynomial-norm-source/adjacent-axioms.json"
    (Json.mkObj [("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
