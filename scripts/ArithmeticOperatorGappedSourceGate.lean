/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.ArithmeticOperatorGappedMinorAudit
import scripts.ArithmeticOperatorResultantDiscrepancy

/-!
# Literal common-prime-power discrepancy of a gapped Pascal minor

The common factor of `q(t)` and `q(t+h)` is observed through every
von-Mangoldt denominator, with its full complex phase. Exact residue
centering gives a bound `2 log |h^2(h^2-5)|`, independent of the prefix
length. Thus polynomially growing positive shifts still give no positive
power-sized source in this CENTERED observation. The uncentered density,
the single-polynomial response and uncontrolled exterior weights are not
paid by this theorem. The native integer minor and all prime-power root
counts are supplied by the imported local leaf, not assumed as a model.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option warningAsError true
noncomputable section
open Filter
open scoped BigOperators Classical Topology
namespace OpenAIReview.GappedSourceGate
open GappedMinor ResultantDiscrepancy

/-- The literal prime-power correlation before its exact density is removed. -/
def commonPacket (T h : ℕ) (phase : ℕ → ℂ) : ℂ :=
  ∑ t ∈ Finset.range T, ∑ d ∈ (Nat.gcd (q t) (q (t+h))).divisors,
    (ArithmeticFunction.vonMangoldt d : ℂ)*phase d

/-- Exact complete-period residue density; it retains every denominator phase. -/
def commonDensity (T h : ℕ) (phase : ℕ → ℂ) : ℂ :=
  ∑ d ∈ (resultant h).divisors, (ArithmeticFunction.vonMangoldt d : ℂ)*phase d*
    (((jointRoots h d).card : ℂ)*T/d)

/-- The actual centered correlation, with no independent error hypothesis. -/
def centeredCommonPacket (T h : ℕ) (phase : ℕ → ℂ) : ℂ :=
  commonPacket T h phase-commonDensity T h phase

/-- The exact divisor support is the same resultant for every cutoff row. -/
theorem gcd_divisors (t : ℕ) {h : ℕ} (hh : 0<h) :
    (Nat.gcd (q t) (q (t+h))).divisors =
      ((resultant h).divisors).filter (fun d => d ∣ q t ∧ d ∣ q (t+h)) := by
  have hq : 0<q t := by unfold q; positivity
  have hg : Nat.gcd (q t) (q (t+h)) ≠ 0 :=
    (Nat.gcd_pos_of_pos_left _ hq).ne'
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨hd,_⟩
    obtain ⟨hl,hr⟩ := Nat.dvd_gcd_iff.mp hd
    exact ⟨⟨common_divisor_resultant hl hr,(resultant_pos hh).ne'⟩,hl,hr⟩
  · rintro ⟨_,hl,hr⟩
    exact ⟨Nat.dvd_gcd hl hr,hg⟩

/-- Joining all literal integer rows gives the exact prime-power prefix
count. No proper prime powers or phases are removed in the interchange. -/
theorem commonPacket_eq_counts (T : ℕ) {h : ℕ} (hh : 0<h) (phase : ℕ → ℂ) :
    commonPacket T h phase =
      ∑ d ∈ (resultant h).divisors, (ArithmeticFunction.vonMangoldt d : ℂ)*phase d*
        (T.count (fun t => d ∣ q t ∧ d ∣ q (t+h)) : ℂ) := by
  unfold commonPacket
  simp_rw [gcd_divisors _ hh, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.count_eq_card_filter_range]
  ring

/-- Native polynomial periodicity identifies the centered literal packet
with the bounded-root discrepancy. This is not a surrogate density model. -/
theorem centered_eq_packet (T : ℕ) {h : ℕ} (hh : 0<h) (phase : ℕ → ℂ) :
    centeredCommonPacket T h phase =
      packet T (resultant h) (jointRoots h) phase := by
  rw [centeredCommonPacket,commonPacket_eq_counts T hh]
  simp only [commonDensity,packet,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0<d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 (resultant_pos hh)
  have hc : T.count (fun t => d ∣ q t ∧ d ∣ q (t+h)) =
      T.count (fun t => t%d ∈ jointRoots h d) := by
    simp only [Nat.count_eq_card_filter_range]
    congr 1
    ext t
    simp only [Finset.mem_filter,joint_divisibility_iff_mod_mem h d t hdpos]
  rw [rootError_eq_count T d (jointRoots h d)
    (fun a ha => Finset.mem_range.mp (Finset.mem_filter.mp ha).1),hc]
  push_cast
  ring

/-- The prime-power root theorem applies exactly where the actual
von-Mangoldt coefficient is nonzero, including every proper power. -/
theorem jointRoots_card_le_two_of_mangoldt_ne_zero (h d : ℕ)
    (hd : ArithmeticFunction.vonMangoldt d ≠ 0) : (jointRoots h d).card ≤ 2 := by
  obtain ⟨p,r,hp,_,rfl⟩ := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hd
  exact jointRoots_prime_power_card_le_two h (Nat.prime_iff.mpr hp)

/-- The joined, density-centered native correlation is logarithmic in
the positive shift, uniformly in the prefix and every unit-bounded phase. -/
theorem norm_centeredCommonPacket_le (T : ℕ) {h : ℕ} (hh : 0<h) (phase : ℕ → ℂ)
    (hphase : ∀ d ∈ (resultant h).divisors, ‖phase d‖ ≤ 1) :
    ‖centeredCommonPacket T h phase‖ ≤ 2*Real.log (resultant h) := by
  rw [centered_eq_packet T hh]
  exact norm_packet_le_log T (resultant h) (jointRoots h) phase hphase
    (fun d _ hd => jointRoots_card_le_two_of_mangoldt_ne_zero h d hd)

/-- In particular the literal twisted denominator `d^(-i*y)` is retained;
the phase is evaluated at each prime power, not at its base prime. -/
theorem norm_twisted_centered_le (T : ℕ) {h : ℕ} (hh : 0<h) (y : ℝ) :
    ‖centeredCommonPacket T h (fun d => (d : ℂ)^(-Complex.I*(y : ℂ)))‖ ≤
      2*Real.log (resultant h) := by
  apply norm_centeredCommonPacket_le T hh
  intro d hd
  have hdpos : (0 : ℝ) < d := by
    exact_mod_cast Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 (resultant_pos hh)
  rw [← Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hdpos]
  simp

/-- Arbitrary bounded row weights do NOT inherit the unweighted prefix
discrepancy estimate: this native prime-eleven periodic code has a nonzero
positive mean. Its weights are exactly plus or minus one. -/
theorem weighted_centering_period_counterexample :
    (∑ t ∈ Finset.range 11,
      (if 11 ∣ q t ∧ 11 ∣ q (t+4) then (1 : ℝ) else -1)*
        ((if 11 ∣ q t ∧ 11 ∣ q (t+4) then (1 : ℝ) else 0)-1/11)) = 20/11 := by
  norm_num [Finset.sum_range_succ,q]

/-- An explicit uniform height bound for the actual positive-shift resultant. -/
theorem resultant_le {h : ℕ} (hh : 0<h) : resultant h ≤ 6*h^4 := by
  have hh1 : (1 : ℤ) ≤ h := by exact_mod_cast hh
  have hs : (1 : ℤ) ≤ (h : ℤ)^2 := by nlinarith
  have ha : |(h : ℤ)^2-5| ≤ 6*(h : ℤ)^2 := by
    rw [abs_le]
    constructor <;> nlinarith
  have hb : |(h : ℤ)^2*((h : ℤ)^2-5)| ≤ 6*(h : ℤ)^4 := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ (h : ℤ)^2*(6*(h : ℤ)^2) := mul_le_mul_of_nonneg_left ha (sq_nonneg _)
      _ = _ := by ring
  unfold resultant
  apply Int.ofNat_le.mp
  simpa only [Int.natCast_natAbs,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow] using hb

/-- Polynomial growth in the dyadic physical scale gives only linear
growth of the logarithmic resultant budget. -/
theorem log_resultant_le (A J : ℕ) {h : ℕ} (hh : 0<h)
    (hgrowth : h ≤ 2^(A*(J+1))) :
    Real.log (resultant h) ≤
      (Real.log 6+4*(A : ℝ)*Real.log 2)*((J : ℝ)+1) := by
  have hr : 0 < (resultant h : ℝ) := by exact_mod_cast resultant_pos hh
  have hhr : 0 < (h : ℝ) := by exact_mod_cast hh
  have hupper : (resultant h : ℝ) ≤ 6*(h : ℝ)^4 := by exact_mod_cast resultant_le hh
  have hg : Real.log (h : ℝ) ≤ ((A : ℝ)*((J : ℝ)+1))*Real.log 2 := by
    have hpow : (h : ℝ) ≤ (2 : ℝ)^(A*(J+1)) := by exact_mod_cast hgrowth
    have he := Real.log_le_log hhr hpow
    rw [Real.log_pow] at he
    exact_mod_cast he
  calc
    _ ≤ Real.log (6*(h : ℝ)^4) := Real.log_le_log hr hupper
    _ = Real.log 6+4*Real.log (h : ℝ) := by
      rw [Real.log_mul (by norm_num) (pow_ne_zero _ hhr.ne'),Real.log_pow]
      norm_num
    _ ≤ Real.log 6+4*(((A : ℝ)*((J : ℝ)+1))*Real.log 2) := by gcongr
    _ ≤ _ := by
      have hl : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
      have hj : (0 : ℝ) ≤ J := by positivity
      nlinarith [mul_nonneg hl hj]

/-- No positive-power source survives exact residue centering, even
when the actual shift grows polynomially in the dyadic physical scale.
This conclusion is uniform in the prefix sequence and denominator phases. -/
theorem tendsto_centered_of_polynomial_shift (r : ℝ) (hr0 : 0≤r) (hr1 : r<1)
    (A : ℕ) (T h : ℕ → ℕ) (phase : ℕ → ℕ → ℂ)
    (hh : ∀ J, 0<h J) (hgrowth : ∀ J, h J ≤ 2^(A*(J+1)))
    (hphase : ∀ J d, d ∈ (resultant (h J)).divisors → ‖phase J d‖ ≤ 1) :
    Tendsto (fun J : ℕ => (r : ℂ)^J*centeredCommonPacket (T J) (h J) (phase J))
      atTop (nhds 0) := by
  simp_rw [centered_eq_packet _ (hh _)]
  exact tendsto_packet_of_log_bound r (Real.log 6+4*(A : ℝ)*Real.log 2) hr0 hr1
    T (fun J => resultant (h J)) (fun J => jointRoots (h J)) phase hphase
    (fun J d _ hd => jointRoots_card_le_two_of_mangoldt_ne_zero (h J) d hd)
    (fun J => log_resultant_le A J (hh J) (hgrowth J))

end OpenAIReview.GappedSourceGate

#lint+ in OpenAIReview.GappedSourceGate

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
  logInfo m!"Native gapped source gate: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-gapped-source-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-gapped-source-gate/axioms.json"
    (Json.mkObj [("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
