/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorIncidenceFreedom
import RiemannGaussian.ArithmeticOperatorRamanujanFreedom

/-!
# Composite divisor-form Ramanujan codes impose no finite profile constraint

The exact integer identity `sum_(q|d) c_q(n) = d*1[d|n]` makes every
positive-index divisor indicator a finite Ramanujan code. Möbius inversion
then realizes every finite complex profile with value zero at the unit,
while its common coprime coefficient remains exactly zero.

This covers arbitrary composite moduli through the physical cutoff and
unrestricted coefficients, including profiles that depend on the prime
power exponent. It does NOT classify bounded coefficient budgets,
nonprincipal residue characters or nonlinear prime-column interactions.
Principal centering in this class supplies no collective prime constraint.
-/

namespace RiemannGaussian.ArithmeticOperatorCompositeRamanujanFreedom
noncomputable section
open Complex ArithmeticOperatorRamanujanAudit
open ArithmeticOperatorKummerCutoff ArithmeticOperatorIncidenceFreedom
open scoped BigOperators

private def divisibilityRow (n : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun d => if d ∣ n then (d : ℤ) else 0, by simp⟩

private theorem ramanujan_eq_convolution {q : ℕ} (hq : 0 < q) (n : ℕ) :
    ramanujanDivisor q n = (divisibilityRow n*ArithmeticFunction.moebius) q := by
  classical
  have he : q.divisors.filter (fun d => d ∣ n) = (Nat.gcd q n).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hd,_⟩,hn⟩
      exact ⟨⟨hd,hn⟩,(Nat.gcd_pos_of_pos_left n hq).ne'⟩
    · rintro ⟨⟨hd,hn⟩,_⟩
      exact ⟨⟨hd,hq.ne'⟩,hn⟩
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d a => divisibilityRow n d*ArithmeticFunction.moebius a)]
  simp only [divisibilityRow, ArithmeticFunction.coe_mk, ite_mul, zero_mul]
  rw [← Finset.sum_filter, he]
  rfl

/-- Exact finite integer cancellation, before any prime specialization. -/
theorem sum_divisors_ramanujan {d : ℕ} (hd : 0 < d) (n : ℕ) :
    (∑ q ∈ d.divisors, ramanujanDivisor q n) = if d ∣ n then (d : ℤ) else 0 := by
  have he : (∑ q ∈ d.divisors, ramanujanDivisor q n) =
      ∑ q ∈ d.divisors, (divisibilityRow n*ArithmeticFunction.moebius) q :=
    Finset.sum_congr rfl (fun q hq => ramanujan_eq_convolution
      (Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hq) hd) n)
  rw [he, ← ArithmeticFunction.coe_mul_zeta_apply, mul_assoc,
    ArithmeticFunction.moebius_mul_coe_zeta, mul_one]
  rfl

/-- The divisor indicator is an exact finite code, not an infinite
Ramanujan expansion or a primitive-character assertion. -/
theorem normalized_divisor_code {d : ℕ} (hd : 0 < d) (n : ℕ) :
    (∑ q ∈ d.divisors, (ramanujanDivisor q n : ℂ))/(d : ℂ) =
      if d ∣ n then 1 else 0 := by
  rw [← Int.cast_sum, sum_divisors_ramanujan hd]
  split_ifs <;> simp [hd.ne']

/-- The complete finite coefficient array, including unit and composite
moduli. No coefficient-budget estimate is being asserted. -/
def coefficients (X : ℕ) (a : ℕ → ℂ) (q : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 2 X, if q ∣ d then a d/(d : ℂ) else 0

private theorem filter_divisors_prefix {X d : ℕ} (hd : 0 < d) (hdX : d ≤ X) :
    (Finset.Icc 1 X).filter (fun q => q ∣ d) = d.divisors := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨_,hq⟩
    exact ⟨hq,hd.ne'⟩
  · rintro ⟨hq,_⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hq hd,(Nat.le_of_dvd hd hq).trans hdX⟩,hq⟩

/-- All modulus rows join exactly to the prescribed divisor profile.
Every native integer endpoint and every subset sign remains literal. -/
theorem code_eq_indicators (X : ℕ) (a : ℕ → ℂ) (n : ℕ) :
    code (Finset.Icc 1 X) (coefficients X a) n =
      ∑ d ∈ Finset.Icc 2 X, if d ∣ n then a d else 0 := by
  classical
  unfold code coefficients
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hd2,hdX⟩ := Finset.mem_Icc.mp hd
  have hd0 : 0 < d := by omega
  have he : (∑ q ∈ Finset.Icc 1 X,
      (if q ∣ d then a d/(d : ℂ) else 0)*(ramanujanDivisor q n : ℂ)) =
      (a d/(d : ℂ))*(∑ q ∈ d.divisors, (ramanujanDivisor q n : ℂ)) := by
    simp only [ite_mul, zero_mul]
    rw [← Finset.sum_filter, filter_divisors_prefix hd0 hdX, Finset.mul_sum]
  rw [he]
  have hh := normalized_divisor_code hd0 n
  calc
    _ = a d*((∑ q ∈ d.divisors, (ramanujanDivisor q n : ℂ))/(d : ℂ)) := by ring
    _ = _ := by rw [hh]; split_ifs <;> simp

/-- Centering does not restrict `a`: it holds for every profile. -/
theorem principalCoefficient_zero (X : ℕ) (a : ℕ → ℂ) :
    principalCoefficient (Finset.Icc 1 X) (coefficients X a) = 0 := by
  have he := code_eq_indicators X a 1
  rw [code_of_coprime _ _ (fun q _ => Nat.coprime_one_right q)] at he
  rw [he]
  apply Finset.sum_eq_zero
  intro d hd
  have hn : ¬d ∣ 1 := by
    intro h
    have hh := Nat.dvd_one.mp h
    have hb := (Finset.mem_Icc.mp hd).1
    omega
  simp only [ite_eq_right hn]

private theorem indicators_eq_observation {X n : ℕ} (hn : 0 < n) (hnX : n ≤ X)
    (a : ℕ → ℂ) (ha : a 1 = 0) :
    (∑ d ∈ Finset.Icc 2 X, if d ∣ n then a d else 0) = divisorObservation a n := by
  classical
  have hfilter : (Finset.Icc 2 X).filter (fun d => d ∣ n) = n.divisors.erase 1 := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_erase, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd2,_⟩,hd⟩
      exact ⟨by omega,hd,hn.ne'⟩
    · rintro ⟨hne,hd,_⟩
      exact ⟨⟨by have hh := Nat.pos_of_dvd_of_pos hd hn; omega,
        (Nat.le_of_dvd hn hd).trans hnX⟩,hd⟩
  rw [← Finset.sum_filter, hfilter]
  exact Finset.sum_subset (Finset.erase_subset _ _) (fun d hmem hd => by
    have he : d = 1 := by
      by_contra hne
      exact hd (Finset.mem_erase.mpr ⟨hne,hmem⟩)
    simpa [he] using ha)

/-- Universal finite surjectivity: principal-centered composite codes
can realize EVERY positive-index profile with unit value zero. -/
theorem exists_centered_code_with_any_profile (X : ℕ) (g : ℕ → ℂ) (hg : g 1 = 0) :
    ∃ lambda : ℕ → ℂ,
      principalCoefficient (Finset.Icc 1 X) lambda = 0 ∧
      ∀ n ∈ Finset.Icc 1 X, code (Finset.Icc 1 X) lambda n = g n := by
  refine ⟨coefficients X (inverseRows g),principalCoefficient_zero X _,?_⟩
  intro n hn
  obtain ⟨hn0,hnX⟩ := Finset.mem_Icc.mp hn
  rw [code_eq_indicators, indicators_eq_observation hn0 hnX _
    (by simp [inverseRows, hg]), observation_inverseRows g hn0]

/-- In particular ANY complete prime-power profile at the literal
cutoff is permitted. No cross-prime/order restriction comes from the
centering or the exact finite Ramanujan bookkeeping itself. -/
theorem native_profile_realization (X : ℕ) (g w : ℕ → ℂ) (hg : g 1 = 0) :
    ∃ lambda : ℕ → ℂ,
      principalCoefficient (Finset.Icc 1 X) lambda = 0 ∧
      (∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ)*w n*
        code (Finset.Icc 1 X) lambda n) =
        ∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ)*w n*g n := by
  obtain ⟨lambda,hc,he⟩ := exists_centered_code_with_any_profile X g hg
  refine ⟨lambda,hc,Finset.sum_congr rfl (fun n hn => by rw [he n hn])⟩

/-- Source/density preflight: one centered code restores the WHOLE
actual Mangoldt sum for every test weight, phase and literal mask at
this cutoff. Its principal cancellation therefore does not remove the
zeta pole or create an independent bound on the retained zero signal. -/
theorem exists_centered_code_restoring_mangoldt (X : ℕ) :
    ∃ lambda : ℕ → ℂ,
      principalCoefficient (Finset.Icc 1 X) lambda = 0 ∧
      ∀ w : ℕ → ℂ,
        (∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ)*w n*
          code (Finset.Icc 1 X) lambda n) =
          ∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ)*w n := by
  let g : ℕ → ℂ := fun n => if n = 1 then 0 else 1
  obtain ⟨lambda,hc,he⟩ := exists_centered_code_with_any_profile X g (by simp [g])
  refine ⟨lambda,hc,?_⟩
  intro w
  apply Finset.sum_congr rfl
  intro n hn
  rw [he n hn]
  by_cases h1 : n = 1
  · simp [h1, g]
  · simp [g, h1]

end
end RiemannGaussian.ArithmeticOperatorCompositeRamanujanFreedom
