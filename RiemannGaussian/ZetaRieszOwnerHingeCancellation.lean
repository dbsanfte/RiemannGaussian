/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSignedDensityCancellation
import RiemannGaussian.ZetaRieszCoreOwnerPayment
import Mathlib.NumberTheory.Bertrand

/-!
# Cancellation across every owner-hinge cutoff

The existing translated owner scalar is a prime-excluded signed density
Riesz mean. Its exact one-prime recurrence and the already proved uniform
density Riesz bound give a cutoff-independent allowance. The original
signed cofactor moments and literal comparison variation remain explicit.

The same recurrence gives a7/p comparison with ONE common density Riesz
function, whose cutoff Lipschitz constant is its exact squarefree density.
Owner summation by parts therefore retains cross-owner cancellation in
signed cumulative owner sums before any norm. Their source cost is open.

The raw comparison extension is then cleaned on the ENTIRE published
unpaid count/bin/owner geometry. Its squarefree rows and signed carrier
are unchanged exactly. Edges wholly outside that geometry have zero
variation cost, and the cleaned centered bound enters the existing
whole-floor ledger with no new error. Its numerical floor remains open.

The cleaned RAW weight still has canonical-owner zeros at multiples of
every prime larger than its owner. A periodic-zero argument and Bertrand
give an exponential lower bound on the CURRENT absolute comparison price
on small-owner columns. This is a majorant audit, not a lower bound on
the signed carrier or an assertion that any population has large mass.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszOwnerHingeCancellation
open Real ZetaRieszSignedDensityMain ZetaRieszLongCutoffError

private def coefficient (n : ℕ) : ℝ := (μ n : ℝ)*SquarefreeCounting.density n.primeFactors

private def excludedCoefficient (p n : ℕ) : ℝ := if p ∣ n then 0 else coefficient n

private def excludedRiesz (p : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊exp t⌋₊, excludedCoefficient p n*max 0 (t-log n)

private theorem coefficient_prime_mul {p n : ℕ} (hp : p.Prime)
    (hn : n ≠ 0) (hpn : ¬p ∣ n) :
    coefficient (p*n) = -((p : ℝ)+1)⁻¹*coefficient n := by
  have hmu : (μ (p*n) : ℝ) = (μ p : ℝ)*(μ n : ℝ) := by
    exact_mod_cast ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (hp.coprime_iff_not_dvd.mpr hpn)
  have hnot : p ∉ n.primeFactors := fun h => hpn (Nat.dvd_of_mem_primeFactors h)
  rw [coefficient, hmu, ArithmeticFunction.moebius_apply_prime hp,
    Int.cast_neg, Int.cast_one, Nat.primeFactors_mul hp.ne_zero hn,
    hp.primeFactors, Finset.singleton_union,
    density_marks _ (fun q hq => by
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact hp
      · exact Nat.prime_of_mem_primeFactors hq), Finset.prod_insert hnot,
    coefficient, density_marks _ (fun q hq => Nat.prime_of_mem_primeFactors hq)]
  ring

private theorem excluded_coefficient_recurrence {p n : ℕ} (hp : p.Prime)
    (hn : 0 < n) :
    excludedCoefficient p n = coefficient n + ((p : ℝ)+1)⁻¹*
      (if p ∣ n then excludedCoefficient p (n/p) else 0) := by
  by_cases hpn : p ∣ n
  · obtain ⟨m,rfl⟩ := hpn
    have hm : m ≠ 0 := by intro h; simp [h] at hn
    have hpdiv : p ∣ p*m := dvd_mul_right _ _
    rw [if_pos hpdiv, Nat.mul_div_cancel_left _ hp.pos]
    by_cases hpm : p ∣ m
    · have hsf : ¬Squarefree (p*m) := by
        intro h
        exact (hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul h)) hpm
      have hmu : (μ (p*m) : ℝ) = 0 := by
        exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf
      simp [excludedCoefficient, coefficient, hpdiv, hpm, hmu]
    · rw [coefficient_prime_mul hp hm hpm]
      simp [excludedCoefficient, hpdiv, hpm]
  · simp [excludedCoefficient, hpn]

private theorem sum_divisible_reindex {p : ℕ} (hp : 0 < p) (M : ℕ) (g : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 M, if p ∣ n then g (n/p) else 0) =
      ∑ m ∈ Finset.Icc 1 (M/p), g m := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun n _ => n/p)
  · intro n hn
    obtain ⟨hn,hdiv⟩ := Finset.mem_filter.mp hn
    have hpos := (Finset.mem_Icc.mp hn).1
    have hle := (Finset.mem_Icc.mp hn).2
    exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hpos hdiv) hp,
      Nat.div_le_div_right hle⟩
  · intro n hn m hm he
    have hn' := (Finset.mem_filter.mp hn).2
    have hm' := (Finset.mem_filter.mp hm).2
    calc
      n = p*(n/p) := (Nat.mul_div_cancel' hn').symm
      _ = p*(m/p) := congrArg (fun a => p*a) he
      _ = m := Nat.mul_div_cancel' hm'
  · intro m hm
    obtain ⟨hm0,hmM⟩ := Finset.mem_Icc.mp hm
    refine ⟨p*m, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.mul_pos hp hm0, ?_⟩, dvd_mul_right _ _⟩, ?_⟩
    · have h := (Nat.le_div_iff_mul_le hp).mp hmM
      simpa only [Nat.mul_comm] using h
    · exact Nat.mul_div_cancel_left _ hp
  · intro n _
    rfl

private theorem floor_shift {p : ℕ} (hp : 0 < p) (t : ℝ) :
    ⌊exp (t-log p)⌋₊ = ⌊exp t⌋₊/p := by
  rw [exp_sub, exp_log (by exact_mod_cast hp), Nat.floor_div_natCast]

private theorem excluded_riesz_recurrence {p : ℕ} (hp : p.Prime) (t : ℝ) :
    excludedRiesz p t = densityRiesz t + ((p : ℝ)+1)⁻¹*excludedRiesz p (t-log p) := by
  have hn (n : ℕ) (h : n ∈ Finset.Icc 1 ⌊exp t⌋₊) := (Finset.mem_Icc.mp h).1
  have he : excludedRiesz p t =
      (∑ n ∈ Finset.Icc 1 ⌊exp t⌋₊, coefficient n*max 0 (t-log n)) +
      ((p : ℝ)+1)⁻¹*(∑ n ∈ Finset.Icc 1 ⌊exp t⌋₊,
        (if p ∣ n then excludedCoefficient p (n/p) else 0)*max 0 (t-log n)) := by
    rw [excludedRiesz, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n h
    rw [excluded_coefficient_recurrence hp (hn n h)]
    ring
  have ht : (∑ n ∈ Finset.Icc 1 ⌊exp t⌋₊,
        (if p ∣ n then excludedCoefficient p (n/p) else 0)*max 0 (t-log n)) =
      excludedRiesz p (t-log p) := by
    calc
      _ = ∑ n ∈ Finset.Icc 1 ⌊exp t⌋₊, if p ∣ n then
          excludedCoefficient p (n/p)*max 0 (t-log p-log (n/p : ℕ)) else 0 := by
        apply Finset.sum_congr rfl
        intro n h
        by_cases hd : p ∣ n
        · have hnp : 0 < n/p := Nat.div_pos (Nat.le_of_dvd (hn n h) hd) hp.pos
          have hl : log n = log p+log (n/p : ℕ) := by
            calc
              _ = log (p*(n/p) : ℕ) := congrArg (fun a : ℕ => log a)
                (Nat.mul_div_cancel' hd).symm
              _ = _ := by rw [Nat.cast_mul,
                log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hnp.ne')]
          rw [if_pos hd, if_pos hd, hl]
          congr 2
          ring
        · simp [hd]
      _ = ∑ m ∈ Finset.Icc 1 (⌊exp t⌋₊/p),
          excludedCoefficient p m*max 0 (t-log p-log m) :=
        sum_divisible_reindex hp.pos _
          (fun m => excludedCoefficient p m*max 0 (t-log p-log m))
      _ = _ := by rw [excludedRiesz, floor_shift hp.pos]
  rw [he, ht, densityRiesz_eq_hinge t le_rfl]
  rfl

private theorem excluded_riesz_bound {p : ℕ} (hp : p.Prime) (t : ℝ) :
    |excludedRiesz p t| ≤ 7*((p : ℝ)+1)/(p : ℝ) := by
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hb : ∀ M : ℕ, ∀ t : ℝ, ⌊exp t⌋₊ = M →
      |excludedRiesz p t| ≤ 7*((p : ℝ)+1)/(p : ℝ) := by
    intro M
    induction M using Nat.strong_induction_on with
    | h M ih =>
      intro t ht
      by_cases hM : M = 0
      · simp only [excludedRiesz, ht, hM, Finset.Icc_eq_empty_of_lt
          (by norm_num : (0 : ℕ) < 1), Finset.sum_empty, abs_zero]
        positivity
      have hsmall : M/p < M := Nat.div_lt_self (Nat.pos_of_ne_zero hM) hp.one_lt
      have hi := ih (M/p) hsmall (t-log p) (by rw [floor_shift hp.pos, ht])
      rw [excluded_riesz_recurrence hp t]
      calc
        _ ≤ |densityRiesz t| + |((p : ℝ)+1)⁻¹*excludedRiesz p (t-log p)| := abs_add_le _ _
        _ ≤ 7 + ((p : ℝ)+1)⁻¹*(7*((p : ℝ)+1)/(p : ℝ)) := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((p : ℝ)+1)⁻¹)]
          exact add_le_add (densityRiesz_bound t)
            (mul_le_mul_of_nonneg_left hi (by positivity))
        _ = _ := by field_simp
  exact hb ⌊exp t⌋₊ t rfl

private theorem normalized_marked_coefficient {p n : ℕ} (hp : p.Prime) :
    (((p : ℝ)+1)/(p : ℝ))*
      ((μ n : ℂ)*RoughSquarefreeCounting.markedDensity {p} n).re =
        excludedCoefficient p n := by
  by_cases hpd : p ∣ n
  · rw [RoughSquarefreeCounting.markedDensity_eq_zero_of_sieve_hit {p}
      (by simpa using hp) ⟨p,by simp,hpd⟩]
    simp [excludedCoefficient,hpd]
  by_cases hsf : Squarefree n
  · have hnot : p ∉ n.primeFactors := fun h => hpd (Nat.dvd_of_mem_primeFactors h)
    have hmarks : SquarefreeCounting.density (insert p n.primeFactors) =
        ((p : ℝ)+1)⁻¹*SquarefreeCounting.density n.primeFactors := by
      rw [density_marks _ (fun q hq => by
          rcases Finset.mem_insert.mp hq with rfl | hq
          · exact hp
          · exact Nat.prime_of_mem_primeFactors hq), Finset.prod_insert hnot,
        density_marks _ (fun q hq => Nat.prime_of_mem_primeFactors hq)]
      ring
    have hmark : RoughSquarefreeCounting.markedDensity {p} n =
        ((SquarefreeCounting.density n.primeFactors -
          SquarefreeCounting.density (insert p n.primeFactors) : ℝ) : ℂ) := by
      rw [RoughSquarefreeCounting.markedDensity, if_pos hsf]
      rw [show ({p} : Finset ℕ) = insert p ∅ from rfl, Finset.powerset_insert]
      simp [Finset.union_comm]
      ring
    have hpr : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hc : (μ n : ℂ) = ((μ n : ℝ) : ℂ) := by norm_cast
    rw [hmark, hc, ← Complex.ofReal_mul, Complex.ofReal_re, hmarks,
      excludedCoefficient, if_neg hpd, coefficient]
    field_simp
    ring
  · have hm : (μ n : ℝ) = 0 := by
      exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf
    have hmc : (μ n : ℂ) = 0 := by
      exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf
    simp [excludedCoefficient, coefficient, hpd, hm, hmc]

private theorem normalized_prefix {p : ℕ} (hp : p.Prime) (D : ℕ) :
    (((p : ℝ)+1)/(p : ℝ))*roughDensityPrefix {p} D =
      ∑ n ∈ Finset.Icc 1 D, excludedCoefficient p n := by
  rw [roughDensityPrefix, Complex.re_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => normalized_marked_coefficient hp)

private theorem owner_profile_eq_excluded_riesz {p : ℕ} (hp : p.Prime) (c : ℝ) :
    (((p : ℝ)+1)/(p : ℝ))*(∑ D ∈ Finset.Icc 1 ⌊exp c⌋₊,
      (max 0 (c-log D)-max 0 (c-log (D+1 : ℕ)))*roughDensityPrefix {p} D) =
        excludedRiesz p c := by
  have he : max 0 (c-log (⌊exp c⌋₊+1 : ℕ)) = 0 := by
    have ht : exp c < (⌊exp c⌋₊+1 : ℕ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (exp c)
    have hl : c < log (⌊exp c⌋₊+1 : ℕ) := by
      simpa only [log_exp] using log_lt_log (exp_pos _) ht
    exact max_eq_left (by linarith)
  rw [Finset.mul_sum]
  have hs := ZetaRieszSignedCutoffEnergy.abel_profile ⌊exp c⌋₊
    (fun d => max 0 (c-log d)) (excludedCoefficient p) he
  have hr : excludedRiesz p c = ∑ d ∈ Finset.Icc 1 ⌊exp c⌋₊,
      max 0 (c-log d)*excludedCoefficient p d := by
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [hr, hs]
  apply Finset.sum_congr rfl
  intro D _
  rw [← normalized_prefix hp D]
  ring

/-- The SAME complete signed owner-hinge scalar has a cutoff-independent
bound. All divisor parities and translated cutoff increments are summed
before charging the constant, with the exact owner factor retained. -/
theorem owner_hinge_cutoff_independent_bound {p : ℕ} (hp : p.Prime) (c : ℝ) :
    |(((p : ℝ)+1)/(p : ℝ))*(∑ D ∈ Finset.Icc 1 ⌊exp c⌋₊,
      (max 0 (c-log D)-max 0 (c-log (D+1 : ℕ)))*roughDensityPrefix {p} D)| ≤
        7*((p : ℝ)+1)/(p : ℝ) := by
  rw [owner_profile_eq_excluded_riesz hp c]
  exact excluded_riesz_bound hp c

/-- A rational allowance valid for every actual owner prime, independent
of the moving hinge height, all cofactor counts, and the radial order. -/
theorem owner_hinge_le_twenty_one_halves {p : ℕ} (hp : p.Prime) (c : ℝ) :
    |(((p : ℝ)+1)/(p : ℝ))*(∑ D ∈ Finset.Icc 1 ⌊exp c⌋₊,
      (max 0 (c-log D)-max 0 (c-log (D+1 : ℕ)))*roughDensityPrefix {p} D)| ≤
        21/2 := by
  apply (owner_hinge_cutoff_independent_bound hp c).trans
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  apply (div_le_iff₀ hpr).mpr
  linarith

/-- Every owner cutoff is joined before the constant price is applied to
the signed cofactor sum. The signed first moment is retained unchanged. -/
theorem owner_main_constant_bounds (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (L : ℝ) (U V : ℕ → ℝ) :
    let rho := SquarefreeCounting.density ∅
    let M := ∑ p ∈ P, (rho*U p - (((p : ℝ)+1)/(p : ℝ))*
      (∑ D ∈ Finset.Icc 1 ⌊exp (L-log p)⌋₊,
        (max 0 (L-log p-log D)-max 0 (L-log p-log (D+1 : ℕ)))*
          roughDensityPrefix {p} D)*V p)
    (∑ p ∈ P, (rho*U p-7*((p : ℝ)+1)/(p : ℝ)*|V p|)) ≤ M ∧
      M ≤ ∑ p ∈ P, (rho*U p+7*((p : ℝ)+1)/(p : ℝ)*|V p|) := by
  dsimp only
  constructor <;> apply Finset.sum_le_sum <;> intro p hp
  all_goals
    have hc := mul_le_mul_of_nonneg_right
      (owner_hinge_cutoff_independent_bound (hP p hp) (L-log p)) (abs_nonneg (V p))
    rw [← abs_mul] at hc
    have hlo := (abs_le.mp hc).1
    have hhi := (abs_le.mp hc).2
    linarith only [hlo, hhi]

/-- Both one-sided estimates for the ORIGINAL scaled masked residual sum,
with a hinge-height-independent main allowance. No count/period/mask is
completed. The literal comparison variation and signed moments are unpaid. -/
theorem literal_whole_carrier_constant_bounds {u : ℝ} (hu : 1/2 ≤ u)
    {N K : ℕ} (hN : 32 ≤ N) (B : Finset ℕ)
    (hB : B ⊆ ZetaRieszParityPacket.coreBand u N K)
    (A : Finset ℕ) (y scale : ℝ) :
    let S := B.filter Squarefree
    let X := max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id
    let L := SquarefreeVaughanLogSource.length u N
    let P := ZetaRieszJointPrimeEnergy.ownerPrimes S
    let rho := SquarefreeCounting.density ∅
    let w := fun a p => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows S) L y scale N a p
    let q := fun a p => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N a p
    let J := scale*(∑ n ∈ S, ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    let E := 6*countingConstant*exp (-(N : ℝ)/128)*
      (∑ p ∈ P, (2+max 0 (L-log p))*max 0 (L-log p)*
        (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k p-q (k+1) p|))
    (∑ p ∈ P, (rho*(∑ a ∈ Finset.Icc 1 X, w a p*VaughanLogAverage.riesz L a)-
      7*((p : ℝ)+1)/(p : ℝ)*|∑ a ∈ Finset.Icc 1 X, w a p|))-E ≤ rho*J ∧
    rho*J ≤ (∑ p ∈ P, (rho*(∑ a ∈ Finset.Icc 1 X, w a p*VaughanLogAverage.riesz L a)+
      7*((p : ℝ)+1)/(p : ℝ)*|∑ a ∈ Finset.Icc 1 X, w a p|))+E := by
  dsimp only
  have hc := literal_whole_carrier_estimate hu hN B hB A y scale
  have hP : ∀ p ∈ ZetaRieszJointPrimeEnergy.ownerPrimes (B.filter Squarefree),
      p.Prime := by
    intro p hp
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hp
    have hn' := Finset.mem_filter.mp hn
    exact (ZetaRieszJointPrimeEnergy.owner_data hn'.2
      (ZetaRieszJointPrimeEnergy.core_count (hB hn'.1))).1
  have hm := owner_main_constant_bounds _ hP (SquarefreeVaughanLogSource.length u N)
    (fun p => ∑ a ∈ Finset.Icc 1 (max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id),
      ZetaRieszJointPrimeEnergy.maskedWeight A
        (ZetaRieszJointPrimeEnergy.ownerRows (B.filter Squarefree))
        (SquarefreeVaughanLogSource.length u N) y scale N a p *
          VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N) a)
    (fun p => ∑ a ∈ Finset.Icc 1 (max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id),
      ZetaRieszJointPrimeEnergy.maskedWeight A
        (ZetaRieszJointPrimeEnergy.ownerRows (B.filter Squarefree))
        (SquarefreeVaughanLogSource.length u N) y scale N a p)
  dsimp only at hc hm
  have hclo := (abs_le.mp hc).1
  have hchi := (abs_le.mp hc).2
  constructor
  · linarith [hm.1]
  · linarith [hm.2]

private theorem hinge_increment_eq_min {s t : ℝ} (hst : s ≤ t) (x : ℝ) :
    max 0 (t-x)-max 0 (s-x) = min (t-s) (max 0 (t-x)) := by
  have h := ZetaRieszJoinedPhysical.hinge_difference_eq_neg_min
    (sub_nonneg.mpr hst) (t-x)
  rw [show t-x-(t-s)=s-x by ring] at h
  linarith only [h]

private theorem density_riesz_lipschitz_ordered {s t : ℝ} (hst : s ≤ t) :
    |densityRiesz t-densityRiesz s| ≤ SquarefreeCounting.density ∅*(t-s) := by
  let R := ⌊exp t⌋₊
  let f := fun d : ℕ => max 0 (t-log d)-max 0 (s-log d)
  have hsR : ⌊exp s⌋₊ ≤ R := Nat.floor_mono (exp_le_exp.mpr hst)
  have hend : f (R+1)=0 := by
    have hcut : exp t < (R+1 : ℕ) := by
      simpa only [R,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one (exp t)
    have hl : t < log (R+1 : ℕ) := by
      simpa only [log_exp] using log_lt_log (exp_pos t) hcut
    have ht : max 0 (t-log (R+1 : ℕ))=0 := max_eq_left (by linarith)
    have hlog : s-log (R+1 : ℕ) ≤ t-log (R+1 : ℕ) := by linarith
    have hs := (max_le_max_left 0 hlog).trans_eq ht
    have hs0 : max 0 (s-log (R+1 : ℕ))=0 := le_antisymm hs (le_max_left _ _)
    simp only [f,ht,hs0,sub_self]
  have hdelta d (hd : d ∈ Finset.Icc 1 R) : 0 ≤ f d-f (d+1) := by
    have hlog := log_le_log (show (0 : ℝ)<d by exact_mod_cast (Finset.mem_Icc.mp hd).1)
      (show (d : ℝ) ≤ (d+1 : ℕ) by exact_mod_cast Nat.le_succ d)
    simp only [f,hinge_increment_eq_min hst]
    exact sub_nonneg.mpr (min_le_min_left _ (max_le_max_left 0 (by linarith)))
  have he : densityRiesz t-densityRiesz s =
      ∑ d ∈ Finset.Icc 1 R, f d*coefficient d := by
    rw [densityRiesz_eq_hinge t le_rfl,densityRiesz_eq_hinge s hsR,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by dsimp [f,coefficient]; ring)
  have hp k : (∑ d ∈ Finset.Icc 1 k, coefficient d) =
      ZetaRieszCofactorDiscrepancy.densityPrefix k := rfl
  rw [he,ZetaRieszSignedCutoffEnergy.abel_profile R f coefficient hend]
  simp_rw [hp]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 R, |(f d-f (d+1))*
        ZetaRieszCofactorDiscrepancy.densityPrefix d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 R, (f d-f (d+1))*SquarefreeCounting.density ∅ := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul,abs_of_nonneg (hdelta d hd)]
      exact mul_le_mul_of_nonneg_left
        (ZetaRieszSignedDensityCancellation.densityPrefix_signed_bound d) (hdelta d hd)
    _ = (f 1)*SquarefreeCounting.density ∅ := by
      rw [← Finset.sum_mul,← Finset.Ico_add_one_right_eq_Icc]
      have ht : (∑ d ∈ Finset.Ico 1 (R+1), (f d-f (d+1)))=f 1 := by
        rw [show (fun d => f d-f (d+1))=(fun d => -(f (d+1)-f d)) by
          funext d; ring,Finset.sum_neg_distrib,Finset.sum_Ico_sub f (by omega),hend]
        ring
      rw [ht]
    _ ≤ _ := by
      have hf : f 1 ≤ t-s := by
        simp only [f,hinge_increment_eq_min hst]
        exact min_le_left _ _
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hf base_density_bounds.1

/-- The SAME signed density Riesz response is uniformly Lipschitz in
its cutoff. Its complete divisor parity is summed before its density
allowance is used. No height, count or phase hypothesis occurs here. -/
theorem densityRiesz_lipschitz (s t : ℝ) :
    |densityRiesz t-densityRiesz s| ≤ SquarefreeCounting.density ∅*|t-s| := by
  rcases le_total s t with hst|hts
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using density_riesz_lipschitz_ordered hst
  · calc
      _ = |densityRiesz s-densityRiesz t| := abs_sub_comm _ _
      _ ≤ SquarefreeCounting.density ∅*(s-t) := density_riesz_lipschitz_ordered hts
      _ = _ := by rw [abs_of_nonpos (sub_nonpos.mpr hts)]; ring

/-- Owner conditioning changes ONE common signed Riesz function by at
most7/p. This is a bound on the exact scalar difference, not a relative
error multiplied by the absolute carrier. -/
theorem owner_hinge_common_reference_error {p : ℕ} (hp : p.Prime) (c : ℝ) :
    |(((p : ℝ)+1)/(p : ℝ))*(∑ D ∈ Finset.Icc 1 ⌊exp c⌋₊,
      (max 0 (c-log D)-max 0 (c-log (D+1 : ℕ)))*roughDensityPrefix {p} D)-
        densityRiesz c| ≤ 7/(p : ℝ) := by
  rw [owner_profile_eq_excluded_riesz hp c,excluded_riesz_recurrence hp c,
    add_sub_cancel_left,abs_mul,abs_of_nonneg (by positivity : (0 : ℝ)≤((p : ℝ)+1)⁻¹)]
  calc
    _ ≤ ((p : ℝ)+1)⁻¹*(7*((p : ℝ)+1)/(p : ℝ)) :=
      mul_le_mul_of_nonneg_left (excluded_riesz_bound hp _) (by positivity)
    _ = _ := by field_simp

/-- Nearby owner primes have nearby exact scalar multipliers, uniformly
over every translated cutoff and ALL cofactor counts. This is the common
coefficient that lets opposite signed owner sums cancel before norms. -/
theorem owner_hinge_nearby_bound {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (L : ℝ) :
    |(((p : ℝ)+1)/(p : ℝ))*(∑ D ∈ Finset.Icc 1 ⌊exp (L-log p)⌋₊,
      (max 0 (L-log p-log D)-max 0 (L-log p-log (D+1 : ℕ)))*roughDensityPrefix {p} D)-
      (((q : ℝ)+1)/(q : ℝ))*(∑ D ∈ Finset.Icc 1 ⌊exp (L-log q)⌋₊,
      (max 0 (L-log q-log D)-max 0 (L-log q-log (D+1 : ℕ)))*roughDensityPrefix {q} D)| ≤
        SquarefreeCounting.density ∅*|log p-log q|+7/(p : ℝ)+7/(q : ℝ) := by
  have h := (abs_sub_le
    ((((p : ℝ)+1)/(p : ℝ))*(∑ D ∈ Finset.Icc 1 ⌊exp (L-log p)⌋₊,
      (max 0 (L-log p-log D)-max 0 (L-log p-log (D+1 : ℕ)))*roughDensityPrefix {p} D))
    (densityRiesz (L-log p))
    ((((q : ℝ)+1)/(q : ℝ))*(∑ D ∈ Finset.Icc 1 ⌊exp (L-log q)⌋₊,
      (max 0 (L-log q-log D)-max 0 (L-log q-log (D+1 : ℕ)))*roughDensityPrefix {q} D))).trans
      (add_le_add_right ((abs_sub_le (densityRiesz (L-log p)) (densityRiesz (L-log q)) _).trans
        (add_le_add (densityRiesz_lipschitz (L-log q) (L-log p))
          (by simpa only [abs_sub_comm] using owner_hinge_common_reference_error hq (L-log q)))) _)
  have he : |(L-log p)-(L-log q)|=|log p-log q| := by
    rw [show (L-log p)-(L-log q)=-(log p-log q) by ring,abs_neg]
  rw [he] at h
  have hh := owner_hinge_common_reference_error hp (L-log p)
  linarith only [h,hh]

private theorem endpoint_abel (X : ℕ) (F z : ℕ → ℝ) :
    (∑ p ∈ Finset.Icc 1 X, F p*z p) =
      F X*(∑ p ∈ Finset.Icc 1 X, z p)+
        ∑ k ∈ Finset.Ico 1 X, (F k-F (k+1))*(∑ p ∈ Finset.Icc 1 k, z p) := by
  induction X with
  | zero => simp
  | succ X ih =>
    by_cases hX : X=0
    · subst X; simp
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ X+1),ih,
      Finset.sum_Icc_succ_top (by omega : 1 ≤ X+1),
      Finset.sum_Ico_succ_top (by omega : 1 ≤ X)]
    ring

private theorem masked_prefix (P : Finset ℕ) (V : ℕ → ℝ) (k : ℕ)
    (hP : ∀ p ∈ P, 0 < p) :
    (∑ p ∈ Finset.Icc 1 k, if p ∈ P then V p else 0) =
      ∑ p ∈ P.filter (fun p => p ≤ k), V p := by
  rw [← Finset.sum_filter]
  congr 1
  ext p
  simp only [Finset.mem_filter,Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_,hp⟩,hmem⟩
    exact ⟨hmem,hp⟩
  · rintro ⟨hmem,hp⟩
    exact ⟨⟨hP p hmem,hp⟩,hmem⟩

/-- Keep the common endpoint moment SIGNED and bound only its centered
owner variation. Every cofactor count stays inside the cumulative sums.
The source-carrying endpoint is not discarded or norm-paid. -/
theorem owner_prefix_centered_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (X : ℕ) (hPX : P ⊆ Finset.Icc 1 X) (L : ℝ) (V : ℕ → ℝ) :
    |∑ p ∈ P, (((p : ℝ)+1)/(p : ℝ))*
      (∑ D ∈ Finset.Icc 1 ⌊exp (L-log p)⌋₊,
        (max 0 (L-log p-log D)-max 0 (L-log p-log (D+1 : ℕ)))*roughDensityPrefix {p} D)*V p-
          densityRiesz (L-log X)*(∑ p ∈ P,V p)| ≤
      SquarefreeCounting.density ∅*(∑ k ∈ Finset.Ico 1 X,
          (log (k+1 : ℕ)-log k)*|∑ p ∈ P.filter (fun p => p ≤ k),V p|)+
        7*(∑ p ∈ P, |V p|/(p : ℝ)) := by
  let F := fun p : ℕ => densityRiesz (L-log p)
  let z := fun p : ℕ => if p ∈ P then V p else 0
  have hpr : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).pos
  have hsum : (∑ p ∈ Finset.Icc 1 X, z p) = ∑ p ∈ P,V p := by
    rw [masked_prefix P V X hpr]
    congr 1
    exact Finset.filter_eq_self.mpr (fun p hp => (Finset.mem_Icc.mp (hPX hp)).2)
  have hmain : (∑ p ∈ P,F p*V p) =
      F X*(∑ p ∈ P,V p)+∑ k ∈ Finset.Ico 1 X,
        (F k-F (k+1))*(∑ p ∈ P.filter (fun p => p ≤ k),V p) := by
    have he : (∑ p ∈ Finset.Icc 1 X,F p*z p) = ∑ p ∈ P,F p*V p := by
      simp only [z,mul_ite,mul_zero,← Finset.sum_filter]
      congr 1
      ext p
      simp only [Finset.mem_filter,Finset.mem_Icc]
      exact ⟨fun h => h.2,fun h => ⟨Finset.mem_Icc.mp (hPX h),h⟩⟩
    rw [← he,endpoint_abel,hsum]
    simp_rw [show z=(fun p => if p ∈ P then V p else 0) from rfl,
      masked_prefix P V _ hpr]
  have hstep k (hk : k ∈ Finset.Ico 1 X) :
      |F k-F (k+1)| ≤ SquarefreeCounting.density ∅*(log (k+1 : ℕ)-log k) := by
    have hl := log_le_log (show (0 : ℝ)<k by exact_mod_cast (Finset.mem_Ico.mp hk).1)
      (show (k : ℝ) ≤ (k+1 : ℕ) by exact_mod_cast Nat.le_succ k)
    have h := densityRiesz_lipschitz (L-log (k+1 : ℕ)) (L-log k)
    simpa only [F,show (L-log k)-(L-log (k+1 : ℕ))=log (k+1 : ℕ)-log k by ring,
      abs_of_nonneg (sub_nonneg.mpr hl)] using h
  have hm : |(∑ p ∈ P,F p*V p)-F X*(∑ p ∈ P,V p)| ≤
      SquarefreeCounting.density ∅*(∑ k ∈ Finset.Ico 1 X,
        (log (k+1 : ℕ)-log k)*|∑ p ∈ P.filter (fun p => p ≤ k),V p|) := by
    rw [hmain,add_sub_cancel_left]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [abs_mul]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hstep k hk) (abs_nonneg _)
  have he : |∑ p ∈ P,
      ((((p : ℝ)+1)/(p : ℝ))*(∑ D ∈ Finset.Icc 1 ⌊exp (L-log p)⌋₊,
        (max 0 (L-log p-log D)-max 0 (L-log p-log (D+1 : ℕ)))*roughDensityPrefix {p} D)-
          F p)*V p| ≤ 7*(∑ p ∈ P, |V p|/(p : ℝ)) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (owner_hinge_common_reference_error (hP p hp) _)
      (abs_nonneg _)).trans_eq (by ring)
  have hid : (∑ p ∈ P, (((p : ℝ)+1)/(p : ℝ))*
      (∑ D ∈ Finset.Icc 1 ⌊exp (L-log p)⌋₊,
        (max 0 (L-log p-log D)-max 0 (L-log p-log (D+1 : ℕ)))*roughDensityPrefix {p} D)*V p) =
      (∑ p ∈ P,F p*V p)+∑ p ∈ P,
        ((((p : ℝ)+1)/(p : ℝ))*(∑ D ∈ Finset.Icc 1 ⌊exp (L-log p)⌋₊,
          (max 0 (L-log p-log D)-max 0 (L-log p-log (D+1 : ℕ)))*roughDensityPrefix {p} D)-
            F p)*V p := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [hid,show (∑ p ∈ P,F p*V p)+
    (∑ p ∈ P, ((((p : ℝ)+1)/(p : ℝ))*(∑ D ∈ Finset.Icc 1 ⌊exp (L-log p)⌋₊,
      (max 0 (L-log p-log D)-max 0 (L-log p-log (D+1 : ℕ)))*roughDensityPrefix {p} D)-F p)*V p)-
        densityRiesz (L-log X)*(∑ p ∈ P,V p) =
    ((∑ p ∈ P,F p*V p)-F X*(∑ p ∈ P,V p))+
      (∑ p ∈ P, ((((p : ℝ)+1)/(p : ℝ))*(∑ D ∈ Finset.Icc 1 ⌊exp (L-log p)⌋₊,
        (max 0 (L-log p-log D)-max 0 (L-log p-log (D+1 : ℕ)))*roughDensityPrefix {p} D)-F p)*V p) by
    dsimp only [F]; ring]
  exact (abs_add_le _ _).trans (add_le_add hm he)

/-- Every owner and cofactor count is joined before the common scalar
is charged. The interior cost uses signed cumulative owner sums; an
opposite pair enters through its small prefix, not two separate norms.
The only owner-conditioning price left is weighted by1/p. -/
theorem owner_prefix_signed_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (X : ℕ) (hPX : P ⊆ Finset.Icc 1 X) (L : ℝ) (V : ℕ → ℝ) :
    |∑ p ∈ P, (((p : ℝ)+1)/(p : ℝ))*
      (∑ D ∈ Finset.Icc 1 ⌊exp (L-log p)⌋₊,
        (max 0 (L-log p-log D)-max 0 (L-log p-log (D+1 : ℕ)))*roughDensityPrefix {p} D)*V p| ≤
      7*|∑ p ∈ P,V p|+
        SquarefreeCounting.density ∅*(∑ k ∈ Finset.Ico 1 X,
          (log (k+1 : ℕ)-log k)*|∑ p ∈ P.filter (fun p => p ≤ k),V p|)+
        7*(∑ p ∈ P, |V p|/(p : ℝ)) := by
  let M := ∑ p ∈ P, (((p : ℝ)+1)/(p : ℝ))*
    (∑ D ∈ Finset.Icc 1 ⌊exp (L-log p)⌋₊,
      (max 0 (L-log p-log D)-max 0 (L-log p-log (D+1 : ℕ)))*roughDensityPrefix {p} D)*V p
  change |M| ≤ _
  have hc := owner_prefix_centered_error P hP X hPX L V
  have ht : |densityRiesz (L-log X)*(∑ p ∈ P,V p)| ≤ 7*|∑ p ∈ P,V p| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (densityRiesz_bound _) (abs_nonneg _)
  calc
    _ = |(M-densityRiesz (L-log X)*(∑ p ∈ P,V p))+
        densityRiesz (L-log X)*(∑ p ∈ P,V p)| := by congr 1; ring
    _ ≤ |M-densityRiesz (L-log X)*(∑ p ∈ P,V p)|+
        |densityRiesz (L-log X)*(∑ p ∈ P,V p)| := abs_add_le _ _
    _ ≤ _ := by dsimp only [M] at *; linarith only [hc,ht]

/-- Both signed bounds for the complete owner main, with cancellation
among owners retained in ONE cumulative profile. Neither cofactor count
classes nor owner primes are given separate constant allowances. -/
theorem owner_main_prefix_bounds (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (X : ℕ) (hPX : P ⊆ Finset.Icc 1 X) (L : ℝ) (U V : ℕ → ℝ) :
    let rho := SquarefreeCounting.density ∅
    let C := 7*|∑ p ∈ P,V p|+rho*(∑ k ∈ Finset.Ico 1 X,
      (log (k+1 : ℕ)-log k)*|∑ p ∈ P.filter (fun p => p ≤ k),V p|)+
        7*(∑ p ∈ P,|V p|/(p : ℝ))
    let M := ∑ p ∈ P, (rho*U p - (((p : ℝ)+1)/(p : ℝ))*
      (∑ D ∈ Finset.Icc 1 ⌊exp (L-log p)⌋₊,
        (max 0 (L-log p-log D)-max 0 (L-log p-log (D+1 : ℕ)))*
          roughDensityPrefix {p} D)*V p)
    rho*(∑ p ∈ P,U p)-C ≤ M ∧ M ≤ rho*(∑ p ∈ P,U p)+C := by
  dsimp only
  have h := abs_le.mp (owner_prefix_signed_bound P hP X hPX L V)
  rw [Finset.sum_sub_distrib,← Finset.mul_sum]
  constructor <;> linarith only [h.1,h.2]

/-- The new joint owner-prefix allowance applies to the ORIGINAL
masked carrier on every coreBand subset. All cofactor counts and phases
remain inside V before any norm; its aggregate first Riesz moment stays
signed. The literal comparison variation is retained and unpaid. -/
theorem literal_whole_carrier_prefix_bounds {u : ℝ} (hu : 1/2 ≤ u)
    {N K : ℕ} (hN : 32 ≤ N) (B : Finset ℕ)
    (hB : B ⊆ ZetaRieszParityPacket.coreBand u N K)
    (A : Finset ℕ) (y scale : ℝ) :
    let S := B.filter Squarefree
    let X := max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id
    let L := SquarefreeVaughanLogSource.length u N
    let P := ZetaRieszJointPrimeEnergy.ownerPrimes S
    let M := max 1 (P.sup id)
    let rho := SquarefreeCounting.density ∅
    let w := fun a p => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows S) L y scale N a p
    let q := fun a p => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N a p
    let V := fun p => ∑ a ∈ Finset.Icc 1 X,w a p
    let C := 7*|∑ p ∈ P,V p|+rho*(∑ k ∈ Finset.Ico 1 M,
      (log (k+1 : ℕ)-log k)*|∑ p ∈ P.filter (fun p => p ≤ k),V p|)+
        7*(∑ p ∈ P,|V p|/(p : ℝ))
    let J := scale*(∑ n ∈ S, ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    let E := 6*countingConstant*exp (-(N : ℝ)/128)*
      (∑ p ∈ P, (2+max 0 (L-log p))*max 0 (L-log p)*
        (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k p-q (k+1) p|))
    rho*(∑ p ∈ P,∑ a ∈ Finset.Icc 1 X,w a p*VaughanLogAverage.riesz L a)-C-E ≤ rho*J ∧
      rho*J ≤ rho*(∑ p ∈ P,∑ a ∈ Finset.Icc 1 X,w a p*VaughanLogAverage.riesz L a)+C+E := by
  dsimp only
  have hc := literal_whole_carrier_estimate hu hN B hB A y scale
  have hP : ∀ p ∈ ZetaRieszJointPrimeEnergy.ownerPrimes (B.filter Squarefree),
      p.Prime := by
    intro p hp
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hp
    have hn' := Finset.mem_filter.mp hn
    exact (ZetaRieszJointPrimeEnergy.owner_data hn'.2
      (ZetaRieszJointPrimeEnergy.core_count (hB hn'.1))).1
  have hPX : ZetaRieszJointPrimeEnergy.ownerPrimes (B.filter Squarefree) ⊆
      Finset.Icc 1 (max 1 ((ZetaRieszJointPrimeEnergy.ownerPrimes (B.filter Squarefree)).sup id)) := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(hP p hp).pos,
      (Finset.le_sup (f := id) hp).trans (le_max_right _ _)⟩
  have hm := owner_main_prefix_bounds _ hP _ hPX (SquarefreeVaughanLogSource.length u N)
    (fun p => ∑ a ∈ Finset.Icc 1 (max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id),
      ZetaRieszJointPrimeEnergy.maskedWeight A
        (ZetaRieszJointPrimeEnergy.ownerRows (B.filter Squarefree))
        (SquarefreeVaughanLogSource.length u N) y scale N a p *
          VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N) a)
    (fun p => ∑ a ∈ Finset.Icc 1 (max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id),
      ZetaRieszJointPrimeEnergy.maskedWeight A
        (ZetaRieszJointPrimeEnergy.ownerRows (B.filter Squarefree))
        (SquarefreeVaughanLogSource.length u N) y scale N a p)
  dsimp only at hc hm
  have hlo := (abs_le.mp hc).1
  have hhi := (abs_le.mp hc).2
  constructor <;> linarith only [hm.1,hm.2,hlo,hhi]

/-- Retain the common owner resonance JOINTLY with the first cofactor
moment in the ORIGINAL carrier. Only the centered cumulative-owner
variation and7/p correction are norm-priced. The explicit literal
comparison error remains unpaid; no floor premise is hidden here. -/
theorem literal_whole_carrier_centered_bounds {u : ℝ} (hu : 1/2 ≤ u)
    {N K : ℕ} (hN : 32 ≤ N) (B : Finset ℕ)
    (hB : B ⊆ ZetaRieszParityPacket.coreBand u N K)
    (A : Finset ℕ) (y scale : ℝ) :
    let S := B.filter Squarefree
    let X := max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id
    let L := SquarefreeVaughanLogSource.length u N
    let P := ZetaRieszJointPrimeEnergy.ownerPrimes S
    let M := max 1 (P.sup id)
    let rho := SquarefreeCounting.density ∅
    let w := fun a p => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows S) L y scale N a p
    let q := fun a p => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N a p
    let V := fun p => ∑ a ∈ Finset.Icc 1 X,w a p
    let T := rho*(∑ p ∈ P,∑ a ∈ Finset.Icc 1 X,w a p*VaughanLogAverage.riesz L a)-
      densityRiesz (L-log M)*(∑ p ∈ P,V p)
    let C := rho*(∑ k ∈ Finset.Ico 1 M,
      (log (k+1 : ℕ)-log k)*|∑ p ∈ P.filter (fun p => p ≤ k),V p|)+
        7*(∑ p ∈ P,|V p|/(p : ℝ))
    let J := scale*(∑ n ∈ S, ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    let E := 6*countingConstant*exp (-(N : ℝ)/128)*
      (∑ p ∈ P, (2+max 0 (L-log p))*max 0 (L-log p)*
        (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k p-q (k+1) p|))
    T-C-E ≤ rho*J ∧ rho*J ≤ T+C+E := by
  dsimp only
  have hc := literal_whole_carrier_estimate hu hN B hB A y scale
  have hP : ∀ p ∈ ZetaRieszJointPrimeEnergy.ownerPrimes (B.filter Squarefree),
      p.Prime := by
    intro p hp
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hp
    have hn' := Finset.mem_filter.mp hn
    exact (ZetaRieszJointPrimeEnergy.owner_data hn'.2
      (ZetaRieszJointPrimeEnergy.core_count (hB hn'.1))).1
  have hPX : ZetaRieszJointPrimeEnergy.ownerPrimes (B.filter Squarefree) ⊆
      Finset.Icc 1 (max 1 ((ZetaRieszJointPrimeEnergy.ownerPrimes (B.filter Squarefree)).sup id)) := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(hP p hp).pos,
      (Finset.le_sup (f := id) hp).trans (le_max_right _ _)⟩
  have hm := owner_prefix_centered_error _ hP _ hPX (SquarefreeVaughanLogSource.length u N)
    (fun p => ∑ a ∈ Finset.Icc 1 (max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id),
      ZetaRieszJointPrimeEnergy.maskedWeight A
        (ZetaRieszJointPrimeEnergy.ownerRows (B.filter Squarefree))
        (SquarefreeVaughanLogSource.length u N) y scale N a p)
  dsimp only at hc hm
  rw [Finset.sum_sub_distrib,← Finset.mul_sum] at hc
  have hclo := (abs_le.mp hc).1
  have hchi := (abs_le.mp hc).2
  have hmlo := (abs_le.mp hm).1
  have hmhi := (abs_le.mp hm).2
  constructor <;> linarith only [hclo,hchi,hmlo,hmhi]

open ZetaRieszParityPacket ZetaRieszJoinedPopulationFloor
open ZetaRieszFewBinCoverFloor ZetaRieszSevenCountTail ZetaRieszPrimeEndpoint

/-- The existing published unpaid owner population, with its original
paid sets and tail unchanged. This is a support alias, not a new carrier. -/
def remainingOwnerBand (u : ℝ) (N K : ℕ) : Finset ℕ :=
  (coreBand u N K\
    ((((coreBand u N K).filter (fun n : ℕ =>
      3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∪ dense56Band u N K) ∪
      bin56Band u N K) ∪ wholeTail (coreBand u N K) N 0))\
        ZetaRieszCoreOwnerPayment.largeOwnerSector u N K

/-- The exact unpaid count/bin/owner tests, without putting squarefreeness
inside the comparison weight. Squarefreeness belongs to the measure. -/
def remainingOwnerGeometry (N n : ℕ) : Prop :=
  56 ≤ n.primeFactors.card ∧
    n.primeFactors.card < ZetaRieszLogCountBudget.countThreshold N ∧
    (n.primeFactors.card : ℝ) < 5*log ((N : ℝ)+1)+2 ∧
    ⌊log ((N : ℝ)+1)/16⌋₊ < (cofactorBins N (n/largestPrime n)).card ∧
    log (largestPrime n) < ZetaRieszCoreOwnerPayment.ownerThreshold*log n

/-- A raw comparison extension of the SAME squarefree unpaid population.
Nonsquarefree rows in paid count/bin ranges are excluded as well. No
squarefree carrier atom is deleted, and no prime support is completed. -/
def comparisonOwnerBand (u : ℝ) (N K : ℕ) : Finset ℕ :=
  (coreBand u N K).filter (remainingOwnerGeometry N)

/-- Every raw comparison label remains on the original unpaid support.
The new extension does not add labels from a funded or paid population. -/
theorem comparisonOwnerBand_subset (u : ℝ) (N K : ℕ) :
    comparisonOwnerBand u N K ⊆ remainingOwnerBand u N K := by
  intro n hn
  obtain ⟨hnS,h56,hthreshold,hupper,hbins,howner⟩ := Finset.mem_filter.mp hn
  have hnotD : n ∉ (coreBand u N K).filter (fun m : ℕ =>
      3 ≤ m.primeFactors.card ∧ m.primeFactors.card ≤ 55) := by
    intro h
    have := (Finset.mem_filter.mp h).2.2
    omega
  have hnotDense : n ∉ dense56Band u N K := by
    intro h
    have hd := (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2.2.2.1
    linarith only [hd,hupper]
  have hnotBin : n ∉ bin56Band u N K := by
    intro h
    have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2.2.2.1.2
    exact (not_le.mpr hbins) hb
  have hnotTail : n ∉ wholeTail (coreBand u N K) N 0 := by
    rw [ZetaRieszLowCountRefund.wholeTail_zero_eq]
    intro h
    have ht := (Finset.mem_filter.mp h).2.2
    omega
  have hnotOwner : n ∉ ZetaRieszCoreOwnerPayment.largeOwnerSector u N K := by
    intro h
    exact (not_le.mpr howner) (Finset.mem_filter.mp h).2
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_sdiff.mpr ⟨hnS,?_⟩,hnotOwner⟩
  intro h
  rcases Finset.mem_union.mp h with h|h
  · rcases Finset.mem_union.mp h with h|h
    · exact (Finset.mem_union.mp h).elim hnotD hnotDense
    · exact hnotBin h
  · exact hnotTail h

/-- ALL squarefree unpaid labels obey the comparison tests, even when
their residual coefficient happens to vanish. No zero hypothesis enters. -/
theorem remainingOwnerBand_squarefree_geometry {u : ℝ} {N K n : ℕ}
    (hn : n ∈ remainingOwnerBand u N K) (hs : Squarefree n) :
    remainingOwnerGeometry N n := by
  obtain ⟨hnH,hnOwner⟩ := Finset.mem_sdiff.mp hn
  obtain ⟨hnS,hnot⟩ := Finset.mem_sdiff.mp hnH
  have hnotD : n ∉ (coreBand u N K).filter (fun m : ℕ =>
      3 ≤ m.primeFactors.card ∧ m.primeFactors.card ≤ 55) :=
    fun h => hnot (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
  have h56 : 56 ≤ n.primeFactors.card := by
    have hc := ZetaRieszJointPrimeEnergy.core_count hnS
    by_contra h
    exact hnotD (Finset.mem_filter.mpr ⟨hnS,hc,by omega⟩)
  have hthreshold : n.primeFactors.card < ZetaRieszLogCountBudget.countThreshold N := by
    by_contra h
    apply hnot
    apply Finset.mem_union_right
    rw [ZetaRieszLowCountRefund.wholeTail_zero_eq]
    exact Finset.mem_filter.mpr ⟨hnS,hs,le_of_not_gt h⟩
  have hupper : (n.primeFactors.card : ℝ) < 5*log ((N : ℝ)+1)+2 := by
    by_contra h
    apply hnot
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨hnS,hs,by omega,le_of_not_gt h,hthreshold⟩,h56⟩)))
  have hbins : ⌊log ((N : ℝ)+1)/16⌋₊ < (cofactorBins N (n/largestPrime n)).card := by
    by_contra h
    apply hnot
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨hnS,hs,by omega,⟨hupper,le_of_not_gt h⟩,hthreshold⟩,h56⟩))
  have howner : log (largestPrime n) < ZetaRieszCoreOwnerPayment.ownerThreshold*log n := by
    by_contra h
    exact hnOwner (Finset.mem_filter.mpr ⟨hnS,le_of_not_gt h⟩)
  exact ⟨h56,hthreshold,hupper,hbins,howner⟩

/-- The original and cleaned comparison extensions have EXACTLY the same
squarefree rows. In particular, every signed cofactor moment is preserved. -/
theorem comparisonOwnerBand_squarefree_eq (u : ℝ) (N K : ℕ) :
    (comparisonOwnerBand u N K).filter Squarefree =
      (remainingOwnerBand u N K).filter Squarefree := by
  ext n
  constructor
  · intro hn
    obtain ⟨hn,hs⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨comparisonOwnerBand_subset u N K hn,hs⟩
  · intro hn
    obtain ⟨hn,hs⟩ := Finset.mem_filter.mp hn
    have hnS : n ∈ coreBand u N K := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hn).1).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨hnS,remainingOwnerBand_squarefree_geometry hn hs⟩,hs⟩

/-- The carrier is unchanged EXACTLY by cleaning the raw comparison
extension. This removes zero nonsquarefree rows, not an unpaid population. -/
theorem remainingOwnerBand_carrier_eq (u y L : ℝ) (N K : ℕ) (A : Finset ℕ) :
    (∑ n ∈ remainingOwnerBand u N K,
      ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n) =
      ∑ n ∈ comparisonOwnerBand u N K,
        ZetaRieszJointAllocation.residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n := by
  symm
  apply Finset.sum_subset (comparisonOwnerBand_subset u N K)
  intro n hn hout
  have hs : ¬Squarefree n := by
    intro hs
    exact hout (Finset.mem_filter.mpr
      ⟨(Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hn).1).1,
        remainingOwnerBand_squarefree_geometry hn hs⟩)
  simp [ZetaRieszJointAllocation.residualCoefficient,
    SquarefreeVaughanLogSource.coefficient,hs]

/-- Every paid count/bin geometry is zero in the new RAW comparison
weight, including nonsquarefree labels. This is before its variation is
taken; no phase or positive cofactor amplitude is substituted. -/
theorem comparisonOwnerWeight_zero_of_not_geometry (u L y scale : ℝ)
    (N K a p : ℕ) (A : Finset ℕ) (hn : ¬remainingOwnerGeometry N (p*a)) :
    ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows (comparisonOwnerBand u N K))
        L y scale N a p = 0 := by
  unfold ZetaRieszJointPrimeEnergy.maskedWeight
  apply if_neg
  intro hp
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hm,he⟩ := Finset.mem_filter.mp hm
  have hmS := (Finset.mem_filter.mp hm).1
  have hpf := ZetaRieszOwnedCells.largestPrime_mem_of_two (m := m)
    (by have := ZetaRieszJointPrimeEnergy.core_count hmS; omega)
  have heq : largestPrime m*a=m := by
    rw [← he]
    exact Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hpf)
  apply hn
  rw [heq]
  exact (Finset.mem_filter.mp hm).2

/-- The literal comparison variation has NO charge on an edge whose
two endpoints are outside the unpaid geometry. Counts, bins and owners
are joined in this single active-edge test before the error is summed. -/
theorem comparisonOwnerVariation_eq_active (u L y scale : ℝ)
    (N K X p : ℕ) (A : Finset ℕ) :
    let q := fun a => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows (comparisonOwnerBand u N K))
        L y scale N a p
    (∑ k ∈ Finset.Icc 1 X, (k : ℝ)*|q k-q (k+1)|) =
      ∑ k ∈ (Finset.Icc 1 X).filter (fun k =>
        remainingOwnerGeometry N (p*k) ∨ remainingOwnerGeometry N (p*(k+1))),
          (k : ℝ)*|q k-q (k+1)| := by
  dsimp only
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro k hk hout
  have hbad : ¬(remainingOwnerGeometry N (p*k) ∨
      remainingOwnerGeometry N (p*(k+1))) :=
    fun h => hout (Finset.mem_filter.mpr ⟨hk,h⟩)
  rw [comparisonOwnerWeight_zero_of_not_geometry u L y scale N K k p A
      (fun h => hbad (Or.inl h)),
    comparisonOwnerWeight_zero_of_not_geometry u L y scale N K (k+1) p A
      (fun h => hbad (Or.inr h))]
  simp

/-- Both signed bounds for the SAME original unpaid carrier, with the
comparison variation restricted to its genuine count/bin/owner geometry.
The common resonance stays signed, and no comparison decay is assumed. -/
theorem literal_remaining_centered_bounds {u : ℝ} (hu : 1/2 ≤ u)
    {N K : ℕ} (hN : 32 ≤ N) (A : Finset ℕ) (y scale : ℝ) :
    let B := remainingOwnerBand u N K
    let Q := comparisonOwnerBand u N K
    let S := B.filter Squarefree
    let X := max 1 (ZetaRieszJointPrimeEnergy.cofactors Q).sup id
    let L := SquarefreeVaughanLogSource.length u N
    let P := ZetaRieszJointPrimeEnergy.ownerPrimes S
    let M := max 1 (P.sup id)
    let rho := SquarefreeCounting.density ∅
    let w := fun a p => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows S) L y scale N a p
    let q := fun a p => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows Q) L y scale N a p
    let V := fun p => ∑ a ∈ Finset.Icc 1 X,w a p
    let T := rho*(∑ p ∈ P,∑ a ∈ Finset.Icc 1 X,w a p*VaughanLogAverage.riesz L a)-
      densityRiesz (L-log M)*(∑ p ∈ P,V p)
    let C := rho*(∑ k ∈ Finset.Ico 1 M,
      (log (k+1 : ℕ)-log k)*|∑ p ∈ P.filter (fun p => p ≤ k),V p|)+
        7*(∑ p ∈ P,|V p|/(p : ℝ))
    let J := scale*(∑ n ∈ B, ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    let E := 6*countingConstant*exp (-(N : ℝ)/128)*
      (∑ p ∈ P, (2+max 0 (L-log p))*max 0 (L-log p)*
        (∑ k ∈ (Finset.Icc 1 X).filter (fun k =>
          remainingOwnerGeometry N (p*k) ∨ remainingOwnerGeometry N (p*(k+1))),
            (k : ℝ)*|q k p-q (k+1) p|))
    T-C-E ≤ rho*J ∧ rho*J ≤ T+C+E := by
  dsimp only
  have h := literal_whole_carrier_centered_bounds hu hN (comparisonOwnerBand u N K)
    (Finset.filter_subset _ _) A y scale
  have hsf := comparisonOwnerBand_squarefree_eq u N K
  have he : (∑ n ∈ (comparisonOwnerBand u N K).filter Squarefree,
      ZetaRieszJointAllocation.residualCoefficient A (SquarefreeVaughanLogSource.length u N) N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n) =
      ∑ n ∈ remainingOwnerBand u N K,
        ZetaRieszJointAllocation.residualCoefficient A (SquarefreeVaughanLogSource.length u N) N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n := by
    rw [remainingOwnerBand_carrier_eq u y (SquarefreeVaughanLogSource.length u N) N K A]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hnQ hn
    have hs : ¬Squarefree n := fun hs => hn (Finset.mem_filter.mpr ⟨hnQ,hs⟩)
    simp [ZetaRieszJointAllocation.residualCoefficient,
      SquarefreeVaughanLogSource.coefficient,hs]
  dsimp only at h
  rw [he,hsf] at h
  simp_rw [comparisonOwnerVariation_eq_active] at h
  exact h

open Filter Topology ZetaRieszAnnulusJoint ZetaRieszPrimeCountFrequency
open ZetaRieszRadialCompensation ZetaRieszBandCompensation
open ZetaRieszRejoinedPopulationFloor
open ZetaRieszLowCountRefund (tailCost)

/-- Spend the cleaned comparison bound in the EXISTING whole-floor
ledger, without an extra error, funding credit or arithmetic hypothesis.
The displayed centered main, active-edge cost and funding debit are still
unpaid; this is not the numerical -79/1000 floor. -/
theorem eventually_joined_centered_owner_floor {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) :
    ∃ h c κ : ℝ, 0 < h ∧ h ≤ 1/20 ∧ 0 < c ∧ 0 < κ ∧
      ∀ ε : ℝ, 0 < ε → ∃ err : ℕ → ℝ,
      (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ v M ∧ v M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let K := dyadicPrimeCount j
        let A := intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N
        let S₀ := coreBand u N K
        let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Paid := (S₀.filter (fun n : ℕ =>
          3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∪ dense56Band u N K) ∪
            bin56Band u N K
        let Ts := radialTail S₀ N 0
        let Ys := radialSupply N h v
        let S := (remainingOwnerBand u N K).filter Squarefree
        let Q := comparisonOwnerBand u N K
        let X := max 1 (ZetaRieszJointPrimeEnergy.cofactors Q).sup id
        let P := ZetaRieszJointPrimeEnergy.ownerPrimes S
        let M := max 1 (P.sup id)
        let rho := SquarefreeCounting.density ∅
        let w := fun a p => ZetaRieszJointPrimeEnergy.maskedWeight A
          (ZetaRieszJointPrimeEnergy.ownerRows S) L y (u^(N+1)) N a p
        let q := fun a p => ZetaRieszJointPrimeEnergy.maskedWeight A
          (ZetaRieszJointPrimeEnergy.ownerRows Q) L y (u^(N+1)) N a p
        let V := fun p => ∑ a ∈ Finset.Icc 1 X,w a p
        let T := rho*(∑ p ∈ P,∑ a ∈ Finset.Icc 1 X,w a p*VaughanLogAverage.riesz L a)-
          densityRiesz (L-log M)*(∑ p ∈ P,V p)
        let C := rho*(∑ k ∈ Finset.Ico 1 M,
          (log (k+1 : ℕ)-log k)*|∑ p ∈ P.filter (fun p => p ≤ k),V p|)+
            7*(∑ p ∈ P,|V p|/(p : ℝ))
        let E := 6*countingConstant*exp (-(N : ℝ)/128)*
          (∑ p ∈ P, (2+max 0 (L-log p))*max 0 (L-log p)*
            (∑ k ∈ (Finset.Icc 1 X).filter (fun k =>
              remainingOwnerGeometry N (p*k) ∨ remainingOwnerGeometry N (p*(k+1))),
                (k : ℝ)*|q k p-q (k+1) p|))
        0 < (∑ n ∈ Ys,f n).re ∧
          (T-C-E)/rho+u^(N+1)*(max (∑ n ∈ Paid,f n).re 0+
            max (∑ n ∈ Ts,f n).re 0-
            (tailCost c N+ε+growingDebit κ N)*(∑ n ∈ Ys,f n).re)-err j ≤
              ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re := by
  obtain ⟨h,c,κ,hh,hhu,hc,hκ,hbase⟩ :=
    ZetaRieszCoreOwnerPayment.eventually_rejoined_floor_without_large_owners hu hU hy
  refine ⟨h,c,κ,hh,hhu,hc,hκ,?_⟩
  intro ε hε
  obtain ⟨err,he0,he,hfloor⟩ := hbase ε hε
  refine ⟨err,he0,he,?_⟩
  filter_upwards [hfloor,tendsto_dyadicMomentOrder.eventually
    (eventually_ge_atTop (32 : ℕ))] with j hj hj32
  obtain ⟨v,hv,hpos,hbound⟩ := hj
  refine ⟨v,hv,hpos,?_⟩
  have hcenter := literal_remaining_centered_bounds (K := dyadicPrimeCount j) hu.le hj32
    (intermediatePrimes u (dyadicMomentOrder j)) y (u^(dyadicMomentOrder j+1))
  dsimp only at hcenter hbound ⊢
  have hlow := (div_le_iff₀ squarefree_density_pos).mpr
    (hcenter.1.trans_eq (mul_comm _ _))
  simp only [remainingOwnerBand] at hlow ⊢
  nlinarith only [hlow,hbound]

private theorem periodic_local_variation (Q : ℕ) (hQ : 0 < Q)
    (w : ℕ → ℝ) (hzero : ∀ n, Q ∣ n → w n = 0) (n : ℕ) :
    |w n| ≤ ∑ j ∈ Finset.range Q, |w (n+j)-w (n+j+1)| := by
  obtain ⟨j,hj,hdiv⟩ : ∃ j < Q, Q ∣ n+j := by
    by_cases hn : n % Q=0
    · exact ⟨0,hQ,by simpa using Nat.dvd_iff_mod_eq_zero.mpr hn⟩
    · have hmod := Nat.mod_lt n hQ
      refine ⟨Q-n%Q,by omega,Nat.dvd_iff_mod_eq_zero.mpr ?_⟩
      rw [Nat.add_mod,show n%Q+(Q-n%Q)%Q=Q by
        rw [Nat.mod_eq_of_lt (by omega : Q-n%Q < Q)]; omega]
      exact Nat.mod_self Q
  have hz := hzero (n+j) hdiv
  have ht := Finset.abs_sum_le_sum_abs
    (s := Finset.range j) (fun i => w (n+i)-w (n+i+1))
  rw [show (∑ i ∈ Finset.range j, (w (n+i)-w (n+i+1)))=w n-w (n+j) by
    simpa only [Nat.add_zero,Nat.add_assoc] using
      (Finset.sum_range_sub' (fun i => w (n+i)) j),hz,sub_zero] at ht
  exact ht.trans (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono hj.le) (fun _ _ _ => abs_nonneg _))

private theorem periodic_weighted_variation (Q X : ℕ) (hQ : 0 < Q)
    (w : ℕ → ℝ) (hzero : ∀ n, Q ∣ n → w n = 0)
    (hout : ∀ n, X < n → w n = 0) :
    (∑ n ∈ Finset.Icc 1 X, (n : ℝ)*|w n|) ≤
      (Q : ℝ)*(∑ n ∈ Finset.Icc 1 X, (n : ℝ)*|w n-w (n+1)|) := by
  let v (n : ℕ) := (n : ℝ)*|w n-w (n+1)|
  have hv n : 0 ≤ v n := by dsimp [v]; positivity
  have hshift (j : ℕ) :
      (∑ n ∈ Finset.Icc 1 X, v (n+j)) ≤ ∑ n ∈ Finset.Icc 1 X, v n := by
    have he : (∑ n ∈ Finset.Icc 1 X, v (n+j)) =
        ∑ n ∈ (Finset.Icc 1 X).image (fun n => n+j), v n := by
      rw [Finset.sum_image]
      intro a _ b _ hab
      dsimp at hab
      omega
    rw [he]
    have hs : (Finset.Icc 1 X).image (fun n => n+j) ⊆ Finset.Icc 1 (X+j) := by
      rintro n hn
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hn
      have ha := Finset.mem_Icc.mp ha
      exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
    have hlarge : (∑ n ∈ Finset.Icc 1 (X+j), v n) = ∑ n ∈ Finset.Icc 1 X, v n := by
      symm
      apply Finset.sum_subset
      · intro n hn
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
          by have := (Finset.mem_Icc.mp hn).2; omega⟩
      · intro n hn hnot
        have hnX : X < n := by
          have := Finset.mem_Icc.mp hn
          simp only [Finset.mem_Icc,not_and] at hnot
          omega
        simp [v,hout n hnX,hout (n+1) (by omega)]
    exact (Finset.sum_le_sum_of_subset_of_nonneg hs (fun n _ _ => hv n)).trans_eq hlarge
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 X, ∑ j ∈ Finset.range Q, v (n+j) := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        _ ≤ (n : ℝ)*(∑ j ∈ Finset.range Q, |w (n+j)-w (n+j+1)|) :=
          mul_le_mul_of_nonneg_left (periodic_local_variation Q hQ w hzero n)
            (Nat.cast_nonneg _)
        _ ≤ _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_right n j)
            (abs_nonneg _)
    _ = ∑ j ∈ Finset.range Q, ∑ n ∈ Finset.Icc 1 X, v (n+j) := Finset.sum_comm
    _ ≤ ∑ _j ∈ Finset.range Q, ∑ n ∈ Finset.Icc 1 X, v n :=
      Finset.sum_le_sum (fun j _ => hshift j)
    _ = _ := by simp [v]

/-- Canonical ownership forces periodic zeros even in the RAW comparison
weight. No squarefree zero extension or completion is used: a cofactor
containing a prime larger than p cannot have p as its largest owner. -/
theorem raw_owner_weight_zero_larger_prime (B A : Finset ℕ)
    (hB : ∀ m ∈ B, 2 ≤ m.primeFactors.card) (L y scale : ℝ) (N p a : ℕ)
    {q : ℕ} (hq : q.Prime) (hqp : p < q) (hqa : q ∣ a) :
    ZetaRieszJointPrimeEnergy.maskedWeight A (ZetaRieszJointPrimeEnergy.ownerRows B)
      L y scale N a p = 0 := by
  unfold ZetaRieszJointPrimeEnergy.maskedWeight
  apply if_neg
  intro hp
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hm,he⟩ := Finset.mem_filter.mp hm
  have hpf := ZetaRieszOwnedCells.largestPrime_mem_of_two (hB m hm)
  have hm0 := (Nat.mem_primeFactors.mp hpf).2.2
  have hqm : q ∈ m.primeFactors := hq.mem_primeFactors
    (hqa.trans (by rw [← he]; exact Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hpf))) hm0
  have hne : m.primeFactors.Nonempty := ⟨q,hqm⟩
  have hle : q ≤ largestPrime m := by
    rw [largestPrime,dif_pos hne]
    exact Finset.le_max' _ _ hqm
  exact (not_lt_of_ge hle) hqp

private theorem raw_owner_weight_outside (B A : Finset ℕ) (L y scale : ℝ)
    (N p a : ℕ) (ha : max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id < a) :
    ZetaRieszJointPrimeEnergy.maskedWeight A (ZetaRieszJointPrimeEnergy.ownerRows B)
      L y scale N a p = 0 := by
  unfold ZetaRieszJointPrimeEnergy.maskedWeight
  apply if_neg
  intro hp
  obtain ⟨m,hm,_⟩ := Finset.mem_image.mp hp
  obtain ⟨hm,he⟩ := Finset.mem_filter.mp hm
  have hac : a ∈ ZetaRieszJointPrimeEnergy.cofactors B := Finset.mem_image.mpr ⟨m,hm,he⟩
  exact (not_le_of_gt ha) ((Finset.le_sup (f := id) hac).trans (le_max_right _ _))

/-- The SAME raw owner-column variation has a mandatory cost of at least
its weighted mass divided by2p. Bertrand supplies a forbidden prime in
(p,2p]. The full phase and every original mask stay inside the weight. -/
theorem raw_owner_variation_lower {p : ℕ} (hp : p.Prime) (B A : Finset ℕ)
    (hB : ∀ m ∈ B, 2 ≤ m.primeFactors.card) (L y scale : ℝ) (N : ℕ) :
    let X := max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id
    let w := fun a => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N a p
    (∑ a ∈ Finset.Icc 1 X, (a : ℝ)*|w a|) ≤
      (2*(p : ℝ))*(∑ a ∈ Finset.Icc 1 X, (a : ℝ)*|w a-w (a+1)|) := by
  dsimp only
  obtain ⟨q,hq,hpq,hqp⟩ := Nat.exists_prime_lt_and_le_two_mul p hp.ne_zero
  have h := periodic_weighted_variation q
    (max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id) hq.pos
    (fun a => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N a p)
    (fun a ha => raw_owner_weight_zero_larger_prime B A hB L y scale N p a hq hpq ha)
    (fun a ha => raw_owner_weight_outside B A L y scale N p a ha)
  apply h.trans
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast hqp
  · positivity

private theorem core_raw_owner_support {u : ℝ} {N K : ℕ} (B A : Finset ℕ)
    (hB : B ⊆ coreBand u N K) {p : ℕ} (hp : p.Prime)
    (hsmall : log p ≤ (N : ℝ)/2) (L y scale : ℝ) {a : ℕ}
    (ha : ZetaRieszJointPrimeEnergy.maskedWeight A (ZetaRieszJointPrimeEnergy.ownerRows B)
      L y scale N a p ≠ 0) : exp ((29/20 : ℝ)*N) ≤ a := by
  have hrow : p ∈ ZetaRieszJointPrimeEnergy.ownerRows B a := by
    by_contra h
    exact ha (by simp [ZetaRieszJointPrimeEnergy.maskedWeight,h])
  obtain ⟨m,hm,hpm⟩ := Finset.mem_image.mp hrow
  obtain ⟨hm,he⟩ := Finset.mem_filter.mp hm
  have hmS := hB hm
  have hpf := ZetaRieszOwnedCells.largestPrime_mem_of_two
    (by have := ZetaRieszJointPrimeEnergy.core_count hmS; omega : 2 ≤ m.primeFactors.card)
  have hm0 := (Nat.mem_primeFactors.mp hpf).2.2
  have hmul : p*a=m := by
    rw [← hpm,← he]
    exact Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hpf)
  have ha0 : a ≠ 0 := by intro h; rw [h,mul_zero] at hmul; exact hm0 hmul.symm
  have hloga : log m=log p+log a := by
    rw [← hmul,Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast ha0)]
  have hlow : (39/20 : ℝ)*N < log m := (Finset.mem_filter.mp hmS).2.1
  have haR : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha0
  exact (exp_le_exp.mpr (by linarith only [hlow,hloga,hsmall])).trans_eq (exp_log haR)

/-- On every literal small-owner core column, the CURRENT exp(-N/128)
absolute comparison allowance loses exponentially relative to its raw
absolute mass. This is a lower bound on that MAJORANT, not on the actual
signed error or carrier; no lower bound on population mass is assumed. -/
theorem raw_owner_allowance_lower {u : ℝ} {N K p : ℕ} (hp : p.Prime)
    (hsmall : log p ≤ (N : ℝ)/2) (B A : Finset ℕ) (hB : B ⊆ coreBand u N K)
    (L y scale : ℝ) :
    let X := max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id
    let w := fun a => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N a p
    (exp ((603/640 : ℝ)*N)/2)*(∑ a ∈ Finset.Icc 1 X, |w a|) ≤
      exp (-(N : ℝ)/128)*(∑ a ∈ Finset.Icc 1 X, (a : ℝ)*|w a-w (a+1)|) := by
  dsimp only
  let X := max 1 (ZetaRieszJointPrimeEnergy.cofactors B).sup id
  let w := fun a => ZetaRieszJointPrimeEnergy.maskedWeight A
    (ZetaRieszJointPrimeEnergy.ownerRows B) L y scale N a p
  have hmass : exp ((29/20 : ℝ)*N)*(∑ a ∈ Finset.Icc 1 X,|w a|) ≤
      ∑ a ∈ Finset.Icc 1 X,(a : ℝ)*|w a| := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    by_cases hw : w a=0
    · simp [hw]
    exact mul_le_mul_of_nonneg_right (core_raw_owner_support B A hB hp hsmall L y scale hw)
      (abs_nonneg _)
  have hv := raw_owner_variation_lower hp B A
    (fun m hm => by have := ZetaRieszJointPrimeEnergy.core_count (hB hm); omega) L y scale N
  change (∑ a ∈ Finset.Icc 1 X,(a : ℝ)*|w a|) ≤
    (2*(p : ℝ))*(∑ a ∈ Finset.Icc 1 X,(a : ℝ)*|w a-w (a+1)|) at hv
  have hpR : (p : ℝ) ≤ exp ((N : ℝ)/2) := by
    simpa only [exp_log (show (0 : ℝ)<p by exact_mod_cast hp.pos)] using exp_le_exp.mpr hsmall
  have hb := hmass.trans (hv.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpR (by norm_num : (0 : ℝ)≤2)) (by positivity)))
  have h := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ exp (-(N : ℝ)/2-(N : ℝ)/128)/2 by positivity)
  have hl : exp (-(N : ℝ)/2-(N : ℝ)/128)*exp ((29/20 : ℝ)*N)=
      exp ((603/640 : ℝ)*N) := by rw [← exp_add]; congr 1; ring
  have hr : exp (-(N : ℝ)/2-(N : ℝ)/128)*exp ((N : ℝ)/2)=
      exp (-(N : ℝ)/128) := by rw [← exp_add]; congr 1; ring
  change (exp ((603/640 : ℝ)*N)/2)*(∑ a ∈ Finset.Icc 1 X,|w a|) ≤
    exp (-(N : ℝ)/128)*(∑ a ∈ Finset.Icc 1 X,(a : ℝ)*|w a-w (a+1)|)
  calc
    _ = (exp (-(N : ℝ)/2-(N : ℝ)/128)/2)*
        (exp ((29/20 : ℝ)*N)*(∑ a ∈ Finset.Icc 1 X,|w a|)) := by
      rw [← hl]
      ring
    _ ≤ (exp (-(N : ℝ)/2-(N : ℝ)/128)/2)*
        (2*exp ((N : ℝ)/2)*(∑ a ∈ Finset.Icc 1 X,(a : ℝ)*|w a-w (a+1)|)) := h
    _ = _ := by
      rw [← hr]
      ring

/-- The same exponential loss applies to the CLEANED active-edge
allowance. Its squarefree cleanup does not remove canonical ownership
zeros. Every count/bin/phase/allocation mask remains literal here. -/
theorem comparison_owner_active_allowance_lower {u : ℝ} {N K p : ℕ} (hp : p.Prime)
    (hsmall : log p ≤ (N : ℝ)/2) (A : Finset ℕ) (L y scale : ℝ) :
    let X := max 1 (ZetaRieszJointPrimeEnergy.cofactors (comparisonOwnerBand u N K)).sup id
    let w := fun a => ZetaRieszJointPrimeEnergy.maskedWeight A
      (ZetaRieszJointPrimeEnergy.ownerRows (comparisonOwnerBand u N K)) L y scale N a p
    (exp ((603/640 : ℝ)*N)/2)*(∑ a ∈ Finset.Icc 1 X,|w a|) ≤
      exp (-(N : ℝ)/128)*
        (∑ a ∈ (Finset.Icc 1 X).filter (fun a =>
          remainingOwnerGeometry N (p*a) ∨ remainingOwnerGeometry N (p*(a+1))),
            (a : ℝ)*|w a-w (a+1)|) := by
  have h := raw_owner_allowance_lower hp hsmall (comparisonOwnerBand u N K) A
    (Finset.filter_subset _ _) L y scale
  dsimp only at h ⊢
  rw [comparisonOwnerVariation_eq_active] at h
  exact h

end RiemannGaussian.ZetaRieszOwnerHingeCancellation
