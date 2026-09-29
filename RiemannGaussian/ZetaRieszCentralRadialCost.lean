/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCentralCostGrowth
import RiemannGaussian.ZetaRieszCausalSurface

/-!
# Summing the coupled radial cost before charging its saddle

The original central cost and all its masks are unchanged. Radial shells
cannot all attain the same factorial saddle for a fixed prime. Summing the
positive radial envelope first saves a growing factor in the whole cost.
This does not remove the remaining exponential or prove phase cancellation.
-/

noncomputable section
open scoped BigOperators Classical
open Real MeasureTheory Set Filter Topology
namespace RiemannGaussian.ZetaRieszCentralRadialCost

/-- The unchanged factorial radial weight, without the source scale. -/
def radial (N : ℕ) (t : ℝ) : ℝ := exp (-t/2)*t^N/N.factorial

private theorem continuous_radial (N : ℕ) : Continuous (radial N) := by
  unfold radial
  fun_prop

private theorem radial_integrable (N : ℕ) : IntegrableOn (radial N) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (by linarith [Nat.cast_nonneg (α := ℝ) N] : (-1 : ℝ) < N) (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1/2)
  have he : radial N = fun t : ℝ => (t^N*exp (-(1/2)*t))/N.factorial := by
    ext t
    simp [radial,div_eq_mul_inv,mul_comm,mul_left_comm]
  rw [he]
  have h' : IntegrableOn (fun t : ℝ => t^N*exp (-(1/2)*t)) (Ioi 0) := by
    simpa using h
  exact h'.div_const _

/-- The entire factorial radial mass is evaluated exactly. -/
theorem integral_radial (N : ℕ) :
    (∫ t : ℝ in Ioi 0, radial N t) = (2 : ℝ)^(N+1) := by
  have h := ZetaRieszCausalSurface.radial_integral N (by norm_num : (0 : ℝ) < 1/2)
  have he : radial N = fun t : ℝ => (t^N*exp (-(1/2)*t))/N.factorial := by
    ext t
    simp [radial,div_eq_mul_inv,mul_comm,mul_left_comm]
  rw [he,integral_div,h,div_pow]
  field_simp
  simp

/-- A finite lattice of radial shells costs its integral, rather than
the number of shells times their common maximum. Uniform in the offset. -/
theorem sum_radial_le (N J : ℕ) {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h) :
    (∑ j ∈ Finset.range J, radial N (x+j*h)) ≤
      exp (h/2)/h*(2 : ℝ)^(N+1) := by
  have hcont := continuous_radial N
  have hone (j : ℕ) :
      h*exp (-h/2)*radial N (x+j*h) ≤
        ∫ t in (x+j*h)..(x+(j+1)*h), radial N t := by
    have hab : x+(j : ℝ)*h ≤ x+(j+1)*h := by linarith
    have hrad : 0 ≤ radial N (x+j*h) := by unfold radial; positivity
    have hp : ∀ t ∈ Icc (x+j*h) (x+(j+1)*h),
        exp (-h/2)*radial N (x+j*h) ≤ radial N t := by
      intro t ht
      have ht0 : 0 ≤ t := (by positivity : 0 ≤ x+j*h).trans ht.1
      have he : exp (-h/2)*exp (-(x+j*h)/2) ≤ exp (-t/2) := by
        rw [← exp_add]
        exact exp_le_exp.mpr (by linarith [ht.2])
      have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ x+j*h) ht.1 N
      unfold radial
      calc
        _ = ((exp (-h/2)*exp (-(x+j*h)/2))*(x+j*h)^N)/N.factorial := by ring
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul he hpow (by positivity) (exp_nonneg _)) (by positivity)
    have hi := intervalIntegral.integral_mono_on hab
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => exp (-h/2)*radial N (x+j*h)) volume _ _)
      (hcont.intervalIntegrable _ _) hp
    simpa only [intervalIntegral.integral_const,smul_eq_mul,mul_assoc,
      show x+(j+1)*h-(x+j*h)=h by ring] using hi
  have hadd := intervalIntegral.sum_integral_adjacent_intervals
    (f := radial N) (μ := volume) (a := fun j : ℕ => x+j*h)
    (fun j (_ : j < J) => hcont.intervalIntegrable _ _)
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range J) => hone j)
  simp only [← Finset.mul_sum] at hs
  have he : (∑ j ∈ Finset.range J,
      ∫ t in (x+j*h)..(x+(j+1)*h), radial N t) =
      ∫ t in x..(x+J*h), radial N t := by
    simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,zero_mul,add_zero] using hadd
  rw [he] at hs
  have hi : (∫ t in x..(x+J*h), radial N t) ≤ (2 : ℝ)^(N+1) := by
    rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right (by positivity)),← integral_radial N]
    apply setIntegral_mono_set (radial_integrable N)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 ≤ t := le_of_lt ht
      unfold radial
      positivity
    · exact Eventually.of_forall (fun t ht => lt_of_le_of_lt hx ht.1)
  have htotal := hs.trans hi
  calc
    _ ≤ (2 : ℝ)^(N+1)/(h*exp (-h/2)) :=
      (le_div_iff₀ (by positivity)).mpr (by nlinarith only [htotal])
    _ = _ := by rw [show -h/2=-(h/2) by ring,exp_neg]; field_simp

open ZetaRieszAllowancePrimeBoxes

/-- The exact prime energy mass that remains after radial aggregation. -/
def primeEnergyMass (X : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, sqrt (log p)/(p : ℝ)

private theorem logPrimes_mem {p : ℕ} (hp : p.Prime) {a h : ℝ}
    (hlo : a < log p) (hhi : log p ≤ a+h) : p ∈ logPrimes a h := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Ioc.mpr ⟨?_,?_⟩,hp⟩
  · apply (Nat.floor_lt (exp_nonneg _)).mpr
    simpa only [exp_log hp0] using exp_lt_exp.mpr hlo
  · apply Nat.le_floor
    simpa only [← exp_add,exp_log hp0,add_comm] using exp_le_exp.mpr hhi

private theorem weighted_prime_shell (j : ℕ) :
    (∑ p ∈ logPrimes (((j : ℝ)+1)/2) (1/2), sqrt (log p)/(p : ℝ)) ≤
      (2*exp (1/2)*log 4)/sqrt ((j : ℝ)+1) := by
  let a := ((j : ℝ)+1)/2
  have ha : 0 < a := by dsimp [a]; positivity
  have hcard := ZetaRieszQuadrupleCompensation.interval_card_upper ha
    (by norm_num : (0 : ℝ) ≤ 1/2)
  have hone p (hp : p ∈ logPrimes a (1/2)) :
      sqrt (log p)/(p : ℝ) ≤ sqrt ((j : ℝ)+1)*exp (-a) := by
    have hb := logPrimes_bounds hp
    have hlog : log p ≤ (j : ℝ)+1 := by dsimp [a] at hb; linarith [Nat.cast_nonneg (α := ℝ) j]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hb.1.pos
    have hinv : (p : ℝ)⁻¹=exp (-log p) := by rw [exp_neg,exp_log hp0]
    rw [div_eq_mul_inv,hinv]
    exact mul_le_mul (sqrt_le_sqrt hlog) (exp_le_exp.mpr (neg_le_neg hb.2.1.le))
      (exp_nonneg _) (sqrt_nonneg _)
  have hs := Finset.sum_le_sum (s := logPrimes a (1/2)) hone
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  have hb := hs.trans (mul_le_mul_of_nonneg_right hcard
    (show 0 ≤ sqrt ((j : ℝ)+1)*exp (-a) by positivity))
  have hc : exp (a+1/2)*exp (-a)=exp (1/2) := by rw [← exp_add]; congr 1; ring
  have hr : (sqrt ((j : ℝ)+1))^2=(j : ℝ)+1 := sq_sqrt (by positivity)
  apply hb.trans_eq
  have hs0 : sqrt ((j : ℝ)+1) ≠ 0 := ne_of_gt (by positivity)
  calc
    _ = (log 4*sqrt ((j : ℝ)+1)/a)*(exp (a+1/2)*exp (-a)) := by ring
    _ = (2*exp (1/2)*log 4)*sqrt ((j : ℝ)+1)/((j : ℝ)+1) := by
      rw [hc]
      dsimp [a]
      field_simp
    _ = _ := by
      apply (div_eq_div_iff (by positivity : (j : ℝ)+1 ≠ 0) hs0).mpr
      calc
        _ = (2*exp (1/2)*log 4)*(sqrt ((j : ℝ)+1))^2 := by ring
        _ = _ := by rw [hr]

private theorem sum_inv_sqrt (J : ℕ) :
    (∑ j ∈ Finset.range J, 1/sqrt ((j : ℝ)+1)) ≤ 2*sqrt J := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have h0 := sqrt_nonneg (J : ℝ)
    have h1 : 0 < sqrt ((J : ℝ)+1) := by positivity
    have hlo := sqrt_le_sqrt (show (J : ℝ) ≤ J+1 by linarith)
    have hs := sq_sqrt (show (0 : ℝ) ≤ J by positivity)
    have ht := sq_sqrt (show (0 : ℝ) ≤ J+1 by positivity)
    have hd : 1/sqrt ((J : ℝ)+1) ≤ 2*(sqrt ((J : ℝ)+1)-sqrt J) := by
      apply (div_le_iff₀ h1).mpr
      nlinarith [sq_nonneg (sqrt ((J : ℝ)+1)-sqrt J)]
    push_cast
    linarith

/-- Chebyshev counts pay the literal prime mass without the spurious
log-log factor caused by maximizing the profile energy over all primes. -/
theorem primeEnergyMass_le (X : ℕ) :
    primeEnergyMass X ≤ (4*exp (1/2)*log 4)*sqrt (4*log X+8) := by
  let M := ⌈log X⌉₊
  let J := 4*M+4
  let B := fun j : ℕ => logPrimes (((j : ℝ)+1)/2) (1/2)
  let D := (Finset.range J).sigma B
  let P := (Finset.Icc 1 X).filter Nat.Prime
  have hMl : log X ≤ (M : ℝ) := Nat.le_ceil _
  have hMu : (M : ℝ) < log X+1 := Nat.ceil_lt_add_one (log_natCast_nonneg X)
  have hcover : P ⊆ D.image (fun z => z.2) := by
    intro p hp
    obtain ⟨hpI,hp⟩ := Finset.mem_filter.mp hp
    have hlog : (1/2 : ℝ) < log p := by
      have hl := log_le_log (by norm_num : (0 : ℝ) < 2)
        (show (2 : ℝ) ≤ p by exact_mod_cast hp.two_le)
      linarith [log_two_gt_d9]
    have hlogX : log p ≤ log X := log_le_log (by exact_mod_cast hp.pos)
      (by exact_mod_cast (Finset.mem_Icc.mp hpI).2)
    let q := ⌈2*log p⌉₊
    have hqlo : 2*log p ≤ (q : ℝ) := Nat.le_ceil _
    have hqhi : (q : ℝ) < 2*log p+1 := Nat.ceil_lt_add_one (by linarith)
    have hq2 : 2 ≤ q := by
      have hh : (1 : ℝ) < q := by linarith
      have hh' : 1 < q := by exact_mod_cast hh
      omega
    have hqJ : q ≤ J := Nat.ceil_le.mpr (by dsimp [J]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) M])
    let j := q-2
    have hej : (j : ℝ)+2=q := by exact_mod_cast Nat.sub_add_cancel hq2
    have hpB : p ∈ B j := logPrimes_mem hp (by linarith) (by linarith)
    exact Finset.mem_image.mpr ⟨⟨j,p⟩,Finset.mem_sigma.mpr
      ⟨Finset.mem_range.mpr (by dsimp [j,J] at *; omega),hpB⟩,rfl⟩
  have hs : primeEnergyMass X ≤ ∑ j ∈ Finset.range J, ∑ p ∈ B j,
      sqrt (log p)/(p : ℝ) := by
    calc
      _ ≤ ∑ p ∈ (D.image (fun z => z.2) : Finset ℕ), sqrt (log p)/(p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover (fun _ _ _ => by positivity)
      _ ≤ ∑ z ∈ D, sqrt (log z.2)/(z.2 : ℝ) :=
        Finset.sum_image_le_of_nonneg (s := D) (g := fun z : Σ _j : ℕ, ℕ => z.2)
          (f := fun p : ℕ => sqrt (log p)/(p : ℝ)) (fun _ _ => by positivity)
      _ = _ := Finset.sum_sigma _ _ _
  have hj : (J : ℝ) ≤ 4*log X+8 := by dsimp [J]; push_cast; linarith
  calc
    _ ≤ ∑ j ∈ Finset.range J, (2*exp (1/2)*log 4)/sqrt ((j : ℝ)+1) :=
      hs.trans (Finset.sum_le_sum (fun j _ => weighted_prime_shell j))
    _ = (2*exp (1/2)*log 4)*(∑ j ∈ Finset.range J, 1/sqrt ((j : ℝ)+1)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ (2*exp (1/2)*log 4)*(2*sqrt J) :=
      mul_le_mul_of_nonneg_left (sum_inv_sqrt J) (by positivity)
    _ = (4*exp (1/2)*log 4)*sqrt J := by ring
    _ ≤ _ := by gcongr

open ZetaRieszJointPrimeEnergy ZetaRieszCenteredPrimeEnergy
  ZetaRieszJointAllocation ZetaRieszCentralCostGrowth ZetaRieszPrimeEndpoint ZetaRieszOwnedCells

private theorem radial_le_shift (N : ℕ) {t t' h : ℝ} (ht : 0 ≤ t)
    (hle : t ≤ t') (hhi : t' ≤ t+h) : radial N t ≤ exp (h/2)*radial N t' := by
  have he : exp (-t/2) ≤ exp (h/2)*exp (-t'/2) := by
    rw [← exp_add]
    exact exp_le_exp.mpr (by linarith)
  have hp := pow_le_pow_left₀ ht hle N
  unfold radial
  have hb := div_le_div_of_nonneg_right
    (mul_le_mul he hp (by positivity) (by positivity))
    (show (0 : ℝ) ≤ N.factorial by positivity)
  simpa only [div_eq_mul_inv,mul_assoc] using hb

/-- Keep each prime's actual radial position instead of charging every
cofactor shell at the common peak. The original allocation and phase remain. -/
theorem primeWeight_radial_le {u L b : ℝ} (hu : 0 ≤ u) {N : ℕ}
    (hN : 0 < N) (hL : (N : ℝ) ≤ L) (A : Finset ℕ) (y : ℝ)
    {n p : ℕ} (hn : 0 < n) (hp : 0 < p)
    (hT : log p+log n ≤ 3*N) (hlo : b ≤ log n) (hhi : log n ≤ b+log 2) :
    |u^(N+1)*primeWeight A L y N n p| ≤
      (3*u^(N+1)*exp (log 2/2)*radial N (log p+b+log 2))/((n : ℝ)*p) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < L := hNR.trans_le hL
  let T := log p+log n
  have hT0 : 0 ≤ T := add_nonneg (log_natCast_nonneg p) (log_natCast_nonneg n)
  have hphase := Real.abs_cos_le_one (y*T)
  have halloc : |1-boundedShare A N (p*n)| ≤ 1 := by
    rw [abs_of_nonneg (by linarith [(boundedShare_bounds A N (p*n)).2])]
    linarith [(boundedShare_bounds A N (p*n)).1]
  have hratio : T/L ≤ 3 := (div_le_iff₀ hL0).mpr (by dsimp [T]; linarith)
  have hrad := radial_le_shift N hT0
    (show T ≤ log p+b+log 2 by dsimp [T]; linarith)
    (show log p+b+log 2 ≤ T+log 2 by dsimp [T]; linarith)
  have habs : |u^(N+1)*primeWeight A L y N n p| =
      (|1-boundedShare A N (p*n)| * |cos (y*T)|)*
        (u^(N+1)*(T/L)*radial N T)/((n : ℝ)*p) := by
    simp only [primeWeight,radial,abs_div,abs_mul,abs_neg,abs_pow,abs_of_nonneg hu,
      abs_of_pos hL0,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N.factorial),
      abs_of_pos hnR,abs_of_pos hpR,abs_of_pos (exp_pos _)]
    rw [abs_of_nonneg hT0,pow_succ]
    dsimp [T]
    ring
  rw [habs]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hprod : |1-boundedShare A N (p*n)| * |cos (y*T)| ≤ 1 :=
    (mul_le_mul halloc hphase (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  calc
    _ ≤ u^(N+1)*(T/L)*radial N T :=
      mul_le_of_le_one_left (by unfold radial; positivity) hprod
    _ ≤ u^(N+1)*3*(exp (log 2/2)*radial N (log p+b+log 2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hratio (by positivity)) hrad
        (by unfold radial; positivity) (by positivity)
    _ = _ := by ring

private theorem column_le {E V : ℝ} (hE : 0 ≤ E) (hV : 0 ≤ V)
    {M : ℕ} (hM : 0 < M) (N : ℕ) (A S : Finset ℕ) (Q : ℕ → Finset ℕ)
    (L y scale : ℝ) {p : ℕ} (hp : p.Prime) (hS : S ⊆ Finset.Ioc M (2*M))
    (hW : ∀ n ∈ S, |maskedWeight A Q L y scale N n p| ≤ V/((n : ℝ)*p)) :
    sqrt ((∑ n ∈ S, (maskedWeight A Q L y scale N n p)^2)*E*(2*M : ℕ)*
      centeredEnergy (2*M) (hinge L p)) ≤ sqrt (2*E)*V*sqrt (log p)/(p : ℝ) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hcard : (S.card : ℝ) ≤ M := by
    have h := Finset.card_le_card hS
    rw [Nat.card_Ioc] at h
    have he : 2*M-M=M := by omega
    rw [he] at h
    exact_mod_cast h
  have hw : (∑ n ∈ S, (maskedWeight A Q L y scale N n p)^2) ≤
      V^2/((M : ℝ)*(p : ℝ)^2) := by
    calc
      _ ≤ ∑ _n ∈ S, (V/((M : ℝ)*p))^2 := by
        apply Finset.sum_le_sum
        intro n hn
        have hnm : (M : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp (hS hn)).1.le
        have h := (hW n hn).trans (div_le_div_of_nonneg_left hV (by positivity)
          (mul_le_mul_of_nonneg_right hnm hp0.le))
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = S.card*(V/((M : ℝ)*p))^2 := by simp
      _ ≤ M*(V/((M : ℝ)*p))^2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
      _ = _ := by field_simp
  have hq := (centeredEnergy_le_raw (2*M) (hinge L p)).trans
    (ZetaRieszCentralPrimeDifference.hinge_energy L hp.one_lt.le (2*M))
  have hbud : (∑ n ∈ S, (maskedWeight A Q L y scale N n p)^2)*E*(2*M : ℕ)*
      centeredEnergy (2*M) (hinge L p) ≤ 2*E*V^2*log p/(p : ℝ)^2 := by
    calc
      _ ≤ (V^2/((M : ℝ)*(p : ℝ)^2))*E*(2*M : ℕ)*log p := by
        have := centeredEnergy_nonneg (2*M) (hinge L p)
        gcongr
      _ = _ := by push_cast; field_simp
  apply (sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  rw [div_pow,mul_pow,mul_pow,sq_sqrt (by positivity),sq_sqrt (log_natCast_nonneg p)]
  exact hbud

private theorem shell_rows {B : Finset ℕ}
    (hB : ∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card) (j : ℕ) :
    cofactors (shell B j) ⊆ Finset.Ioc (2^j) (2*2^j) := by
  intro n hn
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hm,hj⟩ := Finset.mem_filter.mp hm
  have hd := owner_data (hB m hm).1 (hB m hm).2
  have hn : 1 < ownerCofactor m := by
    have hz := hd.2.2.1.ne_zero
    have hne : ownerCofactor m ≠ 1 := by intro he; simp [he] at hd
    omega
  have hz : ownerCofactor m-1 ≠ 0 := by omega
  have hlo := Nat.pow_log_le_self 2 hz
  have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (ownerCofactor m-1)
  change Nat.log 2 (ownerCofactor m-1)=j at hj
  rw [hj] at hlo hhi
  rw [Nat.pow_succ] at hhi
  exact Finset.mem_Ioc.mpr ⟨by omega,by omega⟩

private theorem label_le_pow {N m : ℕ} (hm : 0 < m)
    (hlog : log m ≤ (2029/1000 : ℝ)*N) : m ≤ 2^(4*N) := by
  have hl : log (m : ℝ) ≤ log ((2 : ℝ)^(4*N)) := by
    rw [Real.log_pow]
    push_cast
    nlinarith [Real.log_two_gt_d9,Nat.cast_nonneg (α := ℝ) N]
  exact_mod_cast (Real.log_le_log_iff (by exact_mod_cast hm) (by positivity)).mp hl

/-- A square-root-order majorant for the SAME combined central cost.
Both arithmetic and radial populations have been summed explicitly. -/
def radialGrowthBound (E u : ℝ) (N : ℕ) : ℝ :=
  (12*sqrt (2*E)/log 2)*(4*exp (1/2)*log 4)*sqrt (16*N+8)*(2*u)^N

/-- The entire central cost is O(sqrt(N)*(2u)^N), uniformly in all
heights and original finite masks. The radial and prime sums are paid before
separate maxima can introduce the former N*log(N) loss. -/
theorem centralCost_le_radialGrowth {E u L : ℝ} (hE : 0 ≤ E) (hu : 0 ≤ u)
    (hu1 : u ≤ 1) {N : ℕ} (hN : 0 < N) (hL : (N : ℝ) ≤ L)
    (A B : Finset ℕ) (y : ℝ)
    (hB : ∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card)
    (hlog : ∀ m ∈ B, log m ≤ (2029/1000 : ℝ)*N) :
    centralCost E A B N L y (u^(N+1)) ≤ radialGrowthBound E u N := by
  let R := 2^(4*N)
  let P := (Finset.Icc 1 R).filter Nat.Prime
  let c := 3*sqrt (2*E)*u^(N+1)*exp (log 2/2)
  let f := fun (j p : ℕ) => radial N ((log p+log 2)+(j : ℝ)*log 2)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hblock j :
      primeCost E (2*2^j) N A (cofactors (shell B j)) (ownerPrimes (shell B j))
        (ownerPrimes (shell B j)) (ownerRows (shell B j))
        (fun a p => if a=p then 1 else 0) L y (u^(N+1)) ≤
      ∑ p ∈ P, c*f j p*sqrt (log p)/(p : ℝ) := by
    have hSB : ∀ m ∈ shell B j, Squarefree m ∧ 3 ≤ m.primeFactors.card :=
      fun m hm => hB m (Finset.mem_filter.mp hm).1
    have hS := shell_rows hB j
    have hP : ∀ p ∈ ownerPrimes (shell B j), p ∈ P := by
      intro p hp
      obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hp
      have hd := owner_data (hSB m hm).1 (hSB m hm).2
      have hmB := (Finset.mem_filter.mp hm).1
      have hpm : largestPrime m ≤ m := by
        calc
          _ ≤ largestPrime m*ownerCofactor m :=
            Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hd.2.2.1.ne_zero)
          _ = m := hd.2.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd.1.pos,
        hpm.trans (label_le_pow (Nat.pos_of_ne_zero (hSB m hm).1.ne_zero) (hlog m hmB))⟩,hd.1⟩
    have hone p (hp : p ∈ ownerPrimes (shell B j)) :
        sqrt ((∑ n ∈ cofactors (shell B j),
          (maskedWeight A (ownerRows (shell B j)) L y (u^(N+1)) N n p)^2)*E*(2*2^j : ℕ)*
          centeredEnergy (2*2^j) (hinge L p)) ≤ c*f j p*sqrt (log p)/(p : ℝ) := by
      let V := 3*u^(N+1)*exp (log 2/2)*f j p
      have hV : 0 ≤ V := by dsimp [V,f,radial]; positivity
      have hpp := (Finset.mem_filter.mp (hP p hp)).2
      have hW : ∀ n ∈ cofactors (shell B j),
          |maskedWeight A (ownerRows (shell B j)) L y (u^(N+1)) N n p| ≤ V/((n : ℝ)*p) := by
        intro n hn
        unfold maskedWeight
        split_ifs with hrow
        · obtain ⟨m,hm,hmp⟩ := Finset.mem_image.mp hrow
          obtain ⟨hm,hmn⟩ := Finset.mem_filter.mp hm
          have hd := owner_data (hSB m hm).1 (hSB m hm).2
          have hn0 : 0 < n := Nat.pos_of_ne_zero (cofactors_data (shell B j) hSB hn).1.ne_zero
          have he : p*n=m := by simpa only [hmp,hmn] using hd.2.1
          have hT : log p+log n ≤ 3*N := by
            have hh : log p+log n=log m := by
              rw [← he,Nat.cast_mul,log_mul (by exact_mod_cast hpp.ne_zero) (by exact_mod_cast hn0.ne')]
            rw [hh]
            have hh' := hlog m (Finset.mem_filter.mp hm).1
            linarith [Nat.cast_nonneg (α := ℝ) N]
          have hs := Finset.mem_Ioc.mp (hS hn)
          have hlo : (j : ℝ)*log 2 ≤ log n := by
            have h := log_le_log (show (0 : ℝ) < (2^j : ℕ) by positivity)
              (show ((2^j : ℕ) : ℝ) ≤ n by exact_mod_cast hs.1.le)
            simpa only [Nat.cast_pow,Nat.cast_ofNat,log_pow] using h
          have hhi : log n ≤ (j : ℝ)*log 2+log 2 := by
            have h := log_le_log (by exact_mod_cast hn0 : (0 : ℝ) < n)
              (show (n : ℝ) ≤ (2*2^j : ℕ) by exact_mod_cast hs.2)
            simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,
              log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (2 : ℝ)^j ≠ 0),
              log_pow,add_comm] using h
          have hb := primeWeight_radial_le hu hN hL A y hn0 hpp.pos hT hlo hhi
          convert hb using 1
          dsimp [V,f]
          congr 3
          ring
        · simpa only [abs_zero] using div_nonneg hV (by positivity : (0 : ℝ) ≤ (n : ℝ)*p)
      have hb := column_le hE hV (show 0 < 2^j by positivity) N A
        (cofactors (shell B j)) (ownerRows (shell B j)) L y (u^(N+1)) hpp hS hW
      convert hb using 1
      dsimp [c,V]
      ring
    have hs : primeCost E (2*2^j) N A (cofactors (shell B j)) (ownerPrimes (shell B j))
        (ownerPrimes (shell B j)) (ownerRows (shell B j))
        (fun a p => if a=p then 1 else 0) L y (u^(N+1)) ≤
        ∑ p ∈ ownerPrimes (shell B j), c*f j p*sqrt (log p)/(p : ℝ) := by
      unfold primeCost jointCost
      apply Finset.sum_le_sum
      intro p hp
      simpa only [rotate,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,hp,if_true] using hone p hp
    exact hs.trans (Finset.sum_le_sum_of_subset_of_nonneg hP
      (fun p _ _ => by dsimp [f,radial]; positivity))
  have hrad p : (∑ j ∈ Finset.range (4*N), f j p) ≤
      exp (log 2/2)/log 2*(2 : ℝ)^(N+1) :=
    sum_radial_le N (4*N) (by have := log_natCast_nonneg p; positivity)
      (log_pos (by norm_num : (1 : ℝ) < 2))
  have hmass : primeEnergyMass R ≤ (4*exp (1/2)*log 4)*sqrt (16*N+8) := by
    apply (primeEnergyMass_le R).trans
    have hlogR : log (R : ℝ) ≤ 4*N := by
      dsimp [R]
      rw [Nat.cast_pow,log_pow]
      push_cast
      nlinarith [log_two_lt_d9,Nat.cast_nonneg (α := ℝ) N]
    apply mul_le_mul_of_nonneg_left (sqrt_le_sqrt (by linarith)) (by positivity)
  have hs : centralCost E A B N L y (u^(N+1)) ≤
      c*(exp (log 2/2)/log 2*(2 : ℝ)^(N+1))*primeEnergyMass R := by
    calc
      _ ≤ ∑ j ∈ Finset.range (4*N), ∑ p ∈ P, c*f j p*sqrt (log p)/(p : ℝ) :=
        Finset.sum_le_sum (fun j _ => hblock j)
      _ = ∑ p ∈ P, (c*sqrt (log p)/(p : ℝ))*(∑ j ∈ Finset.range (4*N), f j p) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ ≤ ∑ p ∈ P, (c*sqrt (log p)/(p : ℝ))*(exp (log 2/2)/log 2*(2 : ℝ)^(N+1)) :=
        Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left (hrad p) (by positivity))
      _ = _ := by
        unfold primeEnergyMass
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
  have he : exp (log 2/2)*exp (log 2/2)=2 := by
    rw [← exp_add,show log 2/2+log 2/2=log 2 by ring,exp_log (by norm_num : (0 : ℝ) < 2)]
  have hscale : c*(exp (log 2/2)/log 2*(2 : ℝ)^(N+1)) ≤
      (12*sqrt (2*E)/log 2)*(2*u)^N := by
    have hident : c*(exp (log 2/2)/log 2*(2 : ℝ)^(N+1)) =
        u*((12*sqrt (2*E)/log 2)*(2*u)^N) := by
      dsimp [c]
      rw [mul_pow,pow_succ,pow_succ]
      linear_combination (6*sqrt (2*E)*u*u^N*2^N/log 2)*he
    rw [hident]
    exact mul_le_of_le_one_left (by positivity) hu1
  calc
    _ ≤ (12*sqrt (2*E)/log 2)*(2*u)^N*primeEnergyMass R :=
      hs.trans (mul_le_mul_of_nonneg_right hscale (by unfold primeEnergyMass; positivity))
    _ ≤ (12*sqrt (2*E)/log 2)*(2*u)^N*((4*exp (1/2)*log 4)*sqrt (16*N+8)) := by
      gcongr
    _ = _ := by unfold radialGrowthBound; ring

/-- Explicit square-root order, without any hidden growing factor. The
exponential factor is unchanged, so this is not a bounded eventual allowance. -/
theorem radialGrowthBound_le_sqrt (E u : ℝ) (hu : 0 ≤ u) {N : ℕ} (hN : 0 < N) :
    radialGrowthBound E u N ≤
      (60*sqrt (2*E)/log 2)*(4*exp (1/2)*log 4)*sqrt N*(2*u)^N := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : sqrt (16*(N : ℝ)+8) ≤ 5*sqrt N := by
    apply (sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    rw [mul_pow,sq_sqrt (by positivity)]
    nlinarith
  unfold radialGrowthBound
  calc
    _ ≤ (12*sqrt (2*E)/log 2)*(4*exp (1/2)*log 4)*(5*sqrt N)*(2*u)^N := by
      gcongr
    _ = _ := by ring

open ZetaRieszParityPacket

/-- Both original whole-core bounds inherit the improved large-order
cost. All central counts, factorial orders, full phase and masks remain;
the already paid outer error is charged exactly once. No zero hypothesis
or prime-density approximation enters. -/
theorem exists_eventual_core_radial_bound :
    ∃ E C : ℝ, 0 < E ∧ 0 ≤ C ∧ ∀ (u : ℝ),
      0 < u → u ≤ ZetaRieszWideOwnerAudit.radiusCeiling →
      ∀ᶠ N : ℕ in atTop, ∀ (y : ℝ) (K : ℕ),
        let B := LogarithmicDeviation.deviationBand ((coreBand u N K).filter Squarefree)
          (1971/1000) (2029/1000) N;
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N;
        let L := SquarefreeVaughanLogSource.length u N;
        let D := centralCost E A B N L y (u^(N+1));
        let G := min (growthBound E u N) (radialGrowthBound E u N);
        D ≤ G ∧
        -(G+ZetaRieszLargeOrderCore.rate^N*C) ≤ u^(N+1)*(coreResponse u y N K).re ∧
        u^(N+1)*(coreResponse u y N K).re ≤ G+ZetaRieszLargeOrderCore.rate^N*C := by
  obtain ⟨E,C,hE,hC,hbound⟩ := exists_eventual_core_growth_bound
  refine ⟨E,C,hE,hC,fun u hu hU => ?_⟩
  filter_upwards [hbound u hu hU,ZetaRieszMaskSupport.eventually_length_lower hu
    (hU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le),eventually_ge_atTop 1]
    with N hb hlen hN y K
  have hB : ∀ n ∈ LogarithmicDeviation.deviationBand ((coreBand u N K).filter Squarefree)
      (1971/1000) (2029/1000) N, Squarefree n ∧ 3 ≤ n.primeFactors.card := by
    intro n hn
    have hs := Finset.mem_filter.mp (Finset.mem_filter.mp hn).1
    exact ⟨hs.2,core_count hs.1⟩
  have hlog : ∀ n ∈ LogarithmicDeviation.deviationBand ((coreBand u N K).filter Squarefree)
      (1971/1000) (2029/1000) N, log n ≤ (2029/1000 : ℝ)*N :=
    fun _ hn => (Finset.mem_filter.mp hn).2.2
  have hL : (N : ℝ) ≤ SquarefreeVaughanLogSource.length u N := by
    have := Nat.cast_nonneg (α := ℝ) N
    linarith
  have hu1 : u ≤ 1 := by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at hU; linarith
  have hc := centralCost_le_radialGrowth hE.le hu.le hu1 (by omega : 0 < N) hL
    (ZetaRieszAnnulusJoint.intermediatePrimes u N)
    (LogarithmicDeviation.deviationBand ((coreBand u N K).filter Squarefree)
      (1971/1000) (2029/1000) N) y hB hlog
  have hold := hb y K
  dsimp only at hold ⊢
  have hmin := le_min hold.1 hc
  exact ⟨hmin,by linarith only [hmin,hold.2.1],by linarith only [hmin,hold.2.2]⟩

end RiemannGaussian.ZetaRieszCentralRadialCost
