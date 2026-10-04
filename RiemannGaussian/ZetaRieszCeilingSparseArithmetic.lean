/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCeilingPhaseAverage
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Pointwise payment of sparse literal arithmetic populations

The entire joined integer coefficient is retained. Weighted Cauchy--Schwarz
pays sufficiently sparse populations uniformly at every height, rather than
exchanging the order and height limits of the preceding averaged theorem.
This does not pay the full union or establish the full fixed-strip ceiling.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Complex Real Filter Topology MeasureTheory
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszCeilingSparseArithmetic
open ZetaRieszCeilingPhaseAverage ZetaRieszJointAllocation ZetaRieszParityPacket
open ZetaRieszAnnulusJoint ZetaRieszWideOwnerAudit

/-- A fixed summable tilt, small enough to preserve the numerical source margin. -/
def epsilon : ℝ := 1/100000

/-- Complete genuine divisor-square mass at the summable tilted exponent. -/
def arithmeticMass : ℝ := divisorSquareDirichletMass (1+epsilon)

theorem arithmeticMass_nonneg : 0<=arithmeticMass := divisorSquareDirichletMass_nonneg _

/-- Weighted size of a literal integer population, with no phase randomization. -/
def weightedPopulation (S : Finset ℕ) : ℝ :=
  ∑ n ∈ S, (n : ℝ)^(-(1-epsilon))

theorem weightedPopulation_nonneg (S : Finset ℕ) : 0<=weightedPopulation S := by
  exact Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem core_log_upper {u : ℝ} {N K n : ℕ} (hn : n∈coreBand u N K) :
    Real.log n<=3*N := by
  have h := (Finset.mem_filter.mp hn).2.2
  linarith [show (0 : ℝ)<=N by positivity]

/-- The half-tilt is used only to price a genuinely sparse subset. The
positive whole-core allowance is not asserted to decay. -/
theorem norm_joinedAmplitude_half {u : ℝ} (hu : 0<=u) {N K n : ℕ}
    (hn : n∈coreBand u N K) :
    ‖joinedAmplitude u N K n‖ <=
      (3*u*N*(2*u)^N)*(n.divisors.card : ℝ)*(n : ℝ)^(-1 : ℝ) := by
  have hp : (0 : ℝ)<n := by exact_mod_cast core_label_pos hn
  have hc := norm_residualCoefficient_le (intermediatePrimes u N)
    (SquarefreeVaughanLogSource.length_pos u N) N n
  have hk : ‖zetaPrimeLogKernel N (3/2) n‖<=
      (2 : ℝ)^N*zetaPrimeExpWeight 1 n := by
    convert norm_zetaPrimeLogKernel_le N (3/2) n (by norm_num : (0 : ℝ)<1/2) using 1
    norm_num
  have he : zetaPrimeExpWeight 1 n=(n : ℝ)^(-1 : ℝ) := by
    rw [zetaPrimeExpWeight,Real.rpow_def_of_pos hp]
    congr 1
    ring
  apply (norm_joinedAmplitude_le u N K n).trans
  unfold amplitude
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu]
  calc
    _ <= u^(N+1)*((n.divisors.card : ℝ)*Real.log n)*
        ((2 : ℝ)^N*zetaPrimeExpWeight 1 n) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left
        (hc.trans (majorant_le_divisor_log n)) (pow_nonneg hu _)) hk
        (norm_nonneg _) (by positivity)
    _ <= u^(N+1)*((n.divisors.card : ℝ)*(3*N))*
        ((2 : ℝ)^N*zetaPrimeExpWeight 1 n) := by
      apply mul_le_mul_of_nonneg_right _
        (mul_nonneg (by positivity) (Real.exp_pos _).le)
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (core_log_upper hn) (Nat.cast_nonneg _)) (pow_nonneg hu _)
    _ = _ := by rw [he,pow_succ,mul_pow]; ring

/-- An independent pointwise bound on ANY literal subpopulation. All
signed coefficients are collected before applying the weighted inequality. -/
theorem norm_signal_sq_le {u : ℝ} (hu : 0<=u) {N K : ℕ}
    (S : Finset ℕ) (hS : S⊆coreBand u N K) (y : ℝ) :
    ‖signal S (joinedAmplitude u N K) y‖^2 <=
      (3*u*N*(2*u)^N)^2*arithmeticMass*weightedPopulation S := by
  let f : ℕ→ℝ := fun n => (3*u*N*(2*u)^N)^2*
    ((n.divisors.card : ℝ)^2*(n : ℝ)^(-(1+epsilon)))
  let g : ℕ→ℝ := fun n => (n : ℝ)^(-(1-epsilon))
  have hfg (n : ℕ) (hn : n∈S) : ‖joinedAmplitude u N K n‖^2<=f n*g n := by
    have hp : (0 : ℝ)<n := by exact_mod_cast core_label_pos (hS hn)
    have hb := pow_le_pow_left₀ (norm_nonneg _) (norm_joinedAmplitude_half hu (hS hn)) 2
    have he : ((n : ℝ)^(-1 : ℝ))^2=
        (n : ℝ)^(-(1+epsilon))*(n : ℝ)^(-(1-epsilon)) := by
      rw [← Real.rpow_add hp]
      rw [← Real.rpow_mul_natCast hp.le (-1) 2]
      congr 1
      push_cast
      ring
    simpa only [f,g,mul_pow,mul_assoc,he] using hb
  have hs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (r := fun n => ‖joinedAmplitude u N K n‖) (f := f) (g := g)
    (fun _ _ => by dsimp [f]; positivity) (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) hfg
  have hsum : (∑ n ∈ S, f n)<= (3*u*N*(2*u)^N)^2*arithmeticMass := by
    simp only [f,←Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact (summable_card_divisors_sq_mul_rpow_neg
      (by norm_num [epsilon] : (1 : ℝ)<1+epsilon)).sum_le_tsum _
      (fun _ _ => by positivity)
  have hnorm : ‖signal S (joinedAmplitude u N K) y‖<=∑ n ∈ S, ‖joinedAmplitude u N K n‖ := by
    apply (norm_sum_le _ _).trans_eq
    simp only [norm_mul,character_norm,mul_one]
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    (hs.trans (mul_le_mul_of_nonneg_right hsum (weightedPopulation_nonneg S)))

/-- Exact unit-log cell; this is not a continuum replacement of a finite mask. -/
def logCell (S : Finset ℕ) (k : ℕ) : Finset ℕ :=
  S.filter (fun n => Nat.floor (Real.log n)=k)

/-- Every finite integer progression has its complete quotient count,
including the endpoint correction. -/
theorem progression_card_le (S : Finset ℕ) (d r M : ℕ)
    (hbound : ∀ n∈S, n<=M) (hmod : ∀ n∈S, n%d=r) :
    S.card<=M/d+1 := by
  have h := Finset.card_le_card_of_injOn (s := S) (t := Finset.range (M/d+1))
    (fun n => n/d) (fun n hn => Finset.mem_range.mpr
      (by
        change n/d<M/d+1
        have hh := Nat.div_le_div_right (c := d) (hbound n hn)
        omega)) (by
        intro a ha b hb he
        change a/d=b/d at he
        calc
          a = a%d+d*(a/d) := (Nat.mod_add_div a d).symm
          _ = b%d+d*(b/d) := by rw [hmod a ha,hmod b hb,he]
          _ = b := Nat.mod_add_div b d)
  simpa only [Finset.card_range] using h

/-- Every actual core cell has a nonnegative sparse-count exponent. -/
theorem cell_lower {u : ℝ} {N K n k : ℕ} (hN : 1<=N)
    (hn : n∈coreBand u N K) (hk : Nat.floor (Real.log n)=k) :
    (N : ℝ)/2500<=k := by
  have hlo := (Finset.mem_filter.mp hn).2.1
  have hhi := Nat.lt_floor_add_one (Real.log n)
  rw [hk] at hhi
  have hNR : (1 : ℝ)<=N := by exact_mod_cast hN
  linarith

/-- The pointwise sparse population condition is discharged by ACTUAL
integer congruence classes; no Type-II or prime-distribution premise is assumed. -/
theorem residue_cell_card {u : ℝ} {N K : ℕ} (hN : 1<=N)
    (S : Finset ℕ) (hS : S⊆coreBand u N K) (d r : ℕ)
    (hd : Real.exp ((N : ℝ)/2500)<=(d : ℝ))
    (hmod : ∀ n∈S, n%d=r) (k : ℕ) :
    ((logCell S k).card : ℝ)<=5*Real.exp ((k : ℝ)-(N : ℝ)/2500) := by
  by_cases hempty : logCell S k=∅
  · rw [hempty,Finset.card_empty,Nat.cast_zero]
    positivity
  obtain ⟨n,hn⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hk0 := cell_lower hN (hS (Finset.mem_filter.mp hn).1) (Finset.mem_filter.mp hn).2
  have hk1 : 1<=Real.exp ((k : ℝ)-(N : ℝ)/2500) := Real.one_le_exp_iff.mpr (by linarith)
  have hdpos : (0 : ℝ)<d := lt_of_lt_of_le (Real.exp_pos _) hd
  have hd1 : (1 : ℝ)<=d := by
    have hh : 0<d := by exact_mod_cast hdpos
    exact_mod_cast (show 1<=d by omega)
  let M := Nat.ceil (Real.exp ((k : ℝ)+1))
  have hbound (a : ℕ) (ha : a∈logCell S k) : a<=M := by
    have haS := hS (Finset.mem_filter.mp ha).1
    have hapos : (0 : ℝ)<a := by exact_mod_cast core_label_pos haS
    have hh := Nat.lt_floor_add_one (Real.log a)
    rw [(Finset.mem_filter.mp ha).2] at hh
    have hc : (a : ℝ)<=Real.exp ((k : ℝ)+1) := by
      simpa only [Real.exp_log hapos] using (Real.exp_lt_exp.mpr hh).le
    exact Nat.cast_le.mp (hc.trans (Nat.le_ceil _))
  have hcard : ((logCell S k).card : ℝ)<=(M : ℝ)/(d : ℝ)+1 := by
    have hh := progression_card_le (logCell S k) d r M hbound
      (fun a ha => hmod a (Finset.mem_filter.mp ha).1)
    have hhR : ((logCell S k).card : ℝ)<=((M/d : ℕ) : ℝ)+1 := by exact_mod_cast hh
    exact hhR.trans (add_le_add Nat.cast_div_le le_rfl)
  have hM : (M : ℝ)<=Real.exp ((k : ℝ)+1)+1 :=
    (Nat.ceil_lt_add_one (Real.exp_pos _).le).le
  have hdiv : Real.exp ((k : ℝ)+1)/(d : ℝ)<=
      Real.exp ((k : ℝ)+1-(N : ℝ)/2500) := by
    rw [Real.exp_sub]
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hd
  have hinv : 1/(d : ℝ)<=1 := (div_le_one hdpos).mpr hd1
  have he : Real.exp ((k : ℝ)+1-(N : ℝ)/2500)=
      Real.exp 1*Real.exp ((k : ℝ)-(N : ℝ)/2500) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ <= (M : ℝ)/(d : ℝ)+1 := hcard
    _ <= (Real.exp ((k : ℝ)+1)+1)/(d : ℝ)+1 := by gcongr
    _ <= Real.exp ((k : ℝ)+1-(N : ℝ)/2500)+2 := by rw [add_div]; linarith
    _ <= _ := by rw [he]; nlinarith [Real.exp_one_lt_three]

/-- Complete unit-log partition of a literal population. No cell is omitted. -/
theorem weightedPopulation_eq_cells {u : ℝ} {N K : ℕ}
    (S : Finset ℕ) (hS : S⊆coreBand u N K) :
    weightedPopulation S=∑ k∈Finset.range (3*N+1), weightedPopulation (logCell S k) := by
  have hm (n : ℕ) (hn : n∈S) : Nat.floor (Real.log n)∈Finset.range (3*N+1) := by
    have hh := Nat.floor_le_of_le (show Real.log n<=((3*N : ℕ) : ℝ) by
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using core_log_upper (hS hn))
    exact Finset.mem_range.mpr (by omega)
  exact (Finset.sum_fiberwise_of_maps_to hm
    (fun n => (n : ℝ)^(-(1-epsilon)))).symm

/-- The WHOLE literal progression, across every original count, radial
cell and incidence, has an independent exponentially small weighted size. -/
theorem residue_weightedPopulation {u : ℝ} {N K : ℕ} (hN : 1<=N)
    (S : Finset ℕ) (hS : S⊆coreBand u N K) (d r : ℕ)
    (hd : Real.exp ((N : ℝ)/2500)<=(d : ℝ)) (hmod : ∀ n∈S, n%d=r) :
    weightedPopulation S<=5*(3*N+1)*Real.exp (-(37/100000 : ℝ)*N) := by
  rw [weightedPopulation_eq_cells S hS]
  calc
    _ <= ∑ _k∈Finset.range (3*N+1), 5*Real.exp (-(37/100000 : ℝ)*N) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkR : (k : ℝ)<=3*N := by exact_mod_cast (show k<=3*N by have h := Finset.mem_range.mp hk; omega)
      have hb : weightedPopulation (logCell S k)<=
          ((logCell S k).card : ℝ)*Real.exp (-(1-epsilon)*(k : ℝ)) := by
        unfold weightedPopulation
        calc
          _ <= ∑ _n∈logCell S k, Real.exp (-(1-epsilon)*(k : ℝ)) := by
            apply Finset.sum_le_sum
            intro n hn
            have hnS := hS (Finset.mem_filter.mp hn).1
            have hp : (0 : ℝ)<n := by exact_mod_cast core_label_pos hnS
            have hh := Nat.floor_le (Real.log_natCast_nonneg n)
            rw [(Finset.mem_filter.mp hn).2] at hh
            rw [Real.rpow_def_of_pos hp]
            apply Real.exp_le_exp.mpr
            have he : 0<=1-epsilon := by norm_num [epsilon]
            nlinarith
          _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
      apply hb.trans
      calc
        _ <= 5*Real.exp ((k : ℝ)-(N : ℝ)/2500)*Real.exp (-(1-epsilon)*k) :=
          mul_le_mul_of_nonneg_right (residue_cell_card hN S hS d r hd hmod k) (Real.exp_pos _).le
        _ = 5*Real.exp (epsilon*k-(N : ℝ)/2500) := by
          rw [mul_assoc,← Real.exp_add]
          congr 2
          ring
        _ <= _ := by
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
          norm_num [epsilon] at *
          linarith
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_range,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]; ring

/-- An explicit pointwise price, independent of height, prime count and residue.
The constant is a complete convergent divisor-square sum, not a sampled mass. -/
def sparsePrice (N : ℕ) : ℝ :=
  12*radiusCeiling*Real.sqrt arithmeticMass*(N+1)^2*Real.exp (-(N : ℝ)/16384)

theorem sparsePrice_nonneg (N : ℕ) : 0<=sparsePrice N := by
  unfold sparsePrice
  norm_num [radiusCeiling]
  positivity

/-- The original source growth is beaten by an explicit fixed geometric margin. -/
theorem source_sparse_rate {u : ℝ} (hu : 0<=u) (hU : u<=radiusCeiling) (N : ℕ) :
    (2*u)^(2*N)*Real.exp (-(37/100000 : ℝ)*N)<=
      Real.exp (-(17/100000 : ℝ)*N) := by
  have hb : 2*u<=Real.exp (1/10000 : ℝ) := by
    have he := Real.add_one_le_exp (1/10000 : ℝ)
    norm_num [radiusCeiling] at hU
    linarith
  have hp := pow_le_pow_left₀ (by positivity : 0<=2*u) hb (2*N)
  calc
    _ <= (Real.exp (1/10000 : ℝ))^(2*N)*Real.exp (-(37/100000 : ℝ)*N) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_nat_mul,← Real.exp_add]
      congr 1
      push_cast
      ring

/-- A genuinely pointwise payment of complete literal arithmetic populations.
No mean-height limit, exposed-zero hypothesis or prime-phase premise enters. -/
theorem norm_residue_signal_le {u : ℝ} (hu : 0<=u) (hU : u<=radiusCeiling)
    {N K : ℕ} (hN : 1<=N) (S : Finset ℕ) (hS : S⊆coreBand u N K)
    (d r : ℕ) (hd : Real.exp ((N : ℝ)/2500)<=(d : ℝ))
    (hmod : ∀ n∈S, n%d=r) (y : ℝ) :
    ‖signal S (joinedAmplitude u N K) y‖<=sparsePrice N := by
  have hM := arithmeticMass_nonneg
  have hU0 : 0<=radiusCeiling := by norm_num [radiusCeiling]
  have hNR : (0 : ℝ)<=N := by positivity
  have hsq := (norm_signal_sq_le hu S hS y).trans
    (mul_le_mul_of_nonneg_left (residue_weightedPopulation hN S hS d r hd hmod)
      (mul_nonneg (sq_nonneg _) hM))
  have hpoly : (N : ℝ)^2*(3*N+1)<=3*((N : ℝ)+1)^4 := by
    have h1 : (N : ℝ)^2<=((N : ℝ)+1)^2 := by nlinarith
    have h2 : 3*(N : ℝ)+1<=3*((N : ℝ)+1)^2 := by nlinarith
    calc
      _ <= ((N : ℝ)+1)^2*(3*N+1) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ <= ((N : ℝ)+1)^2*(3*((N : ℝ)+1)^2) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = _ := by ring
  have hexp : Real.exp (-(17/100000 : ℝ)*N)<=Real.exp (-(2/16384 : ℝ)*N) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hb : ‖signal S (joinedAmplitude u N K) y‖^2<=(sparsePrice N)^2 := by
    calc
      _ <= 45*u^2*(N : ℝ)^2*(3*N+1)*arithmeticMass*
          ((2*u)^(2*N)*Real.exp (-(37/100000 : ℝ)*N)) := by
        convert hsq using 1 <;> first | rfl | ring
      _ <= 45*u^2*(N : ℝ)^2*(3*N+1)*arithmeticMass*
          Real.exp (-(17/100000 : ℝ)*N) :=
        mul_le_mul_of_nonneg_left (source_sparse_rate hu hU N) (by positivity)
      _ <= 135*radiusCeiling^2*((N : ℝ)+1)^4*arithmeticMass*
          Real.exp (-(2/16384 : ℝ)*N) := by
        have hu2 := pow_le_pow_left₀ hu hU 2
        calc
          _ <= 45*radiusCeiling^2*((N : ℝ)^2*(3*N+1))*arithmeticMass*
              Real.exp (-(17/100000 : ℝ)*N) := by
            have hh := mul_le_mul_of_nonneg_right hu2
              (show 0<=45*((N : ℝ)^2*(3*N+1))*arithmeticMass*
                Real.exp (-(17/100000 : ℝ)*N) by positivity)
            calc
              _ = u^2*(45*((N : ℝ)^2*(3*N+1))*arithmeticMass*
                  Real.exp (-(17/100000 : ℝ)*N)) := by ring
              _ <= _ := hh
              _ = _ := by ring
          _ <= 45*radiusCeiling^2*(3*((N : ℝ)+1)^4)*arithmeticMass*
              Real.exp (-(2/16384 : ℝ)*N) := by gcongr
          _ = _ := by ring
      _ <= 144*radiusCeiling^2*((N : ℝ)+1)^4*arithmeticMass*
          Real.exp (-(2/16384 : ℝ)*N) := by gcongr; norm_num
      _ = _ := by
        unfold sparsePrice
        rw [mul_pow,mul_pow,mul_pow,mul_pow,Real.sq_sqrt hM,← Real.exp_nat_mul]
        norm_num
        ring_nf
  nlinarith [sparsePrice_nonneg N,norm_nonneg (signal S (joinedAmplitude u N K) y)]

/-- Concrete growing integer modulus. Its sparsity beats the original source
growth; all residue classes together are still the unpaid full carrier. -/
def sparseModulus (N : ℕ) : ℕ := 2^(N/1600+1)

theorem sparseModulus_pos (N : ℕ) : 0<sparseModulus N := by
  unfold sparseModulus
  positivity

theorem sparseModulus_exp_lower (N : ℕ) :
    Real.exp ((N : ℝ)/2500)<=(sparseModulus N : ℝ) := by
  have hdiv : (N : ℝ)<((N/1600+1 : ℕ) : ℝ)*1600 := by
    exact_mod_cast (show N<(N/1600+1)*1600 by have h := Nat.mod_lt N (by norm_num : 0<1600); have he := Nat.mod_add_div N 1600; omega)
  have hlog : (16/25 : ℝ)<=Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (N/1600+1))
  have he : (N : ℝ)/2500<=((N/1600+1 : ℕ) : ℝ)*Real.log 2 := by nlinarith
  calc
    _ <= Real.exp (((N/1600+1 : ℕ) : ℝ)*Real.log 2) := Real.exp_le_exp.mpr he
    _ = _ := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ)<2)]; simp only [sparseModulus,Nat.cast_pow,Nat.cast_ofNat]

/-- A whole literal residue population, retaining every original support mask. -/
def residueBand (u : ℝ) (N K d r : ℕ) : Finset ℕ :=
  (coreBand u N K).filter (fun n => n%d=r)

/-- Already source-normalized joined sum in one actual residue class. -/
def residuePacket (u y : ℝ) (N K d r : ℕ) : ℂ :=
  signal (residueBand u N K d r) (joinedAmplitude u N K) y

theorem norm_residuePacket_le {u : ℝ} (hu : 0<=u) (hU : u<=radiusCeiling)
    {N : ℕ} (hN : 1<=N) (K r : ℕ) (y : ℝ) :
    ‖residuePacket u y N K (sparseModulus N) r‖<=sparsePrice N :=
  norm_residue_signal_le hu hU hN _ (Finset.filter_subset _ _) _ _
    (sparseModulus_exp_lower N) (fun _ hn => (Finset.mem_filter.mp hn).2) y

/-- Exact complete residue ledger for the SAME native carrier. In particular,
no phase correlation between distinct classes is discarded by this identity. -/
theorem joined_eq_residue_sum (u y : ℝ) (N K : ℕ) {d : ℕ} (hd : 0<d) :
    (u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K=
      ∑ r∈Finset.range d, residuePacket u y N K d r := by
  rw [scaled_joined_eq_signal]
  exact (Finset.sum_fiberwise_of_maps_to
    (fun _ _ => Finset.mem_range.mpr (Nat.mod_lt _ hd))
    (fun n => joinedAmplitude u N K n*character n y)).symm

theorem sparsePrice_tendsto : Tendsto sparsePrice atTop (𝓝 0) := by
  have h := (ZetaRieszShiftedHeadBudget.tendsto_quadratic_geometric
    (Real.exp_pos (-(1/16384 : ℝ))).le
    (show Real.exp (-(1/16384 : ℝ))<1 by rw [Real.exp_lt_one_iff]; norm_num)).const_mul
      (12*radiusCeiling*Real.sqrt arithmeticMass)
  simp only [mul_zero] at h
  apply h.congr (fun N => ?_)
  unfold sparsePrice
  rw [← Real.exp_nat_mul]
  have he : Real.exp ((N : ℝ)*-(1/16384))=Real.exp (-(N : ℝ)/16384) := by
    congr 1
    ring
  rw [he]
  ring

/-- Cofinal payment is uniform even in MOVING heights, counts and residues. -/
theorem residuePacket_tendsto {u : ℝ} (hu : 0<=u) (hU : u<=radiusCeiling)
    (heights : ℕ→ℝ) (counts residues : ℕ→ℕ) :
    Tendsto (fun N => residuePacket u (heights N) N (counts N)
      (sparseModulus N) (residues N)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ sparsePrice_tendsto
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact norm_residuePacket_le hu hU hN _ _ _

/-- A literal union of complete residue populations, with no altered support. -/
def residueUnionBand (u : ℝ) (N K d : ℕ) (R : Finset ℕ) : Finset ℕ :=
  (coreBand u N K).filter (fun n => n%d∈R)

/-- Already normalized whole signed sum in the selected residue union. -/
def residueUnionPacket (u y : ℝ) (N K d : ℕ) (R : Finset ℕ) : ℂ :=
  signal (residueUnionBand u N K d R) (joinedAmplitude u N K) y

/-- Exact cross-count/cross-geometry grouping, with each original label once. -/
theorem residueUnionPacket_eq_sum (u y : ℝ) (N K d : ℕ) (R : Finset ℕ) :
    residueUnionPacket u y N K d R=∑ r∈R, residuePacket u y N K d r := by
  have hm (n : ℕ) (hn : n∈residueUnionBand u N K d R) : n%d∈R :=
    (Finset.mem_filter.mp hn).2
  unfold residueUnionPacket signal
  rw [← Finset.sum_fiberwise_of_maps_to hm
    (fun n => joinedAmplitude u N K n*character n y)]
  apply Finset.sum_congr rfl
  intro r hr
  have he : (residueUnionBand u N K d R).filter (fun n => n%d=r)=
      residueBand u N K d r := by
    ext n
    simp only [residueUnionBand,residueBand,Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.1.1,h.2⟩
    · intro h
      exact ⟨⟨h.1,h.2 ▸ hr⟩,h.2⟩
  rw [he]
  rfl

theorem norm_residueUnionPacket_le {u : ℝ} (hu : 0<=u) (hU : u<=radiusCeiling)
    {N : ℕ} (hN : 1<=N) (K : ℕ) (R : Finset ℕ) (y : ℝ) :
    ‖residueUnionPacket u y N K (sparseModulus N) R‖<=R.card*sparsePrice N := by
  rw [residueUnionPacket_eq_sum]
  calc
    _ <= ∑ r∈R, ‖residuePacket u y N K (sparseModulus N) r‖ := norm_sum_le _ _
    _ <= ∑ _r∈R, sparsePrice N := Finset.sum_le_sum (fun _ _ => norm_residuePacket_le hu hU hN _ _ _)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

/-- Explicit price of an exponentially growing but still sparse class union. -/
def unionPrice (N : ℕ) : ℝ :=
  12*radiusCeiling*Real.sqrt arithmeticMass*(N+1)^2*Real.exp (-(N : ℝ)/32768)

theorem norm_sparseUnion_le {u : ℝ} (hu : 0<=u) (hU : u<=radiusCeiling)
    {N : ℕ} (hN : 1<=N) (K : ℕ) (R : Finset ℕ)
    (hR : (R.card : ℝ)<=Real.exp ((N : ℝ)/32768)) (y : ℝ) :
    ‖residueUnionPacket u y N K (sparseModulus N) R‖<=unionPrice N := by
  apply (norm_residueUnionPacket_le hu hU hN K R y).trans
  apply (mul_le_mul_of_nonneg_right hR (sparsePrice_nonneg N)).trans_eq
  unfold unionPrice sparsePrice
  have he : Real.exp ((N : ℝ)/32768)*Real.exp (-(N : ℝ)/16384)=
      Real.exp (-(N : ℝ)/32768) := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ = (12*radiusCeiling*Real.sqrt arithmeticMass*(N+1)^2)*
        (Real.exp ((N : ℝ)/32768)*Real.exp (-(N : ℝ)/16384)) := by ring
    _ = _ := by rw [he]

theorem unionPrice_tendsto : Tendsto unionPrice atTop (𝓝 0) := by
  have h := (ZetaRieszShiftedHeadBudget.tendsto_quadratic_geometric
    (Real.exp_pos (-(1/32768 : ℝ))).le
    (show Real.exp (-(1/32768 : ℝ))<1 by rw [Real.exp_lt_one_iff]; norm_num)).const_mul
      (12*radiusCeiling*Real.sqrt arithmeticMass)
  simp only [mul_zero] at h
  apply h.congr (fun N => ?_)
  unfold unionPrice
  rw [← Real.exp_nat_mul]
  have he : Real.exp ((N : ℝ)*-(1/32768))=Real.exp (-(N : ℝ)/32768) := by congr 1; ring
  rw [he]
  ring

/-- Uniform cofinal decay on ACTUAL exponentially growing selected populations. -/
theorem sparseUnionPacket_tendsto {u : ℝ} (hu : 0<=u) (hU : u<=radiusCeiling)
    (heights : ℕ→ℝ) (counts : ℕ→ℕ) (classes : ℕ→Finset ℕ)
    (hR : ∀ᶠ N in atTop, ((classes N).card : ℝ)<=Real.exp ((N : ℝ)/32768)) :
    Tendsto (fun N => residueUnionPacket u (heights N) N (counts N)
      (sparseModulus N) (classes N)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ unionPrice_tendsto
  filter_upwards [eventually_ge_atTop (1 : ℕ),hR] with N hN hRN
  exact norm_sparseUnion_le hu hU hN _ _ hRN _

/-- The EXACT remaining native signed contribution; no anonymous completion. -/
def residueRestPacket (u y : ℝ) (N K d : ℕ) (R : Finset ℕ) : ℂ :=
  signal ((coreBand u N K).filter (fun n => n%d∉R)) (joinedAmplitude u N K) y

/-- Paid union and unpaid complement add to the original joinedPhysical exactly. -/
theorem joined_eq_union_rest (u y : ℝ) (N K d : ℕ) (R : Finset ℕ) :
    (u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K=
      residueUnionPacket u y N K d R+residueRestPacket u y N K d R := by
  rw [scaled_joined_eq_signal]
  exact (Finset.sum_filter_add_sum_filter_not (coreBand u N K)
    (fun n => n%d∈R) (fun n => joinedAmplitude u N K n*character n y)).symm

/-- The payment also holds along the original cofinal order schedule, with all
other choices moving independently. -/
theorem sparseUnionPacket_tendsto_orders {u : ℝ} (hu : 0<=u) (hU : u<=radiusCeiling)
    (heights : ℕ→ℝ) (orders counts : ℕ→ℕ) (classes : ℕ→Finset ℕ)
    (ho : Tendsto orders atTop atTop)
    (hR : ∀ᶠ j in atTop, ((classes j).card : ℝ)<=Real.exp ((orders j : ℝ)/32768)) :
    Tendsto (fun j => residueUnionPacket u (heights j) (orders j) (counts j)
      (sparseModulus (orders j)) (classes j)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ (unionPrice_tendsto.comp ho)
  filter_upwards [ho.eventually (eventually_ge_atTop (1 : ℕ)),hR] with j hj hRj
  exact norm_sparseUnion_le hu hU hj _ _ hRj _

/-- Removing the paid classes does NOT remove the source: the exact surviving
rest retains the original multiplicity-dependent limit. No ceiling is inferred. -/
theorem residueRestPacket_exact_source (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau≠rho→
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re<=radiusCeiling) (classes : ℕ→Finset ℕ)
    (hR : ∀ᶠ j in atTop, ((classes j).card : ℝ)<=
      Real.exp ((ZetaRieszPrimeCountFrequency.dyadicMomentOrder j : ℝ)/32768)) :
    Tendsto (fun j => residueRestPacket (3/2-rho.1.re) rho.1.im
      (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
      (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)
      (sparseModulus (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)) (classes j)) atTop
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ)+
        (analyticZetaZeroMultiplicity rho : ℂ)^2*
          (ZetaRieszMaskSupport.retainedCost (3/2-rho.1.re) : ℂ))) := by
  have hu : 0<=3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hpaid := sparseUnionPacket_tendsto_orders hu hU (fun _ => rho.1.im)
    ZetaRieszPrimeCountFrequency.dyadicMomentOrder
    ZetaRieszPrimeCountFrequency.dyadicPrimeCount classes
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder hR
  have hs := (ZetaRieszJoinedPhysical.tendsto_joinedPhysical_exact_source rho hrho hexposed hU).sub hpaid
  simp only [sub_zero] at hs
  apply hs.congr' (Eventually.of_forall fun j => ?_)
  rw [joined_eq_union_rest]
  ring

end RiemannGaussian.ZetaRieszCeilingSparseArithmetic
end
