/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCentralPrimeDifference
import RiemannGaussian.ZetaRieszOwnerCountEnergy
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Combined central cost as the moment order grows

All original central labels, counts and masks enter one finite cost. Its
whole dyadic cofactor population and prime sum are bounded, rather than
leaving an unevaluated family of sector costs. The remaining exponential
factor is stated explicitly; a growing majorant is not an eventual floor.
-/

noncomputable section
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszCentralCostGrowth
open Real Filter Topology ZetaRieszJointPrimeEnergy ZetaRieszCenteredPrimeEnergy
  ZetaRieszJointAllocation ZetaRieszPrimeEndpoint ZetaRieszOwnedCells
  ZetaRieszOwnerCountEnergy

/-- Uniform factorial saddle bound, including the square-root saving. -/
theorem radial_peak {N : ℕ} (hN : 0 < N) {T : ℝ} (hT : 0 ≤ T) :
    exp (-T/2)*T^N/N.factorial ≤ (2 : ℝ)^N/sqrt N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < sqrt (N : ℝ) := sqrt_pos.mpr hn
  have hx : 0 ≤ T/(2*N) := by positivity
  have hbase : T/(2*N) ≤ exp (T/(2*N)-1) := by
    linarith only [Real.add_one_le_exp (T/(2*N)-1)]
  have hpow := pow_le_pow_left₀ hx hbase N
  rw [← exp_nat_mul] at hpow
  have he : (N : ℝ)*(T/(2*N)-1)=T/2-N := by field_simp
  rw [he] at hpow
  have hmul := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ exp (-T/2)*(2*(N : ℝ))^N by positivity)
  have he1 : exp (-T/2)*(2*(N : ℝ))^N*(T/(2*N))^N=exp (-T/2)*T^N := by
    rw [mul_assoc,← mul_pow]
    field_simp
  have he2 : exp (-T/2)*(2*(N : ℝ))^N*exp (T/2-N)=
      (2 : ℝ)^N*((N : ℝ)/exp 1)^N := by
    rw [mul_right_comm,← exp_add,show -T/2+(T/2-N)=-(N : ℝ) by ring,
      exp_neg,show exp (N : ℝ)=(exp 1)^N by simp [← exp_nat_mul],div_pow,mul_pow]
    ring
  rw [he1,he2] at hmul
  have hroot : sqrt (N : ℝ) ≤ sqrt (2*Real.pi*N) := by
    apply sqrt_le_sqrt
    nlinarith [Real.pi_gt_three]
  have hfac := (mul_le_mul_of_nonneg_right hroot
    (show 0 ≤ ((N : ℝ)/exp 1)^N by positivity)).trans (Stirling.le_factorial_stirling N)
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < N.factorial) hs).mpr
  calc
    _ ≤ (2 : ℝ)^N*((N : ℝ)/exp 1)^N*sqrt N :=
      mul_le_mul_of_nonneg_right hmul hs.le
    _ = (2 : ℝ)^N*(sqrt N*((N : ℝ)/exp 1)^N) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hfac (by positivity)

/-- The original allocation and full phase obey one joint factorial
weight bound. No factorial-order or prime-count triangle inequality enters. -/
theorem primeWeight_le {u L : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    {N : ℕ} (hN : 0 < N) (hL : (N : ℝ) ≤ L) (A : Finset ℕ) (y : ℝ)
    {n p : ℕ} (hn : 0 < n) (hp : 0 < p)
    (hT : log p+log n ≤ 3*N) :
    |u^(N+1)*primeWeight A L y N n p| ≤
      (3*(2*u)^N/sqrt N)/((n : ℝ)*p) := by
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
  have hrad := radial_peak hN hT0
  have hratio : T/L ≤ 3 := (div_le_iff₀ hL0).mpr (by dsimp [T]; linarith)
  have hnormalized : u^(N+1)*(T/L)*(exp (-T/2)*T^N/N.factorial) ≤
      3*(2*u)^N/sqrt N := by
    calc
      _ ≤ u^(N+1)*3*((2 : ℝ)^N/sqrt N) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hratio (by positivity)) hrad
          (by positivity) (by positivity)
      _ = u*(3*(2*u)^N/sqrt N) := by rw [mul_pow,pow_succ]; ring
      _ ≤ _ := mul_le_of_le_one_left (by positivity) hu1
  have habs : |u^(N+1)*primeWeight A L y N n p| =
      (|1-boundedShare A N (p*n)| * |cos (y*T)|)*
        (u^(N+1)*(T/L)*(exp (-T/2)*T^N/N.factorial))/((n : ℝ)*p) := by
    simp only [primeWeight,abs_div,abs_mul,abs_neg,abs_pow,abs_of_nonneg hu,
      abs_of_pos hL0,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N.factorial),
      abs_of_pos hnR,abs_of_pos hpR,abs_of_pos (exp_pos _)]
    rw [abs_of_nonneg hT0,pow_succ]
    dsimp [T]
    ring
  rw [habs]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hprod : |1-boundedShare A N (p*n)| * |cos (y*T)| ≤ 1 :=
    (mul_le_mul halloc hphase (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  exact (mul_le_of_le_one_left (by positivity) hprod).trans hnormalized


/-- The entire all-count cofactor shell and prime population are paid.
This bounds the existing joint cost, not a newly completed carrier. -/
theorem primeCost_shell_le {E V D : ℝ} (hE : 0 ≤ E) (hV : 0 ≤ V) (hD : 0 ≤ D)
    {M X R : ℕ} (hM : 0 < M) (hX : X ≤ 2*M)
    (N : ℕ) (A S P : Finset ℕ) (Q : ℕ → Finset ℕ) (L y scale : ℝ)
    (hS : S ⊆ Finset.Ioc M (2*M))
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ R ∧ log p ≤ D)
    (hW : ∀ n ∈ S, ∀ p ∈ P, |maskedWeight A Q L y scale N n p| ≤ V/((n : ℝ)*p)) :
    primeCost E X N A S P P Q (fun a p => if a=p then 1 else 0) L y scale ≤
      sqrt (2*E)*V*sqrt D*primeHarmonic R := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hcard : (S.card : ℝ) ≤ M := by
    have h := Finset.card_le_card hS
    rw [Nat.card_Ioc] at h
    have he : 2*M-M=M := by omega
    rw [he] at h
    exact_mod_cast h
  have hone p (hp : p ∈ P) :
      sqrt ((∑ n ∈ S, (maskedWeight A Q L y scale N n p)^2)*E*X*
        centeredEnergy X (hinge L p)) ≤ sqrt (2*E)*V*sqrt D/(p : ℝ) := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).1.pos
    have hw : (∑ n ∈ S, (maskedWeight A Q L y scale N n p)^2) ≤
        V^2/((M : ℝ)*(p : ℝ)^2) := by
      calc
        _ ≤ ∑ _n ∈ S, (V/((M : ℝ)*p))^2 := by
          apply Finset.sum_le_sum
          intro n hn
          have hnm : (M : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp (hS hn)).1.le
          have h := (hW n hn p hp).trans
            (div_le_div_of_nonneg_left hV (by positivity)
              (mul_le_mul_of_nonneg_right hnm hp0.le))
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
        _ = S.card*(V/((M : ℝ)*p))^2 := by simp
        _ ≤ M*(V/((M : ℝ)*p))^2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
        _ = _ := by field_simp
    have hq : centeredEnergy X (hinge L p) ≤ D :=
      (centeredEnergy_le_raw _ _).trans ((ZetaRieszCentralPrimeDifference.hinge_energy L
        (hP p hp).1.one_lt.le X).trans (hP p hp).2.2)
    have hx : (X : ℝ) ≤ 2*M := by exact_mod_cast hX
    have hbud : (∑ n ∈ S, (maskedWeight A Q L y scale N n p)^2)*E*X*
        centeredEnergy X (hinge L p) ≤ 2*E*V^2*D/(p : ℝ)^2 := by
      calc
        _ ≤ (V^2/((M : ℝ)*(p : ℝ)^2))*E*(2*M)*D := by
          have hq0 := centeredEnergy_nonneg X (hinge L p)
          gcongr
        _ = _ := by field_simp
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    rw [div_pow,mul_pow,mul_pow,sq_sqrt (by positivity),sq_sqrt hD]
    exact hbud
  have hsum : primeCost E X N A S P P Q (fun a p => if a=p then 1 else 0) L y scale ≤
      ∑ p ∈ P, sqrt (2*E)*V*sqrt D/(p : ℝ) := by
    unfold primeCost jointCost
    apply Finset.sum_le_sum
    intro p hp
    simpa only [rotate,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,hp,if_true] using hone p hp
  have hsub : P ⊆ (Finset.Icc 1 R).filter Nat.Prime := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(hP p hp).1.pos,(hP p hp).2.1⟩,(hP p hp).1⟩
  calc
    _ ≤ ∑ p ∈ P, sqrt (2*E)*V*sqrt D/(p : ℝ) := hsum
    _ = (sqrt (2*E)*V*sqrt D)*(∑ p ∈ P, 1/(p : ℝ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)) (by positivity)

/-- Canonical dyadic shell of an actual owner cofactor. -/
def shellIndex (m : ℕ) : ℕ := Nat.log 2 (ownerCofactor m-1)

/-- Restrict the original labels, retaining all nested masks exactly. -/
def shell (B : Finset ℕ) (j : ℕ) : Finset ℕ := B.filter (fun m => shellIndex m=j)

/-- The combined central cost includes every radial cofactor shell and all
counts. It uses existing identity coordinates, so optimized costs may be
intersected with it; no numerical optimization is assumed. -/
def centralCost (E : ℝ) (A B : Finset ℕ) (N : ℕ) (L y scale : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (4*N),
    primeCost E (2*2^j) N A (cofactors (shell B j)) (ownerPrimes (shell B j))
      (ownerPrimes (shell B j)) (ownerRows (shell B j))
      (fun a p => if a=p then 1 else 0) L y scale

private theorem cofactor_ne_one {m : ℕ} (hm : Squarefree m) (hc : 3 ≤ m.primeFactors.card) :
    1 < ownerCofactor m := by
  have h := owner_data hm hc
  have hne : ownerCofactor m ≠ 1 := by intro he; simp [he] at h
  have hz := h.2.2.1.ne_zero
  omega

private theorem shell_bounds {B : Finset ℕ} (hB : ∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card)
    {j n : ℕ} (hn : n ∈ cofactors (shell B j)) : 2^j < n ∧ n ≤ 2*2^j := by
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hm,hj⟩ := Finset.mem_filter.mp hm
  have hn := cofactor_ne_one (hB m hm).1 (hB m hm).2
  have hz : ownerCofactor m-1 ≠ 0 := by omega
  have hlo := Nat.pow_log_le_self 2 hz
  have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (ownerCofactor m-1)
  change Nat.log 2 (ownerCofactor m-1)=j at hj
  rw [hj] at hlo hhi
  rw [Nat.pow_succ] at hhi
  constructor <;> omega

private theorem label_le_pow {N m : ℕ} (hm : 0 < m) (hlog : log m ≤ (2029/1000 : ℝ)*N) :
    m ≤ 2^(4*N) := by
  have hl : log (m : ℝ) ≤ log ((2 : ℝ)^(4*N)) := by
    rw [Real.log_pow]
    push_cast
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    nlinarith [Real.log_two_gt_d9]
  have hh := (Real.log_le_log_iff (by exact_mod_cast hm) (by positivity)).mp hl
  exact_mod_cast hh

private theorem shellIndex_lt {N m : ℕ} (hm : Squarefree m) (hc : 3 ≤ m.primeFactors.card)
    (hlog : log m ≤ (2029/1000 : ℝ)*N) : shellIndex m < 4*N := by
  have hn := cofactor_ne_one hm hc
  have hle : ownerCofactor m ≤ m := Nat.div_le_self _ _
  exact Nat.log_lt_of_lt_pow (by omega : ownerCofactor m-1 ≠ 0)
    (by have := label_le_pow (Nat.pos_of_ne_zero hm.ne_zero) hlog; omega)


/-- Explicit combined large-order majorant. Its surviving (2u)^N factor
is greater than one in the restricted right-half-zero campaign. -/
def growthBound (E u : ℝ) (N : ℕ) : ℝ :=
  12*sqrt (6*E)*(2*exp (1/2)*log 4)*N*(1+log (16*N+8))*(2*u)^N

/-- EVERY central prime count and cofactor shell has been summed in this
bound. No finite arithmetic cost sum remains on the right. This is a growth
estimate, not the desired bounded eventual floor or ceiling. -/
theorem centralCost_le_growth {E u L : ℝ} (hE : 0 ≤ E) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    {N : ℕ} (hN : 0 < N) (hL : (N : ℝ) ≤ L) (A B : Finset ℕ) (y : ℝ)
    (hB : ∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card)
    (hlog : ∀ m ∈ B, log m ≤ (2029/1000 : ℝ)*N) :
    centralCost E A B N L y (u^(N+1)) ≤ growthBound E u N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : 0 < sqrt (N : ℝ) := sqrt_pos.mpr hNR
  let V := 3*(2*u)^N/sqrt N
  let R := 2^(4*N)
  have hblock j :
      primeCost E (2*2^j) N A (cofactors (shell B j)) (ownerPrimes (shell B j))
        (ownerPrimes (shell B j)) (ownerRows (shell B j))
        (fun a p => if a=p then 1 else 0) L y (u^(N+1)) ≤
      3*sqrt (6*E)*(2*u)^N*primeHarmonic R := by
    have hSB : ∀ m ∈ shell B j, Squarefree m ∧ 3 ≤ m.primeFactors.card :=
      fun m hm => hB m (Finset.mem_filter.mp hm).1
    have hS : cofactors (shell B j) ⊆ Finset.Ioc (2^j) (2*2^j) :=
      fun _ hn => Finset.mem_Ioc.mpr (shell_bounds hB hn)
    have hP : ∀ p ∈ ownerPrimes (shell B j), p.Prime ∧ p ≤ R ∧ log p ≤ 3*N := by
      intro p hp
      obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hp
      have hmd := owner_data (hSB m hm).1 (hSB m hm).2
      have hmB := (Finset.mem_filter.mp hm).1
      have hpm : largestPrime m ≤ m := by
        calc
          _ ≤ largestPrime m*ownerCofactor m :=
            Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hmd.2.2.1.ne_zero)
          _ = m := hmd.2.1
      refine ⟨hmd.1,hpm.trans (label_le_pow (Nat.pos_of_ne_zero (hSB m hm).1.ne_zero) (hlog m hmB)),?_⟩
      have hh := (log_le_log (show (0 : ℝ) < largestPrime m by exact_mod_cast hmd.1.pos)
        (show (largestPrime m : ℝ) ≤ m by exact_mod_cast hpm)).trans (hlog m hmB)
      linarith
    have hW : ∀ n ∈ cofactors (shell B j), ∀ p ∈ ownerPrimes (shell B j),
        |maskedWeight A (ownerRows (shell B j)) L y (u^(N+1)) N n p| ≤ V/((n : ℝ)*p) := by
      intro n hn p hp
      unfold maskedWeight
      split_ifs with hrow
      · obtain ⟨m,hm,hmp⟩ := Finset.mem_image.mp hrow
        obtain ⟨hm,hmn⟩ := Finset.mem_filter.mp hm
        have hdata := owner_data (hSB m hm).1 (hSB m hm).2
        have hn0 : 0 < n := Nat.pos_of_ne_zero (cofactors_data (shell B j) hSB hn).1.ne_zero
        have hp0 : 0 < p := (hP p hp).1.pos
        have he : p*n=m := by simpa only [hmp,hmn] using hdata.2.1
        apply primeWeight_le hu hu1 hN hL A y hn0 hp0
        have hh : log p+log n=log m := by
          rw [← he,Nat.cast_mul,log_mul (by exact_mod_cast hp0.ne') (by exact_mod_cast hn0.ne')]
        rw [hh]
        have h := hlog m (Finset.mem_filter.mp hm).1
        linarith
      · simp only [abs_zero]
        dsimp [V]
        positivity
    have hb := primeCost_shell_le hE (show 0 ≤ V by dsimp [V]; positivity)
      (show 0 ≤ 3*(N : ℝ) by positivity) (show 0 < 2^j by positivity) le_rfl
      N A (cofactors (shell B j)) (ownerPrimes (shell B j)) (ownerRows (shell B j))
      L y (u^(N+1)) hS hP hW
    apply hb.trans_eq
    have he : sqrt (6*E)=sqrt (2*E)*sqrt 3 := by
      rw [← sqrt_mul (by positivity : 0 ≤ 2*E)]
      congr 1
      ring
    rw [he,sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    dsimp [V]
    field_simp
  have hH : primeHarmonic R ≤ (2*exp (1/2)*log 4)*(1+log (16*N+8)) := by
    apply (primeHarmonic_le_loglog R).trans
    have hlogR : log (R : ℝ) ≤ 4*N := by
      dsimp [R]
      rw [Nat.cast_pow,log_pow]
      push_cast
      nlinarith [log_two_lt_d9]
    have hh : log (4*log (R : ℝ)+8) ≤ log (16*N+8) :=
      log_le_log (by have := log_natCast_nonneg R; positivity) (by linarith)
    gcongr
  calc
    _ ≤ ∑ _j ∈ Finset.range (4*N), 3*sqrt (6*E)*(2*u)^N*primeHarmonic R :=
      Finset.sum_le_sum (fun _ _ => hblock _)
    _ = (4*N)*(3*sqrt (6*E)*(2*u)^N*primeHarmonic R) := by simp
    _ ≤ (4*N)*(3*sqrt (6*E)*(2*u)^N*((2*exp (1/2)*log 4)*(1+log (16*N+8)))) := by
      gcongr
    _ = _ := by unfold growthBound; ring

/-- The cost just bounded really encloses the original full signed central
sum. The universal arithmetic constant is proved but not numerically
specified. Neither prime counts nor actual labels are omitted. -/
theorem exists_central_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (A B : Finset ℕ) (N : ℕ) (L y scale : ℝ),
      (∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card) →
      (∀ m ∈ B, log m ≤ (2029/1000 : ℝ)*N) →
      let J := scale*(∑ m ∈ B, residualCoefficient A L N m*
        zetaPrimeLogKernel N (3/2+Complex.I*y) m).re;
      -centralCost E A B N L y scale ≤ J ∧ J ≤ centralCost E A B N L y scale := by
  obtain ⟨E,hE,hbound⟩ := exists_literal_joint_bounds
  refine ⟨E,hE,fun A B N L y scale hB hlog => ?_⟩
  let f := fun m => residualCoefficient A L N m*zetaPrimeLogKernel N (3/2+Complex.I*y) m
  have hpart : (∑ j ∈ Finset.range (4*N), ∑ m ∈ shell B j, f m)=∑ m ∈ B, f m :=
    Finset.sum_fiberwise_of_maps_to (fun m hm =>
      Finset.mem_range.mpr (shellIndex_lt (hB m hm).1 (hB m hm).2 (hlog m hm))) f
  have hblock j :
      -primeCost E (2*2^j) N A (cofactors (shell B j)) (ownerPrimes (shell B j))
        (ownerPrimes (shell B j)) (ownerRows (shell B j))
        (fun a p => if a=p then 1 else 0) L y scale ≤ scale*(∑ m ∈ shell B j, f m).re ∧
      scale*(∑ m ∈ shell B j, f m).re ≤
        primeCost E (2*2^j) N A (cofactors (shell B j)) (ownerPrimes (shell B j))
          (ownerPrimes (shell B j)) (ownerRows (shell B j))
          (fun a p => if a=p then 1 else 0) L y scale := by
    have hSB : ∀ m ∈ shell B j, Squarefree m ∧ 3 ≤ m.primeFactors.card :=
      fun m hm => hB m (Finset.mem_filter.mp hm).1
    have hS : cofactors (shell B j) ⊆ Finset.Ioc 1 (2*2^j) := by
      intro n hn
      have h := shell_bounds hB hn
      refine Finset.mem_Ioc.mpr ⟨?_,h.2⟩
      have hp : 0 < (2 : ℕ)^j := by positivity
      omega
    have hb := hbound (2*2^j) N A (cofactors (shell B j)) (ownerPrimes (shell B j))
      (ownerPrimes (shell B j)) (ownerRows (shell B j)) (fun a p => if a=p then 1 else 0)
      L y scale (coordinates_identity _) hS (fun _ hn => cofactors_data _ hSB hn)
      (fun _ _ => Finset.image_subset_image (Finset.filter_subset _ _))
      (fun _ _ _ hp => ⟨(ownerRows_data _ hSB hp).1,(ownerRows_data _ hSB hp).2.1⟩)
    have he := ZetaRieszCoupledWindow.sum_owned_products (cofactors (shell B j))
      (ownerRows (shell B j)) f (fun _ hn => (cofactors_data _ hSB hn).1.ne_zero)
      (fun _ _ _ hp => ⟨(ownerRows_data _ hSB hp).1,(ownerRows_data _ hSB hp).2.2⟩)
    rw [owner_labels_eq _ hSB] at he
    simpa only [f,Nat.mul_comm,he] using hb
  have hlo := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range (4*N)) => (hblock j).1)
  have hhi := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range (4*N)) => (hblock j).2)
  simp only [Finset.sum_neg_distrib,← Finset.mul_sum,← Complex.re_sum,hpart] at hlo hhi
  exact ⟨hlo,hhi⟩


open ZetaRieszParityPacket

/-- A concrete bound for the COMBINED central cost as the order grows,
with its exact bridge to both sides of the original whole core. The already
paid outer error is charged once. All remaining factors are scalar functions
of N and u, apart from proved, unevaluated absolute constants. -/
theorem exists_eventual_core_growth_bound :
    ∃ E C : ℝ, 0 < E ∧ 0 ≤ C ∧ ∀ (u : ℝ),
      0 < u → u ≤ ZetaRieszWideOwnerAudit.radiusCeiling →
      ∀ᶠ N : ℕ in atTop, ∀ (y : ℝ) (K : ℕ),
        let B := LogarithmicDeviation.deviationBand ((coreBand u N K).filter Squarefree)
          (1971/1000) (2029/1000) N;
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N;
        let L := SquarefreeVaughanLogSource.length u N;
        let D := centralCost E A B N L y (u^(N+1));
        D ≤ growthBound E u N ∧
        -(D+ZetaRieszLargeOrderCore.rate^N*C) ≤ u^(N+1)*(coreResponse u y N K).re ∧
        u^(N+1)*(coreResponse u y N K).re ≤ D+ZetaRieszLargeOrderCore.rate^N*C := by
  obtain ⟨E,hE,hbound⟩ := exists_central_bounds
  obtain ⟨C,hC,hgeo⟩ := ZetaRieszLargeOrderCore.exists_edge_bound
  refine ⟨E,C,hE,hC,fun u hu hU => ?_⟩
  have hlen := ZetaRieszMaskSupport.eventually_length_lower hu
    (hU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le)
  filter_upwards [hlen,eventually_ge_atTop 1] with N hlen hN y K
  let S := (coreBand u N K).filter Squarefree
  let B := LogarithmicDeviation.deviationBand S (1971/1000) (2029/1000) N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  have hB : ∀ n ∈ B, Squarefree n ∧ 3 ≤ n.primeFactors.card := by
    intro n hn
    have hs := Finset.mem_filter.mp (Finset.mem_filter.mp hn).1
    exact ⟨hs.2,core_count hs.1⟩
  have hlog : ∀ n ∈ B, log n ≤ (2029/1000 : ℝ)*N := fun _ hn =>
    (Finset.mem_filter.mp hn).2.2
  have hLN : (N : ℝ) ≤ L := by
    dsimp [L]
    have := Nat.cast_nonneg (α := ℝ) N
    linarith
  have hu1 : u ≤ 1 := by
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at hU
    linarith
  have hcost := centralCost_le_growth hE.le hu.le hu1
    (by omega : 0 < N) hLN A B y hB hlog
  have hb := hbound A B N L y (u^(N+1)) hB hlog
  have hg := hgeo N S (residualCoefficient A L N)
    (fun n _ => norm_residualCoefficient_le A (SquarefreeVaughanLogSource.length_pos u N) N n)
    y u hu.le hU
  have he := (Complex.abs_re_le_norm _).trans hg
  dsimp only [S,A,L] at he
  rw [← core_eq_squarefree] at he
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,Complex.sub_re,mul_sub] at he
  have hlo := (abs_le.mp he).1
  have hhi := (abs_le.mp he).2
  dsimp only [A,B,S,L] at hcost hb
  dsimp only
  exact ⟨hcost,by linarith only [hb.1,hlo],by linarith only [hb.2,hhi]⟩

/-- Honest rate audit: this combined MAJORANT still diverges for u>1/2.
This does NOT say that the actual signed sum or optimized cost diverges.
A further cancellation rate is needed; fixed percentage savings cannot
turn this particular large-order bound into the required eventual floors. -/
theorem growthBound_tendsto_atTop {E u : ℝ} (hE : 0 < E) (hu : 1/2 < u) :
    Tendsto (growthBound E u) atTop atTop := by
  let C := 12*sqrt (6*E)*(2*exp (1/2)*log 4)
  have hC : 0 < C := by dsimp [C]; positivity
  have ht := (tendsto_pow_atTop_atTop_of_one_lt (show 1 < 2*u by linarith)).const_mul_atTop hC
  apply Filter.tendsto_atTop_mono' atTop ?_ ht
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hl : 0 ≤ log (16*(N : ℝ)+8) := log_nonneg (by linarith)
  have hf : 1 ≤ (N : ℝ)*(1+log (16*(N : ℝ)+8)) := by nlinarith
  change C*(2*u)^N ≤ C*N*(1+log (16*N+8))*(2*u)^N
  nlinarith only [mul_le_mul_of_nonneg_left hf
    (show 0 ≤ C*(2*u)^N by positivity)]


/-- Exact rational bounds on the remaining exponential growth at the
largest campaign radius. This quantifies the rate a further saving must beat. -/
theorem ceiling_growth_exponent :
    (99/1000000 : ℝ) < log (2*ZetaRieszWideOwnerAudit.radiusCeiling) ∧
      log (2*ZetaRieszWideOwnerAudit.radiusCeiling) < (1/10000 : ℝ) := by
  have hlo := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 1/20001)
    (by norm_num : (1/20001 : ℝ) < 1) 1
  norm_num [Finset.sum_range_succ] at hlo
  have hhi := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 10001/10000)
    (by norm_num : (10001/10000 : ℝ) ≠ 1)
  norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at *
  constructor <;> linarith

/-- The global coupled bound saves a factor of order log(N)/N against
the quadratic-polynomial saddle scale. This is a proved asymptotic saving
for the combined allowance, but it leaves the exponential factor untouched. -/
theorem growthBound_div_quadratic_tendsto_zero (E : ℝ) {u : ℝ} (hu : 0 < u) :
    Tendsto (fun N : ℕ => growthBound E u N/((N : ℝ)^2*(2*u)^N)) atTop (𝓝 0) := by
  let C := 12*sqrt (6*E)*(2*exp (1/2)*log 4)
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun N : ℕ => 1/(N : ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hcast
  have h8 : Tendsto (fun N : ℕ => 8/(N : ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hcast
  have hx0 : Tendsto (fun N : ℕ => 16*(N : ℝ)) atTop atTop :=
    hcast.const_mul_atTop (by norm_num : (0 : ℝ) < 16)
  have hx : Tendsto (fun N : ℕ => 16*(N : ℝ)+8) atTop atTop := by
    simpa only [add_comm] using
      (show Tendsto (fun _ : ℕ => (8 : ℝ)) atTop (𝓝 8) from tendsto_const_nhds).add_atTop hx0
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hx
  have hlin : Tendsto (fun N : ℕ => 16+8/(N : ℝ)) atTop (𝓝 16) := by
    simpa only [add_zero] using (show Tendsto (fun _ : ℕ => (16 : ℝ)) atTop (𝓝 16) from
      tendsto_const_nhds).add h8
  have ht := (h1.add (hl.mul hlin)).const_mul C
  simp only [zero_mul,mul_zero,zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hp : (2*u)^N ≠ 0 := pow_ne_zero _ (by positivity)
  have hx0 : 16*(N : ℝ)+8 ≠ 0 := by positivity
  dsimp [growthBound,C]
  field_simp


/-- The actual combined cost, with arbitrary moving heights and count
cutoffs, is little-o of the quadratic saddle scale. This is the proved
polynomial saving for the entire central range, not a packet model. -/
theorem centralCost_div_quadratic_tendsto_zero {E u : ℝ} (hE : 0 ≤ E)
    (hu : 0 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℕ → ℝ) (K : ℕ → ℕ) :
    Tendsto (fun N : ℕ =>
      centralCost E (ZetaRieszAnnulusJoint.intermediatePrimes u N)
        (LogarithmicDeviation.deviationBand ((coreBand u N (K N)).filter Squarefree)
          (1971/1000) (2029/1000) N) N (SquarefreeVaughanLogSource.length u N)
        (y N) (u^(N+1))/((N : ℝ)^2*(2*u)^N)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun N : ℕ => growthBound E u N/((N : ℝ)^2*(2*u)^N))
    ?_ (growthBound_div_quadratic_tendsto_zero E hu)
  filter_upwards [ZetaRieszMaskSupport.eventually_length_lower hu
    (hU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le),eventually_ge_atTop 1]
    with N hlen hN
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let B := LogarithmicDeviation.deviationBand ((coreBand u N (K N)).filter Squarefree)
    (1971/1000) (2029/1000) N
  let L := SquarefreeVaughanLogSource.length u N
  have hB : ∀ n ∈ B, Squarefree n ∧ 3 ≤ n.primeFactors.card := by
    intro n hn
    have hs := Finset.mem_filter.mp (Finset.mem_filter.mp hn).1
    exact ⟨hs.2,core_count hs.1⟩
  have hlog : ∀ n ∈ B, log n ≤ (2029/1000 : ℝ)*N := fun _ hn =>
    (Finset.mem_filter.mp hn).2.2
  have hLN : (N : ℝ) ≤ L := by dsimp [L]; have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hu1 : u ≤ 1 := by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at hU; linarith
  have hc := centralCost_le_growth hE hu.le hu1 (by omega : 0 < N) hLN A B (y N) hB hlog
  have hpos : 0 ≤ centralCost E A B N L (y N) (u^(N+1)) := by
    unfold centralCost primeCost jointCost
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sqrt_nonneg _))
  change ‖centralCost E A B N L (y N) (u^(N+1))/((N : ℝ)^2*(2*u)^N)‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg hpos (by positivity))]
  exact div_le_div_of_nonneg_right hc (by positivity)

end RiemannGaussian.ZetaRieszCentralCostGrowth
