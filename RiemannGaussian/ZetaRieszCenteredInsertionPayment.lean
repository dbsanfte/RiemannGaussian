/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszClippedInsertionFloor
import RiemannGaussian.ZetaRieszInnerHingeGapPayment

/-!
# Global quadratic cost for centered insertion families

The exact factorial amplitude and full phase are differentiated jointly.
A proved zero first log-gap moment then gives a squared-gap transport
price. Summing over distinct original labels costs one harmonic factor,
independently of the insertion counts and the number of candidates.
At gaps `exp(-N/5000)` the total source-scaled transport has the explicit
geometric factor `exp(-N/4000)`.

Prime inventory, coverage, column capacity and literal support are not
asserted. This pays the transport of qualifying families, not their
unmatched signed remainder or the independent native floor.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszCenteredInsertionPayment
open ZetaRieszSmoothOwnerDiscrepancy ZetaRieszWideOwnerAudit
open ZetaRieszClippedInsertionFloor

private def radialD (N : ℕ) (T : ℝ) : ℝ :=
  exp (-T/2)*(((N : ℝ)+1)*T^N-T^(N+1)/2)/(N.factorial : ℝ)

private def radialDD (N : ℕ) (T : ℝ) : ℝ :=
  exp (-T/2)*(((N : ℝ)+1)*N*T^(N-1)-((N : ℝ)+1)*T^N+T^(N+1)/4)/
    (N.factorial : ℝ)

private theorem radialD_deriv (N : ℕ) (T : ℝ) :
    HasDerivAt (radialD N) (radialDD N T) T := by
  have hd := (((((hasDerivAt_id T).pow N).const_mul ((N : ℝ)+1)).sub
    (((hasDerivAt_id T).pow (N+1)).div_const 2)).mul
      (((hasDerivAt_id T).neg.div_const 2).exp)).div_const (N.factorial : ℝ)
  convert! hd using 1
  · ext t
    dsimp [radialD]
    ring
  · dsimp [radialDD]
    simp only [Nat.cast_add,Nat.cast_one]
    ring

private theorem monomial_bound (k : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    exp (-T/2)*T^k/(k.factorial : ℝ) ≤ (2 : ℝ)^k := by
  have h := Real.pow_div_factorial_le_exp (T/2) (by positivity) k
  have hh := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ exp (-T/2)*2^k)
  have he : exp (-T/2)*exp (T/2)=1 := by
    rw [← exp_add,show -T/2+T/2=0 by ring,exp_zero]
  have hp : (2 : ℝ)^k*(T/2)^k=T^k := by rw [← mul_pow]; congr 1; ring
  calc
    _ = (exp (-T/2)*2^k)*((T/2)^k/(k.factorial : ℝ)) := by rw [← hp]; ring
    _ ≤ (exp (-T/2)*2^k)*exp (T/2) := hh
    _ = 2^k*(exp (-T/2)*exp (T/2)) := by ring
    _ = _ := by rw [he,mul_one]

private theorem radialDD_bound {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hT : 0 ≤ T) :
    |radialDD N T| ≤ radialCap N := by
  have hm := monomial_bound (N-1) hT
  have h1 := (radial_bounds N hT).2
  have hf : (N.factorial : ℝ) = N*((N-1).factorial : ℝ) := by
    have he : N=(N-1)+1 := by omega
    conv_lhs => rw [he,Nat.factorial_succ]
    norm_cast
    congr 1
    omega
  have hn0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hf0 : ((N-1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (N-1)
  have hc1 : |exp (-T/2)*((N : ℝ)+1)*N*T^(N-1)/(N.factorial : ℝ)| ≤
      ((N : ℝ)+1)*2^(N-1) := by
    rw [abs_of_nonneg (by positivity),hf]
    have he : exp (-T/2)*((N : ℝ)+1)*N*T^(N-1)/(N*((N-1).factorial : ℝ)) =
        ((N : ℝ)+1)*(exp (-T/2)*T^(N-1)/((N-1).factorial : ℝ)) := by field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_left hm (by positivity)
  have hc2 : |exp (-T/2)*((N : ℝ)+1)*T^N/(N.factorial : ℝ)| ≤
      ((N : ℝ)+1)*2^N := by
    have hb := monomial_bound N hT
    rw [abs_of_nonneg (by positivity)]
    calc
      _ = ((N : ℝ)+1)*(exp (-T/2)*T^N/(N.factorial : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)
  have hc3 : |radial N T/4| ≤ radialCap N/4 := by
    rw [abs_of_nonneg (by unfold radial; positivity)]
    exact div_le_div_of_nonneg_right h1 (by norm_num)
  have he : radialDD N T =
      exp (-T/2)*((N : ℝ)+1)*N*T^(N-1)/(N.factorial : ℝ)-
        exp (-T/2)*((N : ℝ)+1)*T^N/(N.factorial : ℝ)+radial N T/4 := by
    dsimp [radialDD,radial]
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  apply (add_le_add (abs_sub _ _) le_rfl).trans
  apply (add_le_add (add_le_add hc1 hc2) hc3).trans_eq
  unfold radialCap
  have hp : (2 : ℝ)^(N+1)=4*2^(N-1) := by
    rw [show N+1=(N-1)+2 by omega,pow_add]
    norm_num
    ring
  have hp' : (2 : ℝ)^N=2*2^(N-1) := by
    conv_lhs => rw [show N=(N-1)+1 by omega,pow_succ]
    ring
  rw [hp,hp']
  ring

/-- The existing full factorial amplitude with its actual total-log phase.
The hinge coefficient is kept in the joined clipped weights. -/
def amplitude (N : ℕ) (L y T : ℝ) : ℂ :=
  ((radial N T/L : ℝ) : ℂ)*Complex.exp (-((1 : ℂ)+Complex.I*y)*(T : ℂ))

private def amplitudeD (N : ℕ) (L y T : ℝ) : ℂ :=
  (((radialD N T/L : ℝ) : ℂ)-((1 : ℂ)+Complex.I*y)*((radial N T/L : ℝ) : ℂ))*
    Complex.exp (-((1 : ℂ)+Complex.I*y)*(T : ℂ))

private def amplitudeDD (N : ℕ) (L y T : ℝ) : ℂ :=
  (((radialDD N T/L : ℝ) : ℂ)-2*((1 : ℂ)+Complex.I*y)*((radialD N T/L : ℝ) : ℂ)+
    ((1 : ℂ)+Complex.I*y)^2*((radial N T/L : ℝ) : ℂ))*
      Complex.exp (-((1 : ℂ)+Complex.I*y)*(T : ℂ))

private theorem phase_deriv (y T : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (-((1 : ℂ)+Complex.I*y)*(t : ℂ)))
      (-((1 : ℂ)+Complex.I*y)*Complex.exp (-((1 : ℂ)+Complex.I*y)*(T : ℂ))) T := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := T)).const_mul (-((1 : ℂ)+Complex.I*y))).cexp
  simpa [Complex.ofRealCLM_apply,mul_comm] using h

private theorem amplitude_deriv (N : ℕ) (L y T : ℝ) :
    HasDerivAt (amplitude N L y) (amplitudeD N L y T) T := by
  have h := (((radial_deriv N T).div_const L).ofReal_comp).mul
    (phase_deriv y T)
  convert! h using 1
  dsimp [amplitude,amplitudeD,radialD]
  push_cast
  ring

private theorem amplitudeD_deriv (N : ℕ) (L y T : ℝ) :
    HasDerivAt (amplitudeD N L y) (amplitudeDD N L y T) T := by
  have h := ((((radialD_deriv N T).div_const L).ofReal_comp).sub
    ((((radial_deriv N T).div_const L).ofReal_comp).const_mul
      ((1 : ℂ)+Complex.I*y))).mul (phase_deriv y T)
  convert! h using 1
  dsimp [amplitudeDD,amplitudeD,radialD]
  push_cast
  ring

private theorem amplitudeDD_bound {N : ℕ} (hN : 1 ≤ N) {L T : ℝ}
    (hL : 1 ≤ L) (hT : 0 ≤ T) (y : ℝ) :
    ‖amplitudeDD N L y T‖ ≤ (2+|y|)^2*radialCap N*exp (-T) := by
  have hL0 : 0 < L := by linarith
  have hr0 := radialCap_nonneg N
  have hc : ‖(1 : ℂ)+Complex.I*y‖ ≤ 1+|y| := by
    simpa only [norm_one,norm_mul,Complex.norm_I,Complex.norm_real,
      Real.norm_eq_abs,one_mul] using norm_add_le (1 : ℂ) (Complex.I*y)
  have hr : ‖((radial N T/L : ℝ) : ℂ)‖ ≤ radialCap N := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (radial_bounds N hT).1 hL0.le)]
    exact (div_le_div_of_nonneg_right (radial_bounds N hT).2 hL0.le).trans
      (div_le_self (radialCap_nonneg N) hL)
  have hd : ‖((radialD N T/L : ℝ) : ℂ)‖ ≤ radialCap N := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos hL0]
    exact (div_le_div_of_nonneg_right (radial_deriv_bound N hT) hL0.le).trans
      (div_le_self (radialCap_nonneg N) hL)
  have hdd : ‖((radialDD N T/L : ℝ) : ℂ)‖ ≤ radialCap N := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos hL0]
    exact (div_le_div_of_nonneg_right (radialDD_bound hN hT) hL0.le).trans
      (div_le_self (radialCap_nonneg N) hL)
  have hn : ‖((radialDD N T/L : ℝ) : ℂ)-
      2*((1 : ℂ)+Complex.I*y)*((radialD N T/L : ℝ) : ℂ)+
        ((1 : ℂ)+Complex.I*y)^2*((radial N T/L : ℝ) : ℂ)‖ ≤
      radialCap N+2*(1+|y|)*radialCap N+(1+|y|)^2*radialCap N := by
    apply (norm_add_le _ _).trans
    apply (add_le_add (norm_sub_le _ _) le_rfl).trans
    rw [norm_mul,norm_mul,norm_mul,norm_pow]
    norm_num only [Complex.norm_ofNat]
    gcongr
  unfold amplitudeDD
  rw [norm_mul,Complex.norm_exp]
  have he : (-((1 : ℂ)+Complex.I*y)*(T : ℂ)).re = -T := by simp
  rw [he]
  exact (mul_le_mul_of_nonneg_right hn (exp_nonneg _)).trans_eq (by ring)

/-- A genuine centered family pays the SQUARE of its actual gap radius,
with the factorial kernel and full phase already included. -/
theorem centered_amplitude_cost {ι : Type*} (S : Finset ι) (c t : ι → ℝ)
    {N : ℕ} (hN : 1 ≤ N) {L T ρ : ℝ} (hL : 1 ≤ L)
    (hT : 1 ≤ T) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (y : ℝ)
    (hc : ∀ i∈S,0 ≤ c i) (ht : ∀ i∈S,|t i-T| ≤ ρ)
    (hcenter : (∑ i∈S,c i*(t i-T))=0) :
    ‖∑ i∈S,(c i : ℂ)*(amplitude N L y T-amplitude N L y (t i))‖ ≤
      3*(2+|y|)^2*radialCap N*exp (-T)*ρ^2*(∑ i∈S,c i) := by
  have hv v (hv : v ∈ Set.Icc (T-ρ) (T+ρ)) : 0 ≤ v := by linarith [hv.1]
  have hr0 := radialCap_nonneg N
  have hb v (hv : v ∈ Set.Icc (T-ρ) (T+ρ)) :
      ‖amplitudeDD N L y v‖ ≤ 3*(2+|y|)^2*radialCap N*exp (-T) := by
    have he : exp (-v) ≤ 3*exp (-T) := by
      calc
        _ ≤ exp (1-T) := exp_le_exp.mpr (by linarith [hv.1])
        _ = exp 1*exp (-T) := by rw [← exp_add]; congr 1
        _ ≤ _ := mul_le_mul_of_nonneg_right exp_one_lt_three.le (exp_nonneg _)
    exact (amplitudeDD_bound hN hL (by linarith [hv.1]) y).trans
      ((mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (by ring))
  exact centred_transport_norm_quadratic S c t (amplitude N L y)
    (amplitudeD N L y) (amplitudeDD N L y) hρ (by positivity)
    (fun v _ => amplitude_deriv N L y v) (fun v _ => amplitudeD_deriv N L y v)
    hb hc ht hcenter

/-- Centering permits FIVE times the earlier gap radius in the exponent:
its squared price still beats the entire positive source envelope. -/
theorem centered_source_rate {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (N : ℕ) :
    u^(N+1)*2^(N+1)*(exp (-(N : ℝ)/5000))^2 ≤
      2*radiusCeiling*exp (-(N : ℝ)/4000) := by
  have hb : 2*u ≤ exp (1/10000 : ℝ) := by
    have h := add_one_le_exp (1/10000 : ℝ)
    norm_num [radiusCeiling] at hU
    linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 2*u) hb N
  rw [← exp_nat_mul] at hp
  have he : (exp (-(N : ℝ)/5000))^2=exp (-2*(N : ℝ)/5000) := by
    rw [← exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [he]
  have hr := mul_le_mul_of_nonneg_right hp (exp_nonneg (-2*(N : ℝ)/5000))
  rw [← exp_add] at hr
  have hs : exp ((N : ℝ)*(1/10000)+(-2*(N : ℝ)/5000)) ≤ exp (-(N : ℝ)/4000) :=
    exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) N])
  calc
    _ = 2*u*((2*u)^N*exp (-2*(N : ℝ)/5000)) := by rw [← mul_pow,pow_succ]; ring
    _ ≤ 2*u*exp (-(N : ℝ)/4000) := mul_le_mul_of_nonneg_left (hr.trans hs) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (exp_nonneg _)

/-- Price ALL qualifying centered families on distinct ORIGINAL labels.
There is no candidate/count multiplicity in the global constant. Support,
clipped coverage and column capacity remain application obligations. -/
theorem global_centered_cost {ι : Type*} (D : Finset ℕ) (S : ℕ → Finset ι)
    (c t : ℕ → ι → ℝ) {N Q : ℕ} (hN : 1 ≤ N)
    (hD : D ⊆ Finset.Icc 1 Q) (hlogQ : log Q ≤ 3*((N : ℝ)+1))
    {L u : ℝ} (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (y : ℝ)
    (hlog : ∀ n∈D,1 ≤ log n)
    (hc : ∀ n∈D,∀ i∈S n,0 ≤ c n i)
    (hmass : ∀ n∈D,(∑ i∈S n,c n i) ≤ 3*((N : ℝ)+1))
    (ht : ∀ n∈D,∀ i∈S n,|t n i-log n| ≤ exp (-(N : ℝ)/5000))
    (hcenter : ∀ n∈D,(∑ i∈S n,c n i*(t n i-log n))=0) :
    u^(N+1)*(∑ n∈D,‖∑ i∈S n,(c n i : ℂ)*
      (amplitude N L y (log n)-amplitude N L y (t n i))‖) ≤
      72*radiusCeiling*(2+|y|)^2*((N : ℝ)+1)^3*exp (-(N : ℝ)/4000) := by
  let C := 9*(2+|y|)^2*radialCap N*((N : ℝ)+1)*(exp (-(N : ℝ)/5000))^2
  have hr0 := radialCap_nonneg N
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hg : exp (-(N : ℝ)/5000) ≤ 1 := exp_le_one_iff.mpr (by
    nlinarith [Nat.cast_nonneg (α := ℝ) N])
  have he n (hn : n∈D) :
      ‖∑ i∈S n,(c n i : ℂ)*(amplitude N L y (log n)-amplitude N L y (t n i))‖ ≤
        C*(n : ℝ)⁻¹ := by
    have h := centered_amplitude_cost (S n) (c n) (t n) hN hL (hlog n hn)
      (exp_nonneg _) hg y (hc n hn) (ht n hn) (hcenter n hn)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp (hD hn)).1
    rw [exp_neg,exp_log hn0] at h
    exact (h.trans (mul_le_mul_of_nonneg_left (hmass n hn) (by positivity))).trans_eq
      (by dsimp [C]; ring)
  have hb : (∑ n∈D,‖∑ i∈S n,(c n i : ℂ)*
      (amplitude N L y (log n)-amplitude N L y (t n i))‖) ≤ C*(1+log Q) := by
    calc
      _ ≤ ∑ n∈D,C*(n : ℝ)⁻¹ := Finset.sum_le_sum he
      _ = C*∑ n∈D,(n : ℝ)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((Finset.sum_le_sum_of_subset_of_nonneg hD (by intros; positivity)).trans
          (by simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
            using harmonic_le_one_add_log Q)) hC
  have hcap : 1+log Q ≤ 4*((N : ℝ)+1) := by linarith [Nat.cast_nonneg (α := ℝ) N]
  calc
    _ ≤ u^(N+1)*C*(4*((N : ℝ)+1)) := by
      have h := mul_le_mul_of_nonneg_left hcap (mul_nonneg (pow_nonneg hu (N+1)) hC)
      have hb' := mul_le_mul_of_nonneg_left hb (pow_nonneg hu (N+1))
      exact hb'.trans (by convert! h using 1; ring)
    _ = (36*(2+|y|)^2*((N : ℝ)+1)^3)*
        (u^(N+1)*2^(N+1)*(exp (-(N : ℝ)/5000))^2) := by
      dsimp [C,radialCap]
      ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left (centered_source_rate hu hU N)
      (by positivity : 0 ≤ 36*(2+|y|)^2*((N : ℝ)+1)^3)).trans_eq (by ring)

/-- The total centered transport is source-o(1) at every fixed height.
No inventory, coverage or unmatched-label bound is implied. -/
theorem tendsto_centered_price (y : ℝ) :
    Tendsto (fun N : ℕ => 72*radiusCeiling*(2+|y|)^2*((N : ℝ)+1)^3*
      exp (-(N : ℝ)/4000)) atTop (𝓝 0) := by
  have h := ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 3
    (exp_pos (-(1/4000 : ℝ))) (exp_lt_one_iff.mpr (by norm_num : -(1/4000 : ℝ)<0))
  have he (N : ℕ) : exp (-(1/4000 : ℝ))^N=exp (-(N : ℝ)/4000) := by
    rw [← exp_nat_mul]
    congr 1
    ring
  convert! h.const_mul (72*radiusCeiling*(2+|y|)^2) using 1
  · ext N
    rw [he]
    ring
  · simp

/-- A complete centered coefficient cover has a direct one-sided signed
floor with the global geometric price. The arbitrary unit multiplier
retains the original cofactor parity. Literal membership, allocation and
non-reused partner capacity still need their own native ledger proofs. -/
theorem global_centered_floor {ι : Type*} (D : Finset ℕ) (S : ℕ → Finset ι)
    (c t : ℕ → ι → ℝ) (τ : ℕ → ℝ) (σ : ℕ → ℂ)
    {N Q : ℕ} (hN : 1 ≤ N) (hD : D ⊆ Finset.Icc 1 Q)
    (hlogQ : log Q ≤ 3*((N : ℝ)+1)) {L u : ℝ} (hL : 1 ≤ L)
    (hu : 0 ≤ u) (hU : u ≤ radiusCeiling) (y : ℝ)
    (hlog : ∀ n∈D,1 ≤ log n) (hc : ∀ n∈D,∀ i∈S n,0 ≤ c n i)
    (hmass : ∀ n∈D,(∑ i∈S n,c n i) ≤ 3*((N : ℝ)+1))
    (ht : ∀ n∈D,∀ i∈S n,|t n i-log n| ≤ exp (-(N : ℝ)/5000))
    (hcenter : ∀ n∈D,(∑ i∈S n,c n i*(t n i-log n))=0)
    (hcover : ∀ n∈D,τ n=∑ i∈S n,c n i) (hσ : ∀ n∈D,‖σ n‖ ≤ 1) :
    -(72*radiusCeiling*(2+|y|)^2*((N : ℝ)+1)^3*exp (-(N : ℝ)/4000)) ≤
      u^(N+1)*(∑ n∈D,σ n*((τ n : ℂ)*amplitude N L y (log n)-
        ∑ i∈S n,(c n i : ℂ)*amplitude N L y (t n i))).re := by
  let H := fun n => ∑ i∈S n,(c n i : ℂ)*
    (amplitude N L y (log n)-amplitude N L y (t n i))
  have he n (hn : n∈D) :
      (τ n : ℂ)*amplitude N L y (log n)-
        ∑ i∈S n,(c n i : ℂ)*amplitude N L y (t n i)=H n := by
    dsimp [H]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul,← Complex.ofReal_sum,← hcover n hn]
  have hr n (hn : n∈D) : -‖H n‖ ≤ (σ n*H n).re := by
    have hn' : ‖σ n*H n‖ ≤ ‖H n‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hσ n hn)
    exact (neg_le_neg hn').trans (abs_le.mp (Complex.abs_re_le_norm (σ n*H n))).1
  have hs : -(∑ n∈D,‖H n‖) ≤ (∑ n∈D,σ n*H n).re := by
    rw [Complex.re_sum,← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum hr
  have hp := global_centered_cost D S c t hN hD hlogQ hL hu hU y hlog hc hmass ht hcenter
  have hs' := mul_le_mul_of_nonneg_left hs (pow_nonneg hu (N+1))
  have hleft : -(72*radiusCeiling*(2+|y|)^2*((N : ℝ)+1)^3*exp (-(N : ℝ)/4000)) ≤
      u^(N+1)*(-(∑ n∈D,‖H n‖)) := by
    simpa only [H,mul_neg] using neg_le_neg hp
  rw [Finset.sum_congr rfl (fun n hn => congrArg (fun z => σ n*z) (he n hn))]
  exact hleft.trans hs'

end RiemannGaussian.ZetaRieszCenteredInsertionPayment
