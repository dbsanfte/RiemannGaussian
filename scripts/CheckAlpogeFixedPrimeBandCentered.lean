import CheckAlpogeFixedPrimeBandMobius

/-! # The plain Möbius sum between the third and fourth powers -/

noncomputable section
namespace RiemannGaussian.AlpogeMined
open Real Finset Filter

/-- Total unit-density reciprocal ramp up to a real cutoff. -/
def fixedBandUnitRamp (y : ℝ) : ℝ :=
  y * (harmonic ⌊y⌋₊ : ℝ) - ⌊y⌋₊

private def unitRampMain (y : ℝ) : ℝ :=
  y*log y + (eulerMascheroniConstant-1)*y + 1/2

theorem fixedBandUnitRamp_sum {y Y : ℝ} (hy : 0 ≤ y) (hyY : y ≤ Y) :
    (∑ k ∈ Ioc 0 ⌊Y⌋₊, max (y/k-1) 0) = fixedBandUnitRamp y := by
  let q := ⌊y⌋₊
  have ht : (∑ k ∈ Ioc 0 q, max (y/k-1) 0) = ∑ k ∈ Ioc 0 ⌊Y⌋₊, max (y/k-1) 0 := by
    apply sum_subset (Ioc_subset_Ioc_right (Nat.floor_mono hyY))
    intro k hk h
    have hk0 := (mem_Ioc.mp hk).1
    have hq : q < k := lt_of_not_ge (fun hq => h (mem_Ioc.mpr ⟨hk0,hq⟩))
    exact max_eq_right (sub_nonpos.mpr ((div_le_one (Nat.cast_pos.mpr hk0)).mpr ((Nat.floor_lt hy).mp hq).le))
  rw [← ht]
  have hi : (∑ k ∈ Ioc 0 q, (k:ℝ)⁻¹) = (harmonic q:ℝ) := by
    rw [harmonic_eq_sum_Icc,show Ioc 0 q = Icc 1 q by ext k; simp only [mem_Ioc,mem_Icc]; omega]
    push_cast
    rfl
  calc
    _ = ∑ k ∈ Ioc 0 q, (y*(k:ℝ)⁻¹-1) := by
      apply sum_congr rfl
      intro k hk
      have hky := (Nat.cast_le.mpr (mem_Ioc.mp hk).2 : (k:ℝ) ≤ q).trans (Nat.floor_le hy)
      rw [max_eq_left (sub_nonneg.mpr ((one_le_div (Nat.cast_pos.mpr (mem_Ioc.mp hk).1)).mpr hky)),div_eq_mul_inv]
    _ = _ := by simp only [sum_sub_distrib,← mul_sum,hi,sum_const,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul,mul_one,fixedBandUnitRamp,q]

private theorem unitRamp_error {y : ℝ} (hy : 1 ≤ y) :
    |fixedBandUnitRamp y-unitRampMain y| ≤ 4/y := by
  let q := ⌊y⌋₊
  have hq : 1 ≤ q := Nat.le_floor (by exact_mod_cast hy)
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hq₀ := zero_lt_one.trans_le hqR
  have hy₀ := zero_lt_one.trans_le hy
  have hqy : (q:ℝ) ≤ y := Nat.floor_le hy₀.le
  have hyq : y < (q:ℝ)+1 := Nat.lt_floor_add_one _
  have hy2 : y ≤ 2*q := by linarith
  obtain ⟨hl,hu⟩ := AlpogeZetaSamples.harmonic_half_bounds hq
  let A := y*((harmonic q:ℝ)-log q-eulerMascheroniConstant)
  have hA : 1/2-1/(q:ℝ) ≤ A ∧ A ≤ 1/2+1/(q:ℝ) := by
    constructor
    · apply le_trans _ (mul_le_mul_of_nonneg_left hl hy₀.le)
      rw [← mul_div_assoc, mul_one]
      field_simp
      nlinarith only [mul_le_mul_of_nonneg_right hqy hq₀.le,hqR]
    · apply (mul_le_mul_of_nonneg_left hu hy₀.le).trans
      rw [← mul_div_assoc,mul_one]
      field_simp
      linarith only [hyq]
  have hloglo := Real.log_le_sub_one_of_pos (div_pos hq₀ hy₀)
  have hloghi := Real.log_le_sub_one_of_pos (div_pos hy₀ hq₀)
  rw [log_div hq₀.ne' hy₀.ne'] at hloglo
  rw [log_div hy₀.ne' hq₀.ne'] at hloghi
  have hB₁ : y-q ≤ y*(log y-log q) := by
    have h := mul_le_mul_of_nonneg_left hloglo hy₀.le
    rw [mul_sub y ((q:ℝ)/y) 1,mul_div_cancel₀ _ hy₀.ne',mul_one] at h
    linarith only [h]
  have hB₂ : y*(log y-log q) ≤ y-q+1/(q:ℝ) := by
    apply (mul_le_mul_of_nonneg_left hloghi hy₀.le).trans
    have hs : (y-q)^2 ≤ 1 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hqy) (show 0 ≤ 1-(y-q) by linarith),hyq]
    field_simp
    nlinarith only [hs]
  have hrem : fixedBandUnitRamp y-unitRampMain y = (A-1/2)+(y-q-y*(log y-log q)) := by
    dsimp only [fixedBandUnitRamp,unitRampMain,A,q]; ring
  have habs : |fixedBandUnitRamp y-unitRampMain y| ≤ 2/(q:ℝ) := by
    rw [hrem,show 2/(q:ℝ)=2*(1/q) by ring]
    exact abs_le.mpr ⟨by linarith only [hA.1,hB₂],by linarith only [hA.2,hB₁,one_div_pos.mpr hq₀]⟩
  apply habs.trans
  exact (div_le_div_iff₀ hq₀ hy₀).mpr (by linarith)

theorem fixedBandLattice_ramps {y : ℝ} (hy : 0 ≤ y) :
    fixedBandLattice y = fixedBandUnitRamp y-3*fixedBandUnitRamp (y/2)+2*fixedBandUnitRamp (y/4) := by
  unfold fixedBandLattice dyadicPrimeWeight
  simp only [sum_add_distrib,sum_sub_distrib,← mul_sum,fixedBandUnitRamp_sum hy le_rfl,
    fixedBandUnitRamp_sum (by positivity : 0 ≤ y/2) (by linarith : y/2 ≤ y),
    fixedBandUnitRamp_sum (by positivity : 0 ≤ y/4) (by linarith : y/4 ≤ y)]

/-- The endpoints and the half-unit correction cancel in the triangular band.
At spacing d this makes the lattice error proportional to d/N. -/
theorem fixedBandLattice_error_inv {y : ℝ} (hy : 0 < y) :
    |fixedBandLattice y-fixedBandMain y| ≤ 60/y := by
  by_cases h4 : 4 ≤ y
  · have hmain : unitRampMain y-3*unitRampMain (y/2)+2*unitRampMain (y/4) = fixedBandMain y := by
      unfold unitRampMain fixedBandMain
      rw [log_div hy.ne' (by norm_num),log_div hy.ne' (by norm_num),
        show log 4 = 2*log 2 by rw [show (4:ℝ)=2^2 by norm_num,log_pow]; norm_num]
      ring
    have he : fixedBandLattice y-fixedBandMain y =
        (fixedBandUnitRamp y-unitRampMain y)-3*(fixedBandUnitRamp (y/2)-unitRampMain (y/2))+
        2*(fixedBandUnitRamp (y/4)-unitRampMain (y/4)) := by rw [fixedBandLattice_ramps hy.le,← hmain]; ring
    rw [he]
    apply (abs_add_le _ _).trans
    have h₁ := abs_sub (fixedBandUnitRamp y-unitRampMain y) (3*(fixedBandUnitRamp (y/2)-unitRampMain (y/2)))
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3)] at h₁
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hhalf := unitRamp_error (show 1 ≤ y/2 by linarith)
    have hquarter := unitRamp_error (show 1 ≤ y/4 by linarith)
    rw [show 4/(y/2)=8/y by ring] at hhalf
    rw [show 4/(y/4)=16/y by ring] at hquarter
    have hu := unitRamp_error (show 1 ≤ y by linarith)
    simp only [div_eq_mul_inv] at hu hhalf hquarter h₁ ⊢
    linarith only [h₁,hhalf,hquarter,hu]
  · have h : |fixedBandLattice y-fixedBandMain y| ≤ 1 := by rw [abs_sub_comm]; exact fixedBand_lattice_error hy
    exact h.trans ((le_div_iff₀ hy).mpr (by linarith))

private theorem band_divisor_inverse {N k : ℕ} (hk : k ∈ Ioc 0 N) :
      (∑ d ∈ Ioc 0 N, if d ∣ k then (ArithmeticFunction.moebius d:ℝ) else 0) = if k=1 then 1 else 0 := by
    have hset : (Ioc 0 N).filter (fun d => d ∣ k) = k.divisors := by
      ext d
      simp only [mem_filter,mem_Ioc,Nat.mem_divisors]
      have hk₀ := (mem_Ioc.mp hk).1
      exact ⟨fun h => ⟨h.2,hk₀.ne'⟩,fun h => ⟨⟨Nat.pos_of_dvd_of_pos h.1 hk₀,
        (Nat.le_of_dvd hk₀ h.1).trans (mem_Ioc.mp hk).2⟩,h.1⟩⟩
    rw [← sum_filter,hset]
    have h := congrArg (fun f : ArithmeticFunction ℝ => f k) (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℝ))
    simpa only [ArithmeticFunction.coe_zeta_mul_apply,ArithmeticFunction.intCoe_apply,ArithmeticFunction.one_apply] using h

private theorem mobius_unitRamp_sum {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : 0 ≤ x) (hxN : x ≤ N) :
    (∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d : ℝ)*fixedBandUnitRamp (x/d)) = max (x-1) 0 := by
  let S := Ioc 0 N
  let f (k : ℕ) := max (x/k-1) 0
  have row {d : ℕ} (hd : 0 < d) : (∑ k ∈ S.filter (fun k => d ∣ k), f k) = fixedBandUnitRamp (x/d) := by
    rw [← fixedBandUnitRamp_sum (Y := (N:ℝ)/d) (div_nonneg hx (Nat.cast_nonneg _))
      (div_le_div_of_nonneg_right hxN (Nat.cast_nonneg _)),Nat.floor_div_natCast,Nat.floor_natCast]
    symm
    apply sum_bij (fun j _ => d*j)
    · intro j hj
      refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.mul_pos hd (mem_Ioc.mp hj).1,?_⟩,dvd_mul_right _ _⟩
      simpa only [mul_comm] using (Nat.le_div_iff_mul_le hd).mp (mem_Ioc.mp hj).2
    · exact fun _ _ _ _ he => Nat.eq_of_mul_eq_mul_left hd he
    · intro k hk
      obtain ⟨hk,hdvd⟩ := mem_filter.mp hk
      obtain ⟨j,rfl⟩ := hdvd
      refine ⟨j,mem_Ioc.mpr ⟨?_,(Nat.le_div_iff_mul_le hd).mpr (by simpa only [mul_comm] using (mem_Ioc.mp hk).2)⟩,rfl⟩
      exact Nat.pos_of_ne_zero (fun hj => by simp [S,hj] at hk)
    · intro j _
      simp [f,Nat.cast_mul,div_div]
  calc
    _ = ∑ d ∈ S, ∑ k ∈ S, (if d ∣ k then (ArithmeticFunction.moebius d:ℝ) else 0)*f k := by
      apply sum_congr rfl
      intro d hd
      rw [← row (mem_Ioc.mp hd).1,sum_filter,mul_sum]
      apply sum_congr rfl
      intro k _
      by_cases hh : d ∣ k <;> simp [hh]
    _ = ∑ k ∈ S, ∑ d ∈ S, (if d ∣ k then (ArithmeticFunction.moebius d:ℝ) else 0)*f k := sum_comm
    _ = ∑ k ∈ S, if k=1 then f k else 0 := by
      apply sum_congr rfl
      intro k hk
      rw [← sum_mul,band_divisor_inverse hk]
      split_ifs <;> simp
    _ = _ := by simp [S,f,hN]

/-- The constant in the logarithmic moment of the fixed band. -/
def fixedBandLogConstant : ℝ := eulerMascheroniConstant - 1 + log 2

/-- Coefficient of the plain Möbius function after eliminating the continuous
prime density and the logarithms of individual divisors. -/
def fixedBandCenteredKernel (y : ℝ) : ℝ :=
  log 2*(fixedBandUnitRamp y-fixedBandUnitRamp (y/2)) - (log y+fixedBandLogConstant)*fixedBandLattice y

/-- Away from the support of the triangle, finite Möbius inversion cancels
the complete lattice sum, including at nonintegral scales. -/
theorem fixedBandLattice_moebius_zero {N : ℕ} {x : ℝ} (hx : 4 ≤ x) (hxN : x ≤ N) :
    (∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d:ℝ)*fixedBandLattice (x/d)) = 0 := by
  let S := Ioc 0 N
  let mu (d : ℕ) : ℝ := ArithmeticFunction.moebius d
  have h1 : 1 ≤ N := by exact_mod_cast (show (1:ℝ) ≤ N by linarith)
  have hp := mobius_unitRamp_sum h1 (by linarith) hxN
  have hh := mobius_unitRamp_sum h1 (by positivity : 0 ≤ x/2) (by linarith : x/2 ≤ N)
  have hq := mobius_unitRamp_sum h1 (by positivity : 0 ≤ x/4) (by linarith : x/4 ≤ N)
  rw [max_eq_left (by linarith : 0 ≤ x-1)] at hp
  rw [max_eq_left (by linarith : 0 ≤ x/2-1)] at hh
  rw [max_eq_left (by linarith : 0 ≤ x/4-1)] at hq
  calc
    _ = ∑ d ∈ S, (mu d*fixedBandUnitRamp (x/d) -
          3*(mu d*fixedBandUnitRamp ((x/2)/d)) + 2*(mu d*fixedBandUnitRamp ((x/4)/d))) := by
      apply sum_congr rfl
      intro d _
      rw [fixedBandLattice_ramps (show 0 ≤ x/d by positivity),div_right_comm x (d:ℝ) 2,
        div_right_comm x (d:ℝ) 4]
      ring
    _ = _ := by dsimp only [S,mu]; rw [sum_add_distrib,sum_sub_distrib,← mul_sum,← mul_sum,hp,hh,hq]; ring

/-- The same-scale calibration uses the divisor identity for μ and has no residual main term. -/
theorem fixedBand_centered_identity {N : ℕ} (hN : 4 ≤ N) :
    dyadicContrast N = ∑ d ∈ Ioc 0 N, (ArithmeticFunction.moebius d:ℝ)*fixedBandCenteredKernel ((N:ℝ)/d) := by
  let S := Ioc 0 N
  let mu (d : ℕ) : ℝ := ArithmeticFunction.moebius d
  have h1 : 1 ≤ N := by omega
  have h4 : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hN₀ := Nat.cast_pos (α := ℝ).mpr h1
  have hp := mobius_unitRamp_sum h1 hN₀.le le_rfl
  have hh := mobius_unitRamp_sum h1 (by positivity : 0 ≤ (N:ℝ)/2) (by linarith : (N:ℝ)/2 ≤ N)
  rw [max_eq_left (by linarith : 0 ≤ (N:ℝ)-1)] at hp
  rw [max_eq_left (by linarith : 0 ≤ (N:ℝ)/2-1)] at hh
  have hzero := fixedBandLattice_moebius_zero h4 (le_refl (N:ℝ))
  change (∑ d ∈ S, mu d*fixedBandLattice ((N:ℝ)/d)) = 0 at hzero
  have hr (d : ℕ) (hd : d ∈ S) : mu d*fixedBandCenteredKernel ((N:ℝ)/d) =
      log 2*(mu d*fixedBandUnitRamp ((N:ℝ)/d) - mu d*fixedBandUnitRamp (((N:ℝ)/2)/d)) +
      fixedBandMobiusCoeff d*fixedBandLattice ((N:ℝ)/d) -
      (log N+fixedBandLogConstant)*(mu d*fixedBandLattice ((N:ℝ)/d)) := by
    rw [fixedBandCenteredKernel,log_div hN₀.ne' (Nat.cast_pos.mpr (mem_Ioc.mp hd).1).ne',
      div_right_comm (N:ℝ) (d:ℝ) 2]
    dsimp only [mu,fixedBandMobiusCoeff]; ring
  rw [fixedBand_moebius_identity h1]
  change _ = ∑ d ∈ S, mu d*fixedBandCenteredKernel ((N:ℝ)/d)
  rw [sum_congr rfl hr,sum_sub_distrib,sum_add_distrib,← mul_sum,← mul_sum, hzero,mul_zero,sub_zero,
    sum_sub_distrib]
  dsimp only [mu,S]
  rw [hp,hh,fixedBandMain]
  ring

/-- Only the reciprocal lattice error survives in a centered large row. -/
theorem fixedBandCenteredKernel_bound {y : ℝ} (hy : 2 ≤ y) :
    |fixedBandCenteredKernel y| ≤ (72+60*|fixedBandLogConstant|)*(1+log y)/y := by
  have hy₀ : 0 < y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hmain : log 2*(unitRampMain y-unitRampMain (y/2)) = (log y+fixedBandLogConstant)*fixedBandMain y := by
    unfold unitRampMain fixedBandLogConstant fixedBandMain
    rw [log_div hy₀.ne' (by norm_num)]; ring
  have he : fixedBandCenteredKernel y =
      log 2*((fixedBandUnitRamp y-unitRampMain y)-(fixedBandUnitRamp (y/2)-unitRampMain (y/2))) -
      (log y+fixedBandLogConstant)*(fixedBandLattice y-fixedBandMain y) := by
    unfold fixedBandCenteredKernel; linear_combination hmain
  have hu := unitRamp_error hy1
  have hv := unitRamp_error (show 1 ≤ y/2 by linarith)
  rw [show 4/(y/2)=8/y by ring] at hv
  have hstep := (abs_sub _ _).trans (add_le_add hu hv)
  have hlog : |log 2| ≤ 1 := by rw [abs_of_nonneg (log_nonneg (by norm_num))]; linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hcoef := abs_add_le (log y) fixedBandLogConstant
  rw [abs_of_nonneg (log_nonneg hy1)] at hcoef
  rw [he]
  apply (abs_sub _ _).trans
  simp only [abs_mul]
  apply (add_le_add (mul_le_mul hlog hstep (abs_nonneg _) zero_le_one)
    (mul_le_mul hcoef (fixedBandLattice_error_inv hy₀) (abs_nonneg _) (add_nonneg (log_nonneg hy1) (abs_nonneg _)))).trans
  rw [one_mul]
  apply (le_div_iff₀ hy₀).mpr
  field_simp
  nlinarith only [log_nonneg hy1,abs_nonneg fixedBandLogConstant,
    mul_nonneg (abs_nonneg fixedBandLogConstant) (log_nonneg hy1),hy₀]

/-- A finite signed sum having no terms at or below K. -/
def fixedBandCenteredTail (N K : ℕ) : ℝ :=
  ∑ d ∈ Ioc K N, (ArithmeticFunction.moebius d:ℝ)*fixedBandCenteredKernel ((N:ℝ)/d)

private theorem earlyKernel_bound {N K : ℕ} (hN : 0 < N) (hK : 2*K ≤ N)
    {x : ℕ → ℝ} (hx : ∀ d ∈ Ioc 0 K, |x d| ≤ 1) :
    |∑ d ∈ Ioc 0 K, x d*fixedBandCenteredKernel ((N:ℝ)/d)| ≤
      (72+60*|fixedBandLogConstant|)*(K:ℝ)^2*(1+log N)/N := by
  have hN₀ : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  let C := 72+60*|fixedBandLogConstant|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _ ∈ Ioc 0 K, C*((1+log N)*(K:ℝ)/N) := by
      apply sum_le_sum
      intro d hd
      have hd₀ := Nat.cast_pos (α := ℝ).mpr (mem_Ioc.mp hd).1
      have hd1 : (1:ℝ) ≤ d := by exact_mod_cast (mem_Ioc.mp hd).1
      have hdk : (d:ℝ) ≤ K := Nat.cast_le.mpr (mem_Ioc.mp hd).2
      have h2 : 2 ≤ (N:ℝ)/d := (le_div_iff₀ hd₀).mpr (by exact_mod_cast (by have := (mem_Ioc.mp hd).2; omega : 2*d ≤ N))
      have h := fixedBandCenteredKernel_bound h2
      have hlog := Real.log_le_log (div_pos hN₀ hd₀) (div_le_self hN₀.le hd1)
      rw [abs_mul]
      apply (mul_le_of_le_one_left (abs_nonneg _) (hx d hd)).trans
      apply h.trans
      change C*(1+log ((N:ℝ)/d))/((N:ℝ)/d) ≤ _
      rw [show C*(1+log ((N:ℝ)/d))/((N:ℝ)/d) = C*((1+log ((N:ℝ)/d))*d/N) by field_simp]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
        (mul_le_mul (by linarith) hdk hd₀.le (by positivity [log_natCast_nonneg N])) hN₀.le) hC
    _ = _ := by simp only [sum_const,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul,C]; ring

/-- All small divisors, including their main contributions, can be removed at
cost O(K² log N/N) from the same finite sum. -/
theorem fixedBandCenteredTail_error {N K : ℕ} (hN : 4 ≤ N) (hK : 2*K ≤ N) :
    |dyadicContrast N-fixedBandCenteredTail N K| ≤
      (72+60*|fixedBandLogConstant|)*(K:ℝ)^2*(1+log N)/N := by
  let f (d : ℕ) := (ArithmeticFunction.moebius d:ℝ)*fixedBandCenteredKernel ((N:ℝ)/d)
  rw [fixedBand_centered_identity hN,fixedBandCenteredTail,
    ← sum_Ioc_consecutive f (Nat.zero_le K) (by omega : K ≤ N),add_sub_cancel_right]
  apply earlyKernel_bound (by omega) hK
  intro d _
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)

/-- The positive shortfall of the plain Möbius sum on the cubic-to-fourth-power band. -/
def fixedBandCenteredMass (m b : ℕ) : ℝ :=
  ∑ n ∈ Icc m b, max (fixedBandCenteredTail (n^4) (n^3)) 0 / (n:ℝ)^3

theorem fixedBandCentered_fourth_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 2 ≤ n →
      |dyadicPrimeDeficit ((n:ℝ)^4)-fixedBandCenteredTail (n^4) (n^3)| ≤ C*(n:ℝ)^2*(1+log n) := by
  obtain ⟨K,hK,hp⟩ := dyadicPrimeDeficit_power_cost
  let C := 72+60*|fixedBandLogConstant|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨K+4*C,by positivity,fun {n} hn => ?_⟩
  have hn₀ : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  obtain ⟨hlo,hhi⟩ := hp (pow_pos hn₀ 4)
  have hroot : Real.sqrt ((n:ℝ)^4) = (n:ℝ)^2 := by
    rw [show (n:ℝ)^4 = ((n:ℝ)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
  rw [hroot] at hhi
  have h4 : 4 ≤ n^4 := (by decide : 4 ≤ 2^4).trans (Nat.pow_le_pow_left hn 4)
  have hs : 2*n^3 ≤ n^4 := by rw [pow_succ n 3,mul_comm (n^3)]; exact Nat.mul_le_mul_right _ hn
  have hm := fixedBandCenteredTail_error h4 hs
  rw [Nat.cast_pow,Nat.cast_pow,Real.log_pow,Nat.cast_ofNat] at hm
  change |_ - _| ≤ C*((n:ℝ)^3)^2*(1+4*log n)/(n:ℝ)^4 at hm
  rw [show C*((n:ℝ)^3)^2*(1+4*log n)/(n:ℝ)^4 = C*(n:ℝ)^2*(1+4*log n) by field_simp] at hm
  apply (abs_sub_le _ (dyadicContrast ((n:ℝ)^4)) _).trans
  rw [abs_of_nonneg hlo]
  apply (add_le_add hhi hm).trans
  nlinarith only [mul_nonneg hC (sq_nonneg (n:ℝ)),mul_nonneg (mul_nonneg hK (sq_nonneg (n:ℝ))) (log_natCast_nonneg n)]

/-- All removed divisors together cost at most a squared logarithm in the positive mass. -/
theorem fixedBandCenteredMass_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m b : ℕ}, 2 ≤ m →
      |fixedBandMass m b-fixedBandCenteredMass m b| ≤ C*(1+log b)^2 := by
  obtain ⟨C,hC,h⟩ := fixedBandCentered_fourth_error
  exact ⟨C,hC,fun hm => fixedBand_positive_mass_error _ hC h hm⟩

/-- A power saving for the centered Möbius sum excludes precisely the same half-plane. -/
theorem zeta_ne_zero_of_fixedBandCenteredMass {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (h : ∀ A : ℕ, ∃ m ≥ A, fixedBandCenteredMass m ⌈(m:ℝ)^(1+δ)⌉₊ ≤ (m:ℝ)^α)
    {s : ℂ} (hs : 1/2+α/4 < s.re) : riemannZeta s ≠ 0 := by
  let β := (α+4*s.re-2)/2
  have hβ : α < β := by dsimp [β]; linarith
  obtain ⟨C,hC,he⟩ := fixedBandCenteredMass_error
  have hw := fixedBand_cofinal_mass_transfer fixedBandMass fixedBandCenteredMass hC
    (fun hm => (abs_le.mp (he hm)).2) hα hβ hδ₁ h
  exact zeta_ne_zero_of_fixedBandMass (hα.trans hβ) hδ hδ₁ hw (by dsimp [β]; linarith)

/-- Subpower positive mass of ordinary squarefree signs on n³ < d ≤ n⁴ suffices. -/
theorem rh_of_fixedBandCenteredMass_powerWindows
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ A : ℕ, ∃ m ≥ A,
      fixedBandCenteredMass m ⌈(m:ℝ)^(1+δ)⌉₊ ≤ (m:ℝ)^α) : RiemannHypothesis := by
  apply Formalism.VW.rh_of_right
  intro s hs _
  obtain ⟨δ,hδ,hδ₁,hw⟩ := h (s.re-1/2) (by linarith)
  exact zeta_ne_zero_of_fixedBandCenteredMass (by linarith) hδ hδ₁ hw (by linarith)

private theorem ramp_first {y : ℝ} (hy : 0 ≤ y) (hu : y ≤ 2) :
    fixedBandUnitRamp y = max (y-1) 0 := by
  rw [← fixedBandUnitRamp_sum hy hu]
  norm_num [show Ioc 0 (2:ℕ) = {1,2} by decide,max_eq_right (show y/2-1 ≤ 0 by linarith)]

/-- The triangular lattice on the first cofactor interval is a single ramp. -/
theorem fixedBandLattice_first {y : ℝ} (hy : 0 ≤ y) (h2 : y ≤ 2) :
    fixedBandLattice y = max (y-1) 0 := by
  rw [fixedBandLattice_ramps hy,ramp_first hy h2,ramp_first (by positivity : 0 ≤ y/2) (by linarith),
    ramp_first (by positivity : 0 ≤ y/4) (by linarith),
    max_eq_right (by linarith : y/2-1 ≤ 0),max_eq_right (by linarith : y/4-1 ≤ 0)]
  ring

/-- On the first cofactor interval the weight is an explicit function of scale alone. -/
theorem fixedBandCenteredKernel_first {y : ℝ} (h1 : 1 ≤ y) (h2 : y ≤ 2) :
    fixedBandCenteredKernel y = (y-1)*(1-eulerMascheroniConstant-log y) := by
  have hy := zero_le_one.trans h1
  rw [fixedBandCenteredKernel,fixedBandLattice_ramps hy,ramp_first hy h2,
    ramp_first (by positivity : 0 ≤ y/2) (by linarith),ramp_first (by positivity : 0 ≤ y/4) (by linarith),
    max_eq_left (by linarith : 0 ≤ y-1),max_eq_right (by linarith : y/2-1 ≤ 0),
    max_eq_right (by linarith : y/4-1 ≤ 0)]
  unfold fixedBandLogConstant; ring

/-- The matrix entry observes multiples of the product ab in the whole original sample. -/
def fixedBandProductEntry (N a b : ℕ) : ℝ :=
  ∑ k ∈ Ioc 0 N, if a*b ∣ k then fixedBandCenteredKernel ((N:ℝ)/k) else 0

/-- The quadratic form acts on the actual Möbius vector through the square root. -/
def fixedBandQuadratic (N U : ℕ) : ℝ :=
  ∑ a ∈ Ioc 0 U, ∑ b ∈ Ioc 0 U, ((ArithmeticFunction.moebius a:ℝ)*(ArithmeticFunction.moebius b:ℝ))*
    fixedBandProductEntry N a b

private def productEntryThrough (K a b : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Ioc 0 K, if a*b ∣ k then f k else 0

private theorem product_row {N a : ℕ} (ha : a ∈ Ioc 0 N) (f : ℕ → ℝ) :
    (∑ b ∈ Ioc 0 N, (ArithmeticFunction.moebius b:ℝ)*productEntryThrough N a b f) = f a := by
  have inv {k : ℕ} (hk : k ∈ Ioc 0 N) : (∑ b ∈ Ioc 0 N,
      if a*b ∣ k then (ArithmeticFunction.moebius b:ℝ) else 0) = if k=a then 1 else 0 := by
    by_cases hd : a ∣ k
    · obtain ⟨j,rfl⟩ := hd
      have ha₀ := (mem_Ioc.mp ha).1
      have hj : j ∈ Ioc 0 N := mem_Ioc.mpr ⟨Nat.pos_of_ne_zero (fun hh => by simp [hh] at hk),
        (Nat.le_mul_of_pos_left _ ha₀).trans (mem_Ioc.mp hk).2⟩
      simp only [Nat.mul_dvd_mul_iff_left ha₀,band_divisor_inverse hj]
      have he : a*j=a ↔ j=1 := ⟨fun h => Nat.eq_of_mul_eq_mul_left ha₀ (h.trans (Nat.mul_one a).symm),
        fun h => by rw [h,Nat.mul_one]⟩
      simp only [he]
    · have hn : k ≠ a := fun hh => hd (hh ▸ dvd_refl _)
      rw [ite_eq_right hn]
      exact sum_eq_zero fun b _ => ite_eq_right (fun hab => hd ((dvd_mul_right a b).trans hab))
  calc
    _ = ∑ b ∈ Ioc 0 N, ∑ k ∈ Ioc 0 N, (if a*b ∣ k then (ArithmeticFunction.moebius b:ℝ) else 0)*f k := by
      apply sum_congr rfl
      intro b _
      rw [productEntryThrough,mul_sum]
      apply sum_congr rfl
      intro k _
      by_cases h : a*b ∣ k <;> simp [h]
    _ = ∑ k ∈ Ioc 0 N, ∑ b ∈ Ioc 0 N, (if a*b ∣ k then (ArithmeticFunction.moebius b:ℝ) else 0)*f k := sum_comm
    _ = ∑ k ∈ Ioc 0 N, if k=a then f k else 0 := by
      apply sum_congr rfl
      intro k hk
      rw [← sum_mul,inv hk]
      split_ifs <;> simp
    _ = _ := by simp [ha]

/-- Contribution with both divisors above the chosen truncation. -/
def fixedBandOuter (N V : ℕ) : ℝ :=
  ∑ a ∈ Ioc V N, ∑ b ∈ Ioc V N,
    ((ArithmeticFunction.moebius a:ℝ)*(ArithmeticFunction.moebius b:ℝ))*fixedBandProductEntry N a b

theorem fixedBandProductEntry_zero {N a b : ℕ} (h : N < a*b) : fixedBandProductEntry N a b=0 :=
  sum_eq_zero fun _ hk => ite_eq_right (fun hd =>
    (not_le.mpr h) ((Nat.le_of_dvd (mem_Ioc.mp hk).1 hd).trans (mem_Ioc.mp hk).2))

open scoped ArithmeticFunction.Moebius in
private theorem quadratic_split_through {N U : ℕ} (hU : U ≤ N) (f : ℕ → ℝ) :
    (∑ k ∈ Ioc 0 N, (μ k:ℝ)*f k) +
        (∑ a ∈ Ioc 0 U, ∑ b ∈ Ioc 0 U, ((μ a:ℝ)*(μ b:ℝ))*productEntryThrough N a b f) =
      2*(∑ k ∈ Ioc 0 U, (μ k:ℝ)*f k) +
        (∑ a ∈ Ioc U N, ∑ b ∈ Ioc U N, ((μ a:ℝ)*(μ b:ℝ))*productEntryThrough N a b f) := by
  let S := Ioc 0 U
  let L := Ioc U N
  let mu (d : ℕ) : ℝ := ArithmeticFunction.moebius d
  let G (a b : ℕ) := (mu a*mu b)*productEntryThrough N a b f
  let v (a : ℕ) := mu a*f a
  have split (f : ℕ → ℝ) : (∑ a ∈ S, f a)+(∑ a ∈ L, f a) = ∑ a ∈ Ioc 0 N, f a :=
    sum_Ioc_consecutive f (Nat.zero_le U) hU
  have row (a : ℕ) (ha : a ∈ Ioc 0 N) : (∑ b ∈ Ioc 0 N, G a b)=v a := by
    simp only [G,mul_assoc,← mul_sum,v,mu,product_row ha f]
  have symm (a b : ℕ) : G a b = G b a := by
    dsimp only [G,productEntryThrough]
    rw [mul_comm a b,mul_comm (mu a)]
  have cross : (∑ a ∈ L, ∑ b ∈ S, G a b) = ∑ a ∈ S, ∑ b ∈ L, G a b := by
    rw [sum_comm]; exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => symm _ _
  have lhs (A : Finset ℕ) (hA : A ⊆ Ioc 0 N) : (∑ a ∈ A, v a) =
      (∑ a ∈ A, ∑ b ∈ S, G a b)+(∑ a ∈ A, ∑ b ∈ L, G a b) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun a ha => (row a (hA ha)).symm.trans (split (G a)).symm
  have hs := lhs S (Ioc_subset_Ioc_right hU)
  have hl := lhs L (Ioc_subset_Ioc_left (Nat.zero_le U))
  rw [cross] at hl
  change (∑ a ∈ Ioc 0 N, v a)+(∑ a ∈ S, ∑ b ∈ S, G a b) =
    2*(∑ a ∈ S, v a)+(∑ a ∈ L, ∑ b ∈ L, G a b)
  linarith only [split v,hl,hs]

open scoped ArithmeticFunction.Moebius in
/-- Near the square-root cutoff, inversion controls a perturbation of the
multiple weights by O(N) times its uniform error. The outer square has at
most one multiple per pair. -/
theorem fixedBand_weighted_quadratic_abs_le {N V : ℕ} (hV : V^2 ≤ N) (hN : N ≤ 2*V^2)
    {f : ℕ → ℝ} {E : ℝ} (hE : 0 ≤ E) (hf : ∀ k ∈ Ioc 0 N, |f k| ≤ E) :
    |∑ a ∈ Ioc 0 V, ∑ b ∈ Ioc 0 V, ((μ a:ℝ)*(μ b:ℝ))*
      (∑ k ∈ Ioc 0 N, if a*b ∣ k then f k else 0)| ≤ 4*(N:ℝ)*E := by
  let S := Ioc V N
  let T := Ioc V (min N (2*V))
  let g (a b : ℕ) := ((μ a:ℝ)*(μ b:ℝ))*productEntryThrough N a b f
  let w (k : ℕ) := (μ k:ℝ)*f k
  have hVN : V ≤ N := (Nat.le_self_pow (by decide : (2:ℕ) ≠ 0) V).trans hV
  have hT : T ⊆ S := Ioc_subset_Ioc_right (min_le_left _ _)
  have hμ (k : ℕ) : |(μ k:ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k)
  have hzero {a b : ℕ} (hab : N < a*b) : g a b=0 := by
    have he : productEntryThrough N a b f = 0 := by
      apply sum_eq_zero
      intro k hk
      exact ite_eq_right (fun hd => hab.not_ge
        ((Nat.le_of_dvd (mem_Ioc.mp hk).1 hd).trans (mem_Ioc.mp hk).2))
    simp [g,he]
  have hentry {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S) : |g a b| ≤ E := by
    have ha₁ := (mem_Ioc.mp ha).1
    have hb₁ := (mem_Ioc.mp hb).1
    by_cases hab : a*b ≤ N
    · have hab₀ : 0 < a*b := Nat.mul_pos (by omega) (by omega)
      have hab₂ : N < 2*(a*b) := by
        have h := Nat.mul_lt_mul_of_lt_of_lt ha₁ hb₁
        rw [← pow_two] at h
        exact hN.trans_lt (Nat.mul_lt_mul_of_pos_left h (by decide))
      have he : productEntryThrough N a b f = f (a*b) := by
        unfold productEntryThrough
        rw [sum_eq_single (a*b),ite_eq_left (dvd_refl _)]
        · intro k hk hne
          apply ite_eq_right
          rintro ⟨j,rfl⟩
          have hj : 2 ≤ j := by
            have h₀ : j ≠ 0 := fun h => (mem_Ioc.mp hk).1.ne' (by simp [h])
            have h₁ : j ≠ 1 := fun h => hne (by simp [h])
            omega
          have hmul : 2*(a*b) ≤ a*b*j := by
            simpa only [Nat.mul_comm 2] using Nat.mul_le_mul_left (a*b) hj
          exact hab₂.not_ge (hmul.trans (mem_Ioc.mp hk).2)
        · exact fun h => (h (mem_Ioc.mpr ⟨hab₀,hab⟩)).elim
      dsimp only [g]
      rw [he,abs_mul,abs_mul]
      have hprod : |(μ a:ℝ)| * |(μ b:ℝ)| ≤ 1 := by
        simpa using mul_le_mul (hμ a) (hμ b) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
      exact (mul_le_of_le_one_left (abs_nonneg _) hprod).trans (hf _ (mem_Ioc.mpr ⟨hab₀,hab⟩))
    · rw [hzero (lt_of_not_ge hab),abs_zero]
      exact hE
  have houtside {a : ℕ} (ha : a ∈ S) (ht : a ∉ T) : 2*V < a := by
    have ha' := mem_Ioc.mp ha
    by_contra! h
    exact ht (mem_Ioc.mpr ⟨ha'.1,le_min ha'.2 h⟩)
  have houter :
      |∑ a ∈ S, ∑ b ∈ S, g a b| ≤ (N:ℝ)*E := by
    have hcut : (∑ a ∈ S, ∑ b ∈ S, g a b) = ∑ a ∈ T, ∑ b ∈ T, g a b := by
      calc
        _ = ∑ a ∈ S, ∑ b ∈ T, g a b := by
          apply sum_congr rfl
          intro a ha
          apply (sum_subset hT _).symm
          intro b hb ht
          have h := Nat.mul_lt_mul_of_lt_of_lt (mem_Ioc.mp ha).1 (houtside hb ht)
          exact hzero (hN.trans_lt (by convert h using 1; ring))
        _ = _ := by
          apply (sum_subset hT _).symm
          intro a ha ht
          apply sum_eq_zero
          intro b hb
          have h := Nat.mul_lt_mul_of_lt_of_lt (houtside ha ht) (mem_Ioc.mp (hT hb)).1
          exact hzero (hN.trans_lt (by convert h using 1; ring))
    rw [hcut]
    apply (abs_sum_le_sum_abs _ _).trans
    have hc : (#T:ℝ) ≤ V := by
      exact_mod_cast (show #T ≤ V by simp [T,Nat.card_Ioc]; omega)
    calc
      _ ≤ ∑ _a ∈ T, ∑ _b ∈ T, E := by
        apply sum_le_sum
        intro a ha
        exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun b hb => hentry (hT ha) (hT hb))
      _ ≤ (N:ℝ)*E := by
        simp only [sum_const,nsmul_eq_mul,← mul_assoc,← pow_two]
        exact mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ (by positivity) hc 2).trans
          (by exact_mod_cast hV)) hE
  have hlinear {D : ℕ} (hD : D ≤ N) : |∑ k ∈ Ioc 0 D, w k| ≤ (N:ℝ)*E := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _k ∈ Ioc 0 D, E := by
        apply sum_le_sum
        intro k hk
        change |(μ k:ℝ)*f k| ≤ E
        rw [abs_mul]
        exact (mul_le_of_le_one_left (abs_nonneg _) (hμ k)).trans (hf k (Ioc_subset_Ioc_right hD hk))
      _ ≤ _ := by
        simp only [sum_const,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hD) hE
  have h := quadratic_split_through hVN f
  change (∑ k ∈ Ioc 0 N, w k)+(∑ a ∈ Ioc 0 V, ∑ b ∈ Ioc 0 V, g a b) =
    2*(∑ k ∈ Ioc 0 V, w k)+(∑ a ∈ S, ∑ b ∈ S, g a b) at h
  change |∑ a ∈ Ioc 0 V, ∑ b ∈ Ioc 0 V, g a b| ≤ _
  rw [show (∑ a ∈ Ioc 0 V, ∑ b ∈ Ioc 0 V, g a b) =
    (2*(∑ k ∈ Ioc 0 V, w k)-(∑ k ∈ Ioc 0 N, w k))+(∑ a ∈ S, ∑ b ∈ S, g a b) by linarith only [h]]
  apply (abs_add_le _ _).trans
  apply (add_le_add (abs_sub _ _) houter).trans
  rw [abs_mul,abs_of_nonneg (by norm_num : 0 ≤ (2:ℝ))]
  linarith only [hlinear hVN,hlinear le_rfl]

/-- The unrestricted double inversion keeps the outer square as an exact remainder. -/
theorem fixedBand_quadratic_split {N U : ℕ} (hN : 4 ≤ N) (hU : U ≤ N) :
    dyadicContrast N + fixedBandQuadratic N U =
      2*(∑ d ∈ Ioc 0 U, (ArithmeticFunction.moebius d:ℝ)*fixedBandCenteredKernel ((N:ℝ)/d)) +
        fixedBandOuter N U := by
  rw [fixedBand_centered_identity hN]
  exact quadratic_split_through hU (fun k => fixedBandCenteredKernel ((N:ℝ)/k))

open scoped ArithmeticFunction.Moebius in
private theorem quadratic_identity_through {K V : ℕ} (hVK : V ≤ K) (hKV : K ≤ V^2)
    (f : ℕ → ℝ) :
    (∑ k ∈ Ioc 0 K, (μ k:ℝ)*f k) +
        (∑ a ∈ Ioc 0 V, ∑ b ∈ Ioc 0 V, ((μ a:ℝ)*(μ b:ℝ))*productEntryThrough K a b f) =
      2*(∑ k ∈ Ioc 0 V, (μ k:ℝ)*f k) := by
  have hOuter :
      (∑ a ∈ Ioc V K, ∑ b ∈ Ioc V K, ((μ a:ℝ)*(μ b:ℝ))*productEntryThrough K a b f) = 0 := by
    apply sum_eq_zero
    intro a ha
    apply sum_eq_zero
    intro b hb
    rw [productEntryThrough,sum_eq_zero]
    · exact mul_zero _
    · intro k hk
      apply ite_eq_right
      intro hab
      have hprod := Nat.mul_lt_mul_of_lt_of_lt (mem_Ioc.mp ha).1 (mem_Ioc.mp hb).1
      rw [← pow_two] at hprod
      exact (hKV.trans_lt hprod).not_ge
        ((Nat.le_of_dvd (mem_Ioc.mp hk).1 hab).trans (mem_Ioc.mp hk).2)
  have h := quadratic_split_through hVK f
  simpa only [hOuter,add_zero] using h

open scoped ArithmeticFunction.Moebius in
/-- Up to the square of the divisor cutoff, completing both rows gives a
single Möbius coefficient. It changes sign above the cutoff. -/
theorem fixedBand_early_multiples {K V : ℕ} (hVK : V ≤ K) (hKV : K ≤ V^2) (f : ℕ → ℝ) :
    (∑ a ∈ Ioc 0 V, ∑ b ∈ Ioc 0 V, ((μ a:ℝ)*(μ b:ℝ))*
      (∑ k ∈ Ioc 0 K, if a*b ∣ k then f k else 0)) =
    ∑ k ∈ Ioc 0 K, (if k ≤ V then (μ k:ℝ) else -(μ k:ℝ))*f k := by
  have h := quadratic_identity_through hVK hKV f
  rw [← sum_Ioc_consecutive _ (Nat.zero_le V) hVK]
  have hhead : (∑ k ∈ Ioc 0 V, (if k ≤ V then (μ k:ℝ) else -(μ k:ℝ))*f k) =
      ∑ k ∈ Ioc 0 V, (μ k:ℝ)*f k :=
    sum_congr rfl fun k hk => by rw [ite_eq_left (mem_Ioc.mp hk).2]
  have htail : (∑ k ∈ Ioc V K, (if k ≤ V then (μ k:ℝ) else -(μ k:ℝ))*f k) =
      -(∑ k ∈ Ioc V K, (μ k:ℝ)*f k) := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun k hk => by rw [ite_eq_right (mem_Ioc.mp hk).1.not_ge,neg_mul]
  rw [hhead,htail]
  rw [← sum_Ioc_consecutive (fun k => (μ k:ℝ)*f k) (Nat.zero_le V) hVK] at h
  change (∑ a ∈ Ioc 0 V, ∑ b ∈ Ioc 0 V, ((μ a:ℝ)*(μ b:ℝ))*productEntryThrough K a b f) = _
  linarith only [h]

open scoped ArithmeticFunction.Moebius in
/-- Retain only multiples above K in each matrix entry. -/
def fixedBandQuadraticAfter (N V K : ℕ) : ℝ :=
  ∑ a ∈ Ioc 0 V, ∑ b ∈ Ioc 0 V, ((μ a:ℝ)*(μ b:ℝ))*
    (∑ k ∈ Ioc K N, if a*b ∣ k then fixedBandCenteredKernel ((N:ℝ)/k) else 0)

open scoped ArithmeticFunction.Moebius in
private theorem quadratic_sub_after {N V K : ℕ} (hKN : K ≤ N) :
    fixedBandQuadratic N V-fixedBandQuadraticAfter N V K =
      ∑ a ∈ Ioc 0 V, ∑ b ∈ Ioc 0 V, ((μ a:ℝ)*(μ b:ℝ))*
        (∑ k ∈ Ioc 0 K, if a*b ∣ k then fixedBandCenteredKernel ((N:ℝ)/k) else 0) := by
  let f (k : ℕ) := fixedBandCenteredKernel ((N:ℝ)/k)
  simp only [fixedBandQuadratic, fixedBandProductEntry, fixedBandQuadraticAfter,
    ← sum_sub_distrib, ← mul_sub]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  rw [← sum_Ioc_consecutive (fun k => if a*b ∣ k then f k else 0) (Nat.zero_le K) hKN,
    add_sub_cancel_right]

open scoped ArithmeticFunction.Moebius in
/-- The discarded multiples are paid at the cost of a single early Möbius sum. -/
theorem fixedBandQuadraticAfter_error {N V K : ℕ} (hN : 0 < N) (hVK : V ≤ K)
    (hKV : K ≤ V^2) (hK : 2*K ≤ N) :
    |fixedBandQuadratic N V-fixedBandQuadraticAfter N V K| ≤
      (72+60*|fixedBandLogConstant|)*(K:ℝ)^2*(1+log N)/N := by
  rw [quadratic_sub_after (by omega : K ≤ N),fixedBand_early_multiples hVK hKV]
  apply earlyKernel_bound hN hK
  intro d _
  have hμ : |(μ d:ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  split_ifs
  · exact hμ
  · simpa only [abs_neg] using hμ

open scoped ArithmeticFunction.Moebius in
/-- After the early multiples are discarded, the square equals the signed
tail plus the exact contribution with both divisors above the cutoff. -/
theorem fixedBandQuadraticAfter_eq {N V K : ℕ} (hN : 4 ≤ N) (hVK : V ≤ K)
    (hKV : K ≤ V^2) (hKN : K ≤ N) :
    fixedBandQuadraticAfter N V K = fixedBandOuter N V-fixedBandCenteredTail N K := by
  let f (k : ℕ) := fixedBandCenteredKernel ((N:ℝ)/k)
  have h := fixedBand_quadratic_split hN (hVK.trans hKN)
  rw [fixedBand_centered_identity hN,
    ← sum_Ioc_consecutive (fun k => (μ k:ℝ)*f k) (Nat.zero_le K) hKN] at h
  have he := quadratic_identity_through hVK hKV f
  have hs := quadratic_sub_after (V := V) hKN
  change fixedBandQuadratic N V-fixedBandQuadraticAfter N V K =
      ∑ a ∈ Ioc 0 V, ∑ b ∈ Ioc 0 V, ((μ a:ℝ)*(μ b:ℝ))*productEntryThrough K a b f at hs
  change fixedBandQuadraticAfter N V K = fixedBandOuter N V - ∑ k ∈ Ioc K N, (μ k:ℝ)*f k
  linarith only [h,he,hs]

/-- The last discarded multiple at the fourth-power sample. -/
def fixedBandMultipleCutoff (n : ℕ) : ℕ := n^3 / ⌈sqrt (1+log n)⌉₊

theorem fixedBandMultipleCutoff_bounds {n V : ℕ} (hn : 2 ≤ n)
    (hV : V ≤ n^2) (hV₃ : 3*n^2 ≤ 4*V) :
    V ≤ fixedBandMultipleCutoff n ∧ fixedBandMultipleCutoff n ≤ V^2 ∧
      2*fixedBandMultipleCutoff n ≤ n^4 := by
  let t := ⌈sqrt (1+log (n:ℝ))⌉₊
  let K := fixedBandMultipleCutoff n
  have hnR : 2 ≤ (n:ℝ) := by exact_mod_cast hn
  have ht : 0 < t := Nat.ceil_pos.mpr (sqrt_pos.mpr (by linarith [log_natCast_nonneg n]))
  have htn : t ≤ n := Nat.ceil_le.mpr (sqrt_le_iff.mpr ⟨by positivity,by
    have hl := log_le_sub_one_of_pos (show 0 < (n:ℝ) by linarith)
    nlinarith only [hl, hnR, mul_nonneg (show 0 ≤ (n:ℝ) by positivity)
      (show 0 ≤ (n:ℝ)-1 by linarith)]⟩)
  have hKin : n^2 ≤ K := (Nat.le_div_iff_mul_le ht).mpr (by
    calc n^2*t ≤ n^2*n := Nat.mul_le_mul_left _ htn
         _ = n^3 := by ring)
  have hK : K ≤ n^3 := Nat.div_le_self _ _
  have hVpow : n^3 ≤ V^2 := by
    have hr : 3*(n:ℝ)^2 ≤ 4*(V:ℝ) := by exact_mod_cast hV₃
    have hh := pow_le_pow_left₀ (by positivity) hr 2
    exact_mod_cast (show (n:ℝ)^3 ≤ (V:ℝ)^2 by
      nlinarith only [hh,mul_nonneg (show 0 ≤ (n:ℝ)-2 by linarith)
        (show 0 ≤ (n:ℝ)^3 by positivity),show 0 ≤ (n:ℝ)^3 by positivity])
  have h2K : 2*K ≤ n^4 := by
    rw [pow_succ n 3,mul_comm (n^3)]
    exact (Nat.mul_le_mul_left _ hK).trans (Nat.mul_le_mul_right _ hn)
  exact ⟨hV.trans hKin,hK.trans hVpow,h2K⟩

private theorem fixedBandMultipleCutoff_cost {n : ℕ} (hn : 2 ≤ n) :
    (72+60*|fixedBandLogConstant|)*(fixedBandMultipleCutoff n:ℝ)^2*
        (1+log ((n^4:ℕ):ℝ))/((n^4:ℕ):ℝ) ≤
      4*(72+60*|fixedBandLogConstant|)*(n:ℝ)^2 := by
  let t := ⌈sqrt (1+log (n:ℝ))⌉₊
  let K := fixedBandMultipleCutoff n
  let C := 72+60*|fixedBandLogConstant|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hp : 0 ≤ 1+log (n:ℝ) := by positivity [log_natCast_nonneg n]
  have hsq : sqrt (1+log (n:ℝ)) ≤ (t:ℝ) := Nat.le_ceil _
  have hmul : (K:ℝ)*(t:ℝ) ≤ (n:ℝ)^3 := by exact_mod_cast Nat.div_mul_le_self (n^3) t
  have hsqK : (K:ℝ)^2*(1+log (n:ℝ)) ≤ (n:ℝ)^6 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (K:ℝ)*sqrt (1+log (n:ℝ)))
      ((mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ (K:ℝ))).trans hmul) 2
    rw [mul_pow,sq_sqrt hp] at hh
    simpa only [← pow_mul,show 3*2=6 by decide] using hh
  have hn₀ : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  change C*(K:ℝ)^2*(1+log ((n^4:ℕ):ℝ))/((n^4:ℕ):ℝ) ≤ 4*C*(n:ℝ)^2
  rw [Nat.cast_pow,log_pow,Nat.cast_ofNat]
  have hb : (K:ℝ)^2*(1+4*log n) ≤ 4*(n:ℝ)^6 := by
    nlinarith only [hsqK,sq_nonneg (K:ℝ)]
  calc
    _ ≤ C*(4*(n:ℝ)^6)/(n:ℝ)^4 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb hC
    _ = 4*C*(n:ℝ)^2 := by field_simp [hn₀.ne']

section
open scoped ArithmeticFunction.Moebius

/-- The original interval sums use one shared prefix, including across
quotient changes. -/
noncomputable def fixedBandPrefix (k : ℕ) : ℝ :=
  ∑ j ∈ range (k+1), (μ j:ℝ)

private theorem fixedBandPrefix_abs_le (k : ℕ) : |fixedBandPrefix k| ≤ k := by
  unfold fixedBandPrefix
  rw [sum_range_succ' (fun j : ℕ => (μ j:ℝ))]
  simp only [ArithmeticFunction.map_zero,Int.cast_zero,add_zero]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _j ∈ range k, (1:ℝ) :=
      sum_le_sum fun j _ => by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := j+1)
    _ = (k:ℝ) := by simp

/-- Taking each quotient interval's contribution with the same endpoint
weight makes the signed endpoint terms telescope when the intervals join. -/
theorem fixedBand_abel_join (w : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ k ∈ Ioc a b, (μ k:ℝ)*w k) =
      fixedBandPrefix b*w b-fixedBandPrefix a*w a+
        ∑ k ∈ Ico a b, fixedBandPrefix k*(w k-w (k+1)) := by
  have hdiff (k : ℕ) : (μ (k+1):ℝ) = fixedBandPrefix (k+1)-fixedBandPrefix k := by
    simp only [fixedBandPrefix, sum_range_succ (n := k+1),add_sub_cancel_left]
  rw [← Ico_add_one_add_one_eq_Ioc, ← sum_Ico_add']
  simp_rw [hdiff]
  have htel :
      (∑ k ∈ Ico a b, (fixedBandPrefix (k+1)*w (k+1)-fixedBandPrefix k*w k)) =
        fixedBandPrefix b*w b-fixedBandPrefix a*w a := by
    simpa only using sum_Ico_sub (fun k => fixedBandPrefix k*w k) hab
  rw [← htel, ← sum_add_distrib]
  exact sum_congr rfl fun k _ => by ring

/-- The signed prefix statistic retains terms from all quotient intervals
until after summation. The endpoints at each interior quotient change
cancel algebraically. -/
noncomputable def fixedBandCoupledPrefixAt (n : ℕ) : ℝ :=
  let w := fun k : ℕ => fixedBandCenteredKernel (((n^4:ℕ):ℝ)/k)
  ∑ k ∈ Ico (fixedBandMultipleCutoff n) (n^4), fixedBandPrefix k*(w k-w (k+1))

theorem fixedBandCoupledPrefixAt_eq {n : ℕ} (hn : 2 ≤ n) :
    fixedBandCenteredTail (n^4) (fixedBandMultipleCutoff n) =
      fixedBandCoupledPrefixAt n-fixedBandPrefix (fixedBandMultipleCutoff n)*
        fixedBandCenteredKernel (((n^4:ℕ):ℝ)/(fixedBandMultipleCutoff n:ℕ)) := by
  let K := fixedBandMultipleCutoff n
  let w := fun k : ℕ => fixedBandCenteredKernel (((n^4:ℕ):ℝ)/k)
  have hK := (fixedBandMultipleCutoff_bounds (V := n^2) hn le_rfl (by omega)).2.2
  have hw : w (n^4)=0 := by
    have hp : 0 < ((n^4:ℕ):ℝ) := Nat.cast_pos.mpr (pow_pos (by omega : 0 < n) _)
    dsimp [w]
    rw [div_self hp.ne', fixedBandCenteredKernel_first le_rfl (by norm_num)]
    ring
  change (∑ k ∈ Ioc K (n^4), (μ k:ℝ)*w k) =
    (∑ k ∈ Ico K (n^4), fixedBandPrefix k*(w k-w (k+1)))-fixedBandPrefix K*w K
  rw [fixedBand_abel_join w (by omega), hw,mul_zero]
  ring

private theorem fixedBandPrefix_boundary_le {N K : ℕ} (hK : 1 ≤ K) (hN : 2*K ≤ N) :
    |fixedBandPrefix K * fixedBandCenteredKernel ((N:ℝ)/K)| ≤
      (72+60*|fixedBandLogConstant|)*(K:ℝ)^2*(1+log N)/(N:ℝ) := by
  have hK₁ : 1 ≤ (K:ℝ) := by exact_mod_cast hK
  have hK₀ : 0 < (K:ℝ) := by linarith
  have hN₂ : 2*(K:ℝ) ≤ N := by exact_mod_cast hN
  have hN₀ : 0 < (N:ℝ) := by linarith
  have hy : 2 ≤ (N:ℝ)/K := (le_div_iff₀ hK₀).mpr hN₂
  have hlog : log ((N:ℝ)/K) ≤ log N :=
    log_le_log (by positivity) (div_le_self hN₀.le hK₁)
  let C := 72+60*|fixedBandLogConstant|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  rw [abs_mul]
  apply (mul_le_mul (fixedBandPrefix_abs_le K) (fixedBandCenteredKernel_bound hy)
    (abs_nonneg _) hK₀.le).trans
  calc
    _ = C*(K:ℝ)^2*(1+log ((N:ℝ)/K))/(N:ℝ) := by
      dsimp only [C]
      field_simp [hK₀.ne',hN₀.ne']
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hN₀.le
      exact mul_le_mul_of_nonneg_left (add_le_add_right hlog 1) (by positivity)

/-- The shared-prefix representation loses at most the existing square-root
budget at its two endpoints. -/
theorem fixedBandCoupledPrefixAt_error {n : ℕ} (hn : 2 ≤ n) :
    |fixedBandCenteredTail (n^4) (fixedBandMultipleCutoff n)-fixedBandCoupledPrefixAt n| ≤
      4*(72+60*|fixedBandLogConstant|)*(n:ℝ)^2 := by
  obtain ⟨hle,_,hK⟩ := fixedBandMultipleCutoff_bounds (V := n^2) hn le_rfl (by omega)
  have hpos : 1 ≤ fixedBandMultipleCutoff n := (by positivity : 0 < n^2).trans_le hle
  rw [fixedBandCoupledPrefixAt_eq hn,sub_right_comm,sub_self,zero_sub,abs_neg]
  exact (fixedBandPrefix_boundary_le hpos hK).trans (fixedBandMultipleCutoff_cost hn)

end

/-- This truncation costs O(n²) uniformly across the adaptive divisor cutoffs. -/
theorem fixedBandQuadraticAfter_fourth_error {n V : ℕ} (hn : 2 ≤ n)
    (hV : V ≤ n^2) (hV₃ : 3*n^2 ≤ 4*V) :
    |fixedBandQuadratic (n^4) V-fixedBandQuadraticAfter (n^4) V (fixedBandMultipleCutoff n)| ≤
      4*(72+60*|fixedBandLogConstant|)*(n:ℝ)^2 := by
  obtain ⟨h₁,h₂,h₃⟩ := fixedBandMultipleCutoff_bounds hn hV hV₃
  exact (fixedBandQuadraticAfter_error (pow_pos (by omega : 0 < n) _) h₁ h₂ h₃).trans
    (fixedBandMultipleCutoff_cost hn)

/-- Above the square-root cutoff both large divisors cannot occur in one product. -/
theorem fixedBandOuter_zero {N U : ℕ} (hNU : N ≤ U^2) : fixedBandOuter N U = 0 := by
  apply sum_eq_zero
  intro a ha
  apply sum_eq_zero
  intro b hb
  have h := Nat.mul_lt_mul_of_lt_of_lt (mem_Ioc.mp ha).1 (mem_Ioc.mp hb).1
  rw [← pow_two] at h
  rw [fixedBandProductEntry_zero (hNU.trans_lt h),mul_zero]

/-- At or below U² the double inversion leaves just the small square. -/
theorem fixedBand_quadratic_identity {N U : ℕ} (hN : 4 ≤ N) (hU : U ≤ N) (hNU : N ≤ U^2) :
    dyadicContrast N + fixedBandQuadratic N U =
      2*∑ d ∈ Ioc 0 U, (ArithmeticFunction.moebius d:ℝ)*fixedBandCenteredKernel ((N:ℝ)/d) := by
  rw [fixedBand_quadratic_split hN hU,fixedBandOuter_zero hNU,add_zero]

/-- The full small-divisor sum, with its mean, has a reciprocal lattice error. -/
theorem fixedBand_small_rows {N V : ℕ} (hN : 4 ≤ N) (hV : 2*V ≤ N) :
    |∑ d ∈ Ioc 0 V, (ArithmeticFunction.moebius d:ℝ)*fixedBandCenteredKernel ((N:ℝ)/d)| ≤
      (72+60*|fixedBandLogConstant|)*(V:ℝ)^2*(1+log N)/N := by
  have h := fixedBandCenteredTail_error hN hV
  rw [fixedBand_centered_identity hN,fixedBandCenteredTail,
    ← sum_Ioc_consecutive _ (Nat.zero_le V) (by omega : V ≤ N),add_sub_cancel_right] at h
  exact h

/-- In the prime-power statistic the quadratic form costs only a logarithm per sample. -/
theorem fixedBand_quadratic_fourth_error {n : ℕ} (hn : 2 ≤ n) :
    |dyadicContrast ((n:ℝ)^4)+fixedBandQuadratic (n^4) (n^2)| ≤
      2*(72+60*|fixedBandLogConstant|)*(1+4*log n) := by
  let N := n^4
  let U := n^2
  let f (d : ℕ) := (ArithmeticFunction.moebius d:ℝ)*fixedBandCenteredKernel ((N:ℝ)/d)
  have hN : 4 ≤ N := (by decide : 4 ≤ 2^4).trans (Nat.pow_le_pow_left hn 4)
  have hU2 : 2 ≤ U := (by decide : 2 ≤ 2^2).trans (Nat.pow_le_pow_left hn 2)
  have hsq : N = U^2 := by dsimp [N,U]; ring
  have hcut : 2*U ≤ N := by rw [hsq,pow_two]; exact Nat.mul_le_mul_right U hU2
  have hUN : U ≤ N := by omega
  have he := fixedBand_quadratic_identity hN hUN hsq.le
  change dyadicContrast N+fixedBandQuadratic N U=2*∑ d ∈ Ioc 0 U, f d at he
  have hprefix : dyadicContrast N-fixedBandCenteredTail N U = ∑ d ∈ Ioc 0 U, f d := by
    rw [fixedBand_centered_identity hN,fixedBandCenteredTail]
    change (∑ d ∈ Ioc 0 N, f d)-(∑ d ∈ Ioc U N, f d)=_
    rw [← sum_Ioc_consecutive f (Nat.zero_le U) hUN,add_sub_cancel_right]
  have h₀ := fixedBandCenteredTail_error hN hcut
  rw [hprefix] at h₀
  have hn₀ : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hnN : (N:ℝ)=(n:ℝ)^4 := Nat.cast_pow _ _
  have hnU : (U:ℝ)=(n:ℝ)^2 := Nat.cast_pow _ _
  rw [hnU,hnN,Real.log_pow,Nat.cast_ofNat] at h₀
  let C := 72+60*|fixedBandLogConstant|
  change |_| ≤ C*((n:ℝ)^2)^2*(1+4*log n)/(n:ℝ)^4 at h₀
  rw [show C*((n:ℝ)^2)^2*(1+4*log n)/(n:ℝ)^4 = C*(1+4*log n) by field_simp] at h₀
  rw [← hnN,he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  exact (mul_le_mul_of_nonneg_left h₀ (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by dsimp [C]; ring)

/-- Removing proper powers leaves a uniform square-root error from the negative quadratic form. -/
theorem fixedBand_prime_quadratic_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 2 ≤ n →
      |dyadicPrimeDeficit ((n:ℝ)^4)+fixedBandQuadratic (n^4) (n^2)| ≤ C*(n:ℝ)^2 := by
  obtain ⟨K,hK,hp⟩ := dyadicPrimeDeficit_power_cost
  let B := 2*(72+60*|fixedBandLogConstant|)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨K+5*B,by positivity,fun {n} hn => ?_⟩
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hn₀ := zero_lt_one.trans_le hnR
  obtain ⟨hlo,hhi⟩ := hp (pow_pos hn₀ 4)
  rw [show Real.sqrt ((n:ℝ)^4)=(n:ℝ)^2 by rw [show (n:ℝ)^4=((n:ℝ)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]] at hhi
  have ht := fixedBand_quadratic_fourth_error hn
  rw [show dyadicPrimeDeficit ((n:ℝ)^4)+fixedBandQuadratic (n^4) (n^2) =
    (dyadicPrimeDeficit ((n:ℝ)^4)-dyadicContrast ((n:ℝ)^4))+
    (dyadicContrast ((n:ℝ)^4)+fixedBandQuadratic (n^4) (n^2)) by ring]
  apply (abs_add_le _ _).trans
  rw [abs_of_nonneg hlo]
  apply (add_le_add hhi ht).trans
  change K*(n:ℝ)^2+B*(1+4*log n) ≤ _
  have hl : 1+4*log n ≤ 5*(n:ℝ)^2 := by
    nlinarith only [Real.log_le_sub_one_of_pos hn₀,mul_le_mul_of_nonneg_left hnR hn₀.le,hnR]
  linarith only [mul_le_mul_of_nonneg_left hl hB]

/-- Only the negative part of the quadratic form needs a window estimate. -/
def fixedBandQuadraticMass (m b : ℕ) : ℝ :=
  ∑ n ∈ Icc m b, max (-fixedBandQuadratic (n^4) (n^2)) 0/(n:ℝ)^3

/-- A uniform square-root error per sample changes the entire fourth-power
window by at most a logarithm. -/
theorem fixedBand_mass_sqrt_error {x y : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ {n : ℕ}, 2 ≤ n → |x n-y n| ≤ C*(n:ℝ)^2) {m b : ℕ} (hm : 2 ≤ m) :
    |(∑ n ∈ Icc m b, max (x n) 0/(n:ℝ)^3)-
      ∑ n ∈ Icc m b, max (y n) 0/(n:ℝ)^3| ≤ C*(1+log b) := by
  have hi := harmonic_le_one_add_log b
  simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] at hi
  rw [← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ n ∈ Icc m b, C*(n:ℝ)⁻¹ := by
      apply sum_le_sum
      intro n hn
      have hn2 := hm.trans (mem_Icc.mp hn).1
      have hn₀ : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
      rw [← sub_div,abs_div,abs_of_nonneg (pow_nonneg hn₀.le 3)]
      apply (div_le_div_of_nonneg_right ((abs_max_sub_max_le_abs _ _ 0).trans
        (h hn2)) (pow_nonneg hn₀.le 3)).trans
      exact le_of_eq (by field_simp)
    _ ≤ _ := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg
        (Icc_subset_Icc_left (by omega : 1 ≤ m)) (fun n _ _ => inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) n))).trans hi) hC

theorem fixedBandQuadraticMass_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m b : ℕ}, 2 ≤ m →
      |fixedBandMass m b-fixedBandQuadraticMass m b| ≤ C*(1+log b) := by
  obtain ⟨C,hC,h⟩ := fixedBand_prime_quadratic_error
  exact ⟨C,hC,fun hm => fixedBand_mass_sqrt_error (x := fun n => dyadicPrimeDeficit ((n:ℝ)^4))
    (y := fun n => -fixedBandQuadratic (n^4) (n^2)) hC (fun hn => by simpa only [sub_neg_eq_add] using h hn) hm⟩

/-- The positive part of the critical-scale linear Möbius tail. -/
def fixedBandCriticalTailMass (m b : ℕ) : ℝ :=
  ∑ n ∈ Icc m b, max (fixedBandCenteredTail (n^4) (fixedBandMultipleCutoff n)) 0/(n:ℝ)^3

/-- The critical tail differs from the ordinary-prime window by O(log b). -/
theorem fixedBandCriticalTailMass_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m b : ℕ}, 2 ≤ m →
      |fixedBandMass m b-fixedBandCriticalTailMass m b| ≤ C*(1+log b) := by
  obtain ⟨C,hC,h⟩ := dyadicPrimeDeficit_power_cost
  let D := 4*(72+60*|fixedBandLogConstant|)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨C+D,by positivity,fun {m b} hm => fixedBand_mass_sqrt_error
    (x := fun n => dyadicPrimeDeficit ((n:ℝ)^4)) (y := fun n => fixedBandCenteredTail (n^4) (fixedBandMultipleCutoff n))
    (by positivity) (fun {n} hn => ?_) hm⟩
  have hn₀ : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  obtain ⟨hlo,hhi⟩ := h (pow_pos hn₀ 4)
  rw [show sqrt ((n:ℝ)^4) = (n:ℝ)^2 by rw [show (n:ℝ)^4=((n:ℝ)^2)^2 by ring,
    Real.sqrt_sq (sq_nonneg (n:ℝ))]] at hhi
  have hK := fixedBandMultipleCutoff_bounds (V := n^2) hn le_rfl (by omega)
  have hN : 4 ≤ n^4 := (by decide : 4 ≤ 2^4).trans (Nat.pow_le_pow_left hn 4)
  have ht := (fixedBandCenteredTail_error hN hK.2.2).trans (fixedBandMultipleCutoff_cost hn)
  rw [Nat.cast_pow] at ht
  apply (abs_sub_le _ (dyadicContrast ((n:ℝ)^4)) _).trans
  rw [abs_of_nonneg hlo]
  exact (add_le_add hhi ht).trans_eq (by dsimp [D]; ring)

theorem rh_of_fixedBand_upper_log_squareWindows (mass : ℕ → ℕ → ℝ)
    (hupper : ∃ K : ℝ, 0 ≤ K ∧ ∀ {m b : ℕ}, 2 ≤ m →
      fixedBandMass m b-mass m b ≤ K*(1+log b))
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A, mass m (m^2) ≤ C*(1+2*log m)) :
    RiemannHypothesis := by
  apply rh_of_fixedBandMass_log_squareWindows
  obtain ⟨C,hC,hw⟩ := h
  obtain ⟨K,hK,he⟩ := hupper
  refine ⟨C+K,by positivity,fun A => ?_⟩
  obtain ⟨m,hm,hM⟩ := hw (max 2 A)
  have hh := he (b := m^2) ((le_max_left _ _).trans hm)
  rw [Nat.cast_pow,log_pow,Nat.cast_ofNat] at hh
  exact ⟨m,(le_max_right _ _).trans hm,by linarith only [hh,hM]⟩

/-- The critical Möbius tails suffice at logarithmic mass on late square windows. -/
theorem rh_of_fixedBandCriticalTail_log_squareWindows
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A,
      fixedBandCriticalTailMass m (m^2) ≤ C*(1+2*log m)) : RiemannHypothesis := by
  apply rh_of_fixedBand_upper_log_squareWindows _ _ h
  obtain ⟨K,hK,he⟩ := fixedBandCriticalTailMass_error
  exact ⟨K,hK,fun {_ _} hm => (abs_le.mp (he hm)).2⟩

section
open scoped ArithmeticFunction.Moebius

/-- A signed multiple in the critical Möbius tail. -/
def fixedBandTailTerm (n k : ℕ) : ℝ :=
  (μ k:ℝ)*fixedBandCenteredKernel (((n^4:ℕ):ℝ)/k)

/-- The diagonal of the square of the complete signed Möbius tail. -/
def fixedBandTailDiagonal (n : ℕ) : ℝ :=
  ∑ k ∈ Ioc (fixedBandMultipleCutoff n) (n^4), (fixedBandTailTerm n k)^2

/-- The signed terms at distinct multiples in the square of the tail. -/
def fixedBandTailOffDiagonal (n : ℕ) : ℝ :=
  let S := Ioc (fixedBandMultipleCutoff n) (n^4)
  ∑ k ∈ S, ∑ l ∈ S.erase k, fixedBandTailTerm n k*fixedBandTailTerm n l

theorem fixedBandTail_sq (n : ℕ) :
    (fixedBandCenteredTail (n^4) (fixedBandMultipleCutoff n))^2 =
      fixedBandTailDiagonal n+fixedBandTailOffDiagonal n := by
  let S := Ioc (fixedBandMultipleCutoff n) (n^4)
  let a := fixedBandTailTerm n
  change (∑ k ∈ S, a k)^2 = (∑ k ∈ S, (a k)^2) + ∑ k ∈ S, ∑ l ∈ S.erase k, a k*a l
  rw [pow_two,sum_mul_sum,← sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  rw [← sum_erase_add _ _ hk,pow_two,add_comm]

/-- A uniform bound for the centered kernel on its full arithmetic range. -/
theorem fixedBandCenteredKernel_uniform {y : ℝ} (hy : 1 ≤ y) :
    |fixedBandCenteredKernel y| ≤ 72+60*|fixedBandLogConstant| := by
  have hy₀ : 0 < y := zero_lt_one.trans_le hy
  by_cases h : 2 ≤ y
  · refine (fixedBandCenteredKernel_bound h).trans ?_
    rw [mul_div_assoc]
    refine mul_le_of_le_one_right (by positivity) ((div_le_one hy₀).mpr ?_)
    linarith only [log_le_sub_one_of_pos hy₀]
  · have h₂ := (lt_of_not_ge h).le
    rw [fixedBandCenteredKernel_first hy h₂,abs_mul,abs_of_nonneg (sub_nonneg.mpr hy)]
    have hcoef : |1-eulerMascheroniConstant-log y| ≤ 1 := abs_le.mpr
      ⟨by linarith only [log_le_sub_one_of_pos hy₀,h₂,eulerMascheroniConstant_lt_two_thirds],
        by linarith only [log_nonneg hy,one_half_lt_eulerMascheroniConstant]⟩
    refine (mul_le_mul (show y-1 ≤ 1 by linarith) hcoef (abs_nonneg _) zero_le_one).trans ?_
    nlinarith only [abs_nonneg fixedBandLogConstant]

/-- The actual diagonal is paid at the square-root scale, after taking its square. -/
theorem fixedBandTailDiagonal_le (n : ℕ) :
    fixedBandTailDiagonal n ≤ (72+60*|fixedBandLogConstant|)^2*(n:ℝ)^4 := by
  let S := Ioc (fixedBandMultipleCutoff n) (n^4)
  let C := 72+60*|fixedBandLogConstant|
  have hC : 0 ≤ C := by positivity
  change (∑ k ∈ S, (fixedBandTailTerm n k)^2) ≤ C^2*(n:ℝ)^4
  calc
    _ ≤ ∑ _k ∈ S, C^2 := by
      apply sum_le_sum
      intro k hk
      obtain ⟨hk₁,hk₂⟩ := mem_Ioc.mp hk
      have hk₀ : 0 < (k:ℝ) := Nat.cast_pos.mpr ((Nat.zero_le _).trans_lt hk₁)
      have hμ : |(μ k:ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k)
      have hF : |fixedBandCenteredKernel (((n^4:ℕ):ℝ)/k)| ≤ C :=
        fixedBandCenteredKernel_uniform ((one_le_div hk₀).mpr (Nat.cast_le.mpr hk₂))
      have h := mul_le_mul hμ hF (abs_nonneg _) zero_le_one
      rw [← abs_mul,one_mul] at h
      simpa only [fixedBandTailTerm,sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
    _ ≤ _ := by
      rw [sum_const,nsmul_eq_mul,mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [← Nat.cast_pow]
      exact Nat.cast_le.mpr (by simp only [S,Nat.card_Ioc]; omega)

/-- The window covariance keeps the signs of every pair at distinct multiples. -/
def fixedBandOffDiagonalMass (m b : ℕ) : ℝ :=
  ∑ n ∈ Icc m b, fixedBandTailOffDiagonal n/(n:ℝ)^5

/-- All diagonal terms together cost only a logarithm. The budget for the
positive tail is reduced to one upper bound on the signed off-diagonal sum. -/
theorem fixedBandCriticalTailMass_offDiagonal_le {m b : ℕ} (hm : 2 ≤ m) :
    2*fixedBandCriticalTailMass m b ≤ fixedBandOffDiagonalMass m b+
      ((72+60*|fixedBandLogConstant|)^2+1)*(1+log b) := by
  let C := (72+60*|fixedBandLogConstant|)^2+1
  have hC : 0 ≤ C := by positivity
  let T (n : ℕ) := fixedBandCenteredTail (n^4) (fixedBandMultipleCutoff n)
  have he (n : ℕ) (hn : n ∈ Icc m b) :
      2*(max (T n) 0/(n:ℝ)^3) ≤ fixedBandTailOffDiagonal n/(n:ℝ)^5+C/(n:ℝ) := by
    have hn₀ : 0 < (n:ℝ) := Nat.cast_pos.mpr (by have := (mem_Icc.mp hn).1; omega)
    have hs : 2*(max (T n) 0/(n:ℝ)^3) ≤ (T n)^2/(n:ℝ)^5+1/(n:ℝ) := by
      rcases le_total 0 (T n) with h | h
      · rw [max_eq_left h]
        field_simp [hn₀.ne']
        nlinarith only [sq_nonneg (T n-(n:ℝ)^2)]
      · rw [max_eq_right h,zero_div,mul_zero]
        positivity
    refine hs.trans ?_
    rw [show (T n)^2=fixedBandTailDiagonal n+fixedBandTailOffDiagonal n from fixedBandTail_sq n]
    rw [add_div]
    have hd := div_le_div_of_nonneg_right (fixedBandTailDiagonal_le n) (by positivity : 0 ≤ (n:ℝ)^5)
    rw [show (72+60*|fixedBandLogConstant|)^2*(n:ℝ)^4/(n:ℝ)^5 =
      (72+60*|fixedBandLogConstant|)^2/(n:ℝ) by field_simp [hn₀.ne']] at hd
    dsimp only [C]
    rw [add_div]
    linarith only [hd]
  have hi := harmonic_le_one_add_log b
  simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] at hi
  unfold fixedBandCriticalTailMass fixedBandOffDiagonalMass
  rw [mul_sum]
  refine (sum_le_sum he).trans ?_
  rw [sum_add_distrib]
  apply add_le_add_right
  simp only [div_eq_mul_inv,← mul_sum]
  exact mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg
    (Icc_subset_Icc_left (by omega : 1 ≤ m)) (fun n _ _ => inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) n))).trans hi) hC

theorem rh_of_fixedBandOffDiagonalMass_log_squareWindows
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A,
      fixedBandOffDiagonalMass m (m^2) ≤ C*(1+2*log m)) : RiemannHypothesis := by
  apply rh_of_fixedBandCriticalTail_log_squareWindows
  obtain ⟨C,hC,h⟩ := h
  let D := (72+60*|fixedBandLogConstant|)^2+1
  refine ⟨C+D,by positivity,fun A => ?_⟩
  obtain ⟨m,hm,hw⟩ := h (max 2 A)
  have hm₂ : 2 ≤ m := (le_max_left 2 A).trans hm
  have he := fixedBandCriticalTailMass_offDiagonal_le (b := m^2) hm₂
  rw [Nat.cast_pow,log_pow,Nat.cast_ofNat] at he
  change _ ≤ fixedBandOffDiagonalMass m (m^2)+D*(1+2*log m) at he
  have hp : 0 ≤ (C+D)*(1+2*log m) := by positivity [log_natCast_nonneg m]
  exact ⟨m,(le_max_right 2 A).trans hm,by nlinarith only [he,hw,hp]⟩

end

/-- A cofinal exponent for negative values of the quadratic form implies the same half-plane. -/
theorem zeta_ne_zero_of_fixedBandQuadraticMass {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (h : ∀ A : ℕ, ∃ m ≥ A, fixedBandQuadraticMass m ⌈(m:ℝ)^(1+δ)⌉₊ ≤ (m:ℝ)^α)
    {s : ℂ} (hs : 1/2+α/4 < s.re) : riemannZeta s ≠ 0 := by
  let β := (α+4*s.re-2)/2
  have hβ : α < β := by dsimp [β]; linarith
  obtain ⟨C,hC,he⟩ := fixedBandQuadraticMass_error
  have hw := fixedBand_cofinal_mass_transfer fixedBandMass fixedBandQuadraticMass hC (fun {m b} hm =>
    (abs_le.mp (he hm)).2.trans (mul_le_mul_of_nonneg_left (by nlinarith only [log_natCast_nonneg b,sq_nonneg (log b)]) hC))
    hα hβ hδ₁ h
  exact zeta_ne_zero_of_fixedBandMass (hα.trans hβ) hδ hδ₁ hw (by dsimp [β]; linarith)

theorem rh_of_fixedBandQuadraticMass_powerWindows
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ A : ℕ, ∃ m ≥ A,
      fixedBandQuadraticMass m ⌈(m:ℝ)^(1+δ)⌉₊ ≤ (m:ℝ)^α) : RiemannHypothesis := by
  apply Formalism.VW.rh_of_right
  intro s hs _
  obtain ⟨δ,hδ,hδ₁,hw⟩ := h (s.re-1/2) (by linarith)
  exact zeta_ne_zero_of_fixedBandQuadraticMass (by linarith) hδ hδ₁ hw (by linarith)

private theorem lone_multiple {N a b : ℕ} (hp : 0 < a*b) (hle : a*b ≤ N) (hhi : N < 2*(a*b)) :
    fixedBandProductEntry N a b = fixedBandCenteredKernel ((N:ℝ)/(a*b)) := by
  unfold fixedBandProductEntry
  rw [sum_eq_single (a*b),ite_eq_left (dvd_refl _),Nat.cast_mul]
  · intro k hk hne
    apply ite_eq_right
    rintro ⟨j,rfl⟩
    have hj₀ : 0 < j := Nat.pos_of_ne_zero (fun h => by simp [h] at hk)
    have hj₂ : 2 ≤ j := by
      by_contra! h
      have he : j=1 := by omega
      exact hne (by simp [he])
    have hmul := Nat.mul_le_mul_right (a*b) hj₂
    rw [mul_comm j] at hmul
    exact (not_le.mpr hhi) (hmul.trans (mem_Ioc.mp hk).2)
  · intro h
    exact (h (mem_Ioc.mpr ⟨hp,hle⟩)).elim

/-- A product in the outer half of the sample contributes its first multiple alone. -/
theorem fixedBandProductEntry_first {N a b : ℕ} (hp : 0 < a*b) (hle : a*b ≤ N) (hhi : N < 2*(a*b)) :
    let y := (N:ℝ)/(a*b)
    fixedBandProductEntry N a b = (y-1)*(1-eulerMascheroniConstant-log y) := by
  have hpR : 0 < (a:ℝ)*b := by exact_mod_cast hp
  rw [lone_multiple hp hle hhi]
  exact fixedBandCenteredKernel_first ((one_le_div hpR).mpr (by exact_mod_cast hle))
    ((div_le_iff₀ hpR).mpr (by exact_mod_cast hhi.le))

/-- On this square of indices each product has a single contributing multiple. -/
theorem fixedBand_block_entry {t a b : ℕ} (ha : a ∈ Ioc (20*t) (21*t)) (hb : b ∈ Ioc (20*t) (21*t)) :
    let y := (((28*t)^2:ℕ):ℝ)/(a*b)
    16/9 ≤ y ∧ y ≤ 2 ∧ fixedBandProductEntry ((28*t)^2) a b =
      (y-1)*(1-eulerMascheroniConstant-log y) := by
  have hl := Nat.mul_lt_mul_of_lt_of_lt (mem_Ioc.mp ha).1 (mem_Ioc.mp hb).1
  have hu := Nat.mul_le_mul (mem_Ioc.mp ha).2 (mem_Ioc.mp hb).2
  have hp : 0 < a*b := lt_of_le_of_lt (Nat.zero_le _) hl
  have hle : a*b ≤ (28*t)^2 := by nlinarith only [hu]
  have hhi : (28*t)^2 < 2*(a*b) := by nlinarith only [hl]
  let y := (((28*t)^2:ℕ):ℝ)/(a*b)
  have hpR : 0 < (a:ℝ)*b := by exact_mod_cast hp
  have huR : (a:ℝ)*b ≤ (21*(t:ℝ))*(21*t) := by exact_mod_cast hu
  have hlo : 16/9 ≤ y := (le_div_iff₀ hpR).mpr (by push_cast; nlinarith only [huR])
  have hle2 : y ≤ 2 := (div_le_iff₀ hpR).mpr (by exact_mod_cast hhi.le)
  refine ⟨hlo,hle2,?_⟩
  exact fixedBandProductEntry_first hp hle hhi

/-- A macroscopic square of negative entries rules out an unconditional
lower bound of square-root size that holds for every bounded vector. -/
theorem fixedBand_negative_block {t : ℕ} (ht : 0 < t) :
    (∑ a ∈ Ioc (20*t) (21*t), ∑ b ∈ Ioc (20*t) (21*t), fixedBandProductEntry ((28*t)^2) a b)
      ≤ -(t:ℝ)^2/25 := by
  let S := Ioc (20*t) (21*t)
  have hlog : 14/25 ≤ log (16/9:ℝ) := by
    have h := sum_range_le_log_div (x := (7:ℝ)/25) (by norm_num) (by norm_num) 1
    norm_num at h ⊢
    linarith only [h]
  have hentry (a : ℕ) (ha : a ∈ S) (b : ℕ) (hb : b ∈ S) :
      fixedBandProductEntry ((28*t)^2) a b ≤ -(1/25:ℝ) := by
    let y := (((28*t)^2:ℕ):ℝ)/(a*b)
    obtain ⟨hlo,_,he⟩ := fixedBand_block_entry ha hb
    change 16/9 ≤ y at hlo
    rw [he]
    change (y-1)*(1-eulerMascheroniConstant-log y) ≤ _
    have hylog := hlog.trans (log_le_log (by norm_num : (0:ℝ)<16/9) hlo)
    have hgamma := one_half_lt_eulerMascheroniConstant
    calc
      _ ≤ (y-1)*(-3/50) := mul_le_mul_of_nonneg_left (by linarith only [hylog,hgamma]) (by linarith)
      _ ≤ _ := by linarith only [hlo]
  calc
    _ ≤ ∑ a ∈ S, ∑ _ ∈ S, -(1/25:ℝ) := sum_le_sum fun a ha => sum_le_sum fun b hb => hentry a ha b hb
    _ = _ := by
      simp only [S,sum_const,Nat.card_Ioc,show 21*t-20*t=t by omega,nsmul_eq_mul]
      ring

end RiemannGaussian.AlpogeMined
end

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.fixedBand_centered_identity,
      ``RiemannGaussian.AlpogeMined.fixedBandCenteredTail_error,
      ``RiemannGaussian.AlpogeMined.fixedBandCenteredMass_error,
      ``RiemannGaussian.AlpogeMined.zeta_ne_zero_of_fixedBandCenteredMass,
      ``RiemannGaussian.AlpogeMined.rh_of_fixedBandCenteredMass_powerWindows,
      ``RiemannGaussian.AlpogeMined.fixedBand_quadratic_identity,
      ``RiemannGaussian.AlpogeMined.fixedBand_early_multiples,
      ``RiemannGaussian.AlpogeMined.fixedBandQuadraticAfter_eq,
      ``RiemannGaussian.AlpogeMined.fixedBandQuadraticAfter_fourth_error,
      ``RiemannGaussian.AlpogeMined.fixedBand_quadratic_fourth_error,
      ``RiemannGaussian.AlpogeMined.fixedBandQuadraticMass_error,
      ``RiemannGaussian.AlpogeMined.fixedBandCoupledPrefixAt_error,
      ``RiemannGaussian.AlpogeMined.rh_of_fixedBandCriticalTail_log_squareWindows,
      ``RiemannGaussian.AlpogeMined.rh_of_fixedBandOffDiagonalMass_log_squareWindows,
      ``RiemannGaussian.AlpogeMined.rh_of_fixedBandQuadraticMass_powerWindows,
      ``RiemannGaussian.AlpogeMined.fixedBand_negative_block] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
