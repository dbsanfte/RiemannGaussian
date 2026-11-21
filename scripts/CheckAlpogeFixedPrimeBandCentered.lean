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
  have hq := mobius_unitRamp_sum h1 (by positivity : 0 ≤ (N:ℝ)/4) (by linarith : (N:ℝ)/4 ≤ N)
  rw [max_eq_left (by linarith : 0 ≤ (N:ℝ)-1)] at hp
  rw [max_eq_left (by linarith : 0 ≤ (N:ℝ)/2-1)] at hh
  rw [max_eq_left (by linarith : 0 ≤ (N:ℝ)/4-1)] at hq
  have hzero : (∑ d ∈ S, mu d*fixedBandLattice ((N:ℝ)/d))=0 := by
    calc
      _ = ∑ d ∈ S, (mu d*fixedBandUnitRamp ((N:ℝ)/d) -
            3*(mu d*fixedBandUnitRamp (((N:ℝ)/2)/d)) + 2*(mu d*fixedBandUnitRamp (((N:ℝ)/4)/d))) := by
        apply sum_congr rfl
        intro d _
        rw [fixedBandLattice_ramps (show 0 ≤ (N:ℝ)/d by positivity),div_right_comm (N:ℝ) (d:ℝ) 2,
          div_right_comm (N:ℝ) (d:ℝ) 4]
        ring
      _ = _ := by dsimp only [S,mu]; rw [sum_add_distrib,sum_sub_distrib,← mul_sum,← mul_sum,hp,hh,hq]; ring
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

/-- All small divisors, including their main contributions, can be removed at
cost O(K² log N/N) from the same finite sum. -/
theorem fixedBandCenteredTail_error {N K : ℕ} (hN : 4 ≤ N) (hK : 2*K ≤ N) :
    |dyadicContrast N-fixedBandCenteredTail N K| ≤
      (72+60*|fixedBandLogConstant|)*(K:ℝ)^2*(1+log N)/N := by
  have hN₀ : 0 < (N:ℝ) := Nat.cast_pos.mpr (by omega)
  let C := 72+60*|fixedBandLogConstant|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let f (d : ℕ) := (ArithmeticFunction.moebius d:ℝ)*fixedBandCenteredKernel ((N:ℝ)/d)
  rw [fixedBand_centered_identity hN,fixedBandCenteredTail,← sum_Ioc_consecutive f (Nat.zero_le K) (by omega : K ≤ N),add_sub_cancel_right]
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
      have hμ : |(ArithmeticFunction.moebius d:ℝ)| ≤ 1 := by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
      rw [abs_mul]
      apply (mul_le_of_le_one_left (abs_nonneg _) hμ).trans
      apply h.trans
      change C*(1+log ((N:ℝ)/d))/((N:ℝ)/d) ≤ _
      rw [show C*(1+log ((N:ℝ)/d))/((N:ℝ)/d) = C*((1+log ((N:ℝ)/d))*d/N) by field_simp]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
        (mul_le_mul (by linarith) hdk hd₀.le (by positivity [log_natCast_nonneg N])) hN₀.le) hC
    _ = _ := by simp only [sum_const,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul,C]; ring

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

private theorem product_row {N a : ℕ} (ha : a ∈ Ioc 0 N) :
    (∑ b ∈ Ioc 0 N, (ArithmeticFunction.moebius b:ℝ)*fixedBandProductEntry N a b) =
      fixedBandCenteredKernel ((N:ℝ)/a) := by
  let f (k : ℕ) := fixedBandCenteredKernel ((N:ℝ)/k)
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
      rw [fixedBandProductEntry,mul_sum]
      apply sum_congr rfl
      intro k _
      by_cases h : a*b ∣ k <;> simp [h,f]
    _ = ∑ k ∈ Ioc 0 N, ∑ b ∈ Ioc 0 N, (if a*b ∣ k then (ArithmeticFunction.moebius b:ℝ) else 0)*f k := sum_comm
    _ = ∑ k ∈ Ioc 0 N, if k=a then f k else 0 := by
      apply sum_congr rfl
      intro k hk
      rw [← sum_mul,inv hk]
      split_ifs <;> simp
    _ = _ := by simp [ha,f]

/-- Contribution with both divisors above the chosen truncation. -/
def fixedBandOuter (N V : ℕ) : ℝ :=
  ∑ a ∈ Ioc V N, ∑ b ∈ Ioc V N,
    ((ArithmeticFunction.moebius a:ℝ)*(ArithmeticFunction.moebius b:ℝ))*fixedBandProductEntry N a b

theorem fixedBandProductEntry_zero {N a b : ℕ} (h : N < a*b) : fixedBandProductEntry N a b=0 :=
  sum_eq_zero fun _ hk => ite_eq_right (fun hd =>
    (not_le.mpr h) ((Nat.le_of_dvd (mem_Ioc.mp hk).1 hd).trans (mem_Ioc.mp hk).2))

/-- The unrestricted double inversion keeps the outer square as an exact remainder. -/
theorem fixedBand_quadratic_split {N U : ℕ} (hN : 4 ≤ N) (hU : U ≤ N) :
    dyadicContrast N + fixedBandQuadratic N U =
      2*(∑ d ∈ Ioc 0 U, (ArithmeticFunction.moebius d:ℝ)*fixedBandCenteredKernel ((N:ℝ)/d)) +
        fixedBandOuter N U := by
  let S := Ioc 0 U
  let L := Ioc U N
  let mu (d : ℕ) : ℝ := ArithmeticFunction.moebius d
  let G (a b : ℕ) := (mu a*mu b)*fixedBandProductEntry N a b
  let v (a : ℕ) := mu a*fixedBandCenteredKernel ((N:ℝ)/a)
  have split (f : ℕ → ℝ) : (∑ a ∈ S, f a)+(∑ a ∈ L, f a) = ∑ a ∈ Ioc 0 N, f a :=
    sum_Ioc_consecutive f (Nat.zero_le U) hU
  have row (a : ℕ) (ha : a ∈ Ioc 0 N) : (∑ b ∈ Ioc 0 N, G a b)=v a := by
    simp only [G,mul_assoc,← mul_sum,v,mu,product_row ha]
  have symm (a b : ℕ) : G a b = G b a := by
    dsimp only [G,fixedBandProductEntry]
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
  rw [fixedBand_centered_identity hN]
  change (∑ a ∈ Ioc 0 N, v a)+(∑ a ∈ S, ∑ b ∈ S, G a b) =
    2*(∑ a ∈ S, v a)+(∑ a ∈ L, ∑ b ∈ L, G a b)
  linarith only [split v,hl,hs]

/-- At or below U², two divisors greater than U cannot occur in one product.
Splitting both indices of the full Möbius inversion leaves its small square. -/
theorem fixedBand_quadratic_identity {N U : ℕ} (hN : 4 ≤ N) (hU : U ≤ N) (hNU : N ≤ U^2) :
    dyadicContrast N + fixedBandQuadratic N U =
      2*∑ d ∈ Ioc 0 U, (ArithmeticFunction.moebius d:ℝ)*fixedBandCenteredKernel ((N:ℝ)/d) := by
  rw [fixedBand_quadratic_split hN hU]
  suffices hz : fixedBandOuter N U=0 by rw [hz,add_zero]
  apply sum_eq_zero
  intro a ha
  apply sum_eq_zero
  intro b hb
  have h := Nat.mul_lt_mul_of_lt_of_lt (mem_Ioc.mp ha).1 (mem_Ioc.mp hb).1
  rw [← pow_two] at h
  rw [fixedBandProductEntry_zero (hNU.trans_lt h),mul_zero]

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
      ``RiemannGaussian.AlpogeMined.fixedBand_quadratic_fourth_error,
      ``RiemannGaussian.AlpogeMined.fixedBandQuadraticMass_error,
      ``RiemannGaussian.AlpogeMined.rh_of_fixedBandQuadraticMass_powerWindows,
      ``RiemannGaussian.AlpogeMined.fixedBand_negative_block] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
