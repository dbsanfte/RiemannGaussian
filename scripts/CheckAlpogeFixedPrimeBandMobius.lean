import CheckAlpogeFixedPrimeBand

/-! # Small Möbius divisors in the fixed prime band -/

noncomputable section
namespace RiemannGaussian.AlpogeMined
open Finset Real
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt

/-- Continuous mass of the triangular band. -/
def fixedBandMain (y : ℝ) : ℝ := y*log 2/2

/-- Integer mass of the triangular band. On multiples of d its scale is x/d. -/
def fixedBandLattice (y : ℝ) : ℝ :=
  ∑ j ∈ Ioc 0 ⌊y⌋₊, dyadicPrimeWeight y j

/-- Logarithmic Möbius coefficient of a divisor row. -/
def fixedBandMobiusCoeff (d : ℕ) : ℝ := (μ d : ℝ)*log d

private theorem multiples {d : ℕ} (hd : 0 < d) (N : ℕ) :
    (∑ k ∈ (Ioc 0 N).filter (fun k => d ∣ k), dyadicPrimeWeight N k) =
      fixedBandLattice ((N:ℝ)/d) := by
  unfold fixedBandLattice
  rw [Nat.floor_div_natCast,Nat.floor_natCast]
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
    exact Nat.pos_of_ne_zero (fun hj => by simp [hj] at hk)
  · intro j _
    simp only [dyadicPrimeWeight,Nat.cast_mul,div_eq_mul_inv,mul_inv_rev]
    ring_nf

private theorem coeff_sum {k N : ℕ} (hk : k ∈ Ioc 0 N) :
    (∑ d ∈ Ioc 0 N, if d ∣ k then fixedBandMobiusCoeff d else 0) = -Λ k := by
  have hset : (Ioc 0 N).filter (fun d => d ∣ k) = k.divisors := by
    ext d
    simp only [mem_filter,mem_Ioc,Nat.mem_divisors]
    have hk₀ := (mem_Ioc.mp hk).1
    exact ⟨fun h => ⟨h.2,hk₀.ne'⟩,fun h => ⟨⟨Nat.pos_of_dvd_of_pos h.1 hk₀,
      (Nat.le_of_dvd hk₀ h.1).trans (mem_Ioc.mp hk).2⟩,h.1⟩⟩
  rw [← sum_filter,hset]
  exact ArithmeticFunction.sum_moebius_mul_log_eq

/-- Exact arithmetic expansion over divisors, with one weight for each multiple. -/
theorem fixedBand_moebius_identity {N : ℕ} (hN : 0 < N) :
    dyadicContrast N = fixedBandMain N + ∑ d ∈ Ioc 0 N, fixedBandMobiusCoeff d*fixedBandLattice ((N:ℝ)/d) := by
  have ht : (∑ d ∈ Ioc 0 N, fixedBandMobiusCoeff d*fixedBandLattice ((N:ℝ)/d)) =
      ∑ k ∈ Ioc 0 N, (-Λ k)*dyadicPrimeWeight N k := by
    calc
      _ = ∑ d ∈ Ioc 0 N, ∑ k ∈ Ioc 0 N, (if d ∣ k then fixedBandMobiusCoeff d else 0)*dyadicPrimeWeight N k := by
        apply sum_congr rfl
        intro d hd
        rw [← multiples (mem_Ioc.mp hd).1,sum_filter,mul_sum]
        apply sum_congr rfl
        intro k _
        by_cases hh : d ∣ k <;> simp [hh]
      _ = ∑ k ∈ Ioc 0 N, ∑ d ∈ Ioc 0 N, (if d ∣ k then fixedBandMobiusCoeff d else 0)*dyadicPrimeWeight N k := sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro k hk
        rw [← sum_mul,coeff_sum hk]
  rw [dyadicContrast_prime_power (Nat.cast_pos.mpr hN),Nat.floor_natCast,ht]
  simp only [fixedBandMain,neg_mul,sum_neg_distrib,sub_eq_add_neg]

/-- Exact large-divisor rows joined to the continuous means of the small divisors. -/
def fixedBandMobiusTail (N K : ℕ) : ℝ :=
  fixedBandMain N + ∑ d ∈ Ioc 0 N, fixedBandMobiusCoeff d *
    (if d ≤ K then fixedBandMain ((N:ℝ)/d) else fixedBandLattice ((N:ℝ)/d))

/-- Replacing all divisor rows through K by their means costs at most K log K,
including their signed Möbius weights. -/
theorem fixedBandMobiusTail_error {N K : ℕ} (hN : 0 < N) :
    |dyadicContrast N-fixedBandMobiusTail N K| ≤ (K:ℝ)*log K := by
  rw [fixedBand_moebius_identity hN,fixedBandMobiusTail,add_sub_add_left_eq_sub,← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ d ∈ Ioc 0 N, if d ≤ K then log K else 0 := by
      apply sum_le_sum
      intro d hd
      by_cases h : d ≤ K
      · simp only [ite_eq_left h,← mul_sub,abs_mul]
        have hd₀ := (mem_Ioc.mp hd).1
        have hlog := Real.log_nonneg (show (1:ℝ) ≤ d by exact_mod_cast hd₀)
        have hc : |fixedBandMobiusCoeff d| ≤ log K := by
          have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
          rw [fixedBandMobiusCoeff,abs_mul,abs_of_nonneg hlog]
          exact (mul_le_mul_of_nonneg_right hμ hlog).trans ((one_mul _).le.trans
            (Real.log_le_log (Nat.cast_pos.mpr hd₀) (Nat.cast_le.mpr h)))
        have he : |fixedBandLattice ((N:ℝ)/d)-fixedBandMain ((N:ℝ)/d)| ≤ 1 := by
          rw [abs_sub_comm]; exact fixedBand_lattice_error (div_pos (Nat.cast_pos.mpr hN) (Nat.cast_pos.mpr hd₀))
        calc _ ≤ |fixedBandMobiusCoeff d| * 1 := mul_le_mul_of_nonneg_left he (abs_nonneg _)
             _ ≤ _ := (mul_one _).le.trans hc
      · simp [h]
    _ ≤ _ := by
      rw [← sum_filter,sum_const,nsmul_eq_mul]
      have hs : ((Ioc 0 N).filter (fun d => d ≤ K)) ⊆ Ioc 0 K :=
        fun d hd => mem_Ioc.mpr ⟨(mem_Ioc.mp (mem_filter.mp hd).1).1,(mem_filter.mp hd).2⟩
      have hc := card_le_card hs
      simp only [Nat.card_Ioc,Nat.sub_zero] at hc
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (Real.log_natCast_nonneg _)

/-- At a fourth power the cost of every small divisor and every proper power
fits in the square-root scale with one logarithm. -/
theorem fixedBandMobius_fourth_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 1 ≤ n →
      |dyadicPrimeDeficit ((n:ℝ)^4)-fixedBandMobiusTail (n^4) (n^2)| ≤
        C*(n:ℝ)^2*(1+log n) := by
  obtain ⟨K,hK,hp⟩ := dyadicPrimeDeficit_power_cost
  refine ⟨K+2,by positivity,fun {n} hn => ?_⟩
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ := zero_lt_one.trans_le hnR
  obtain ⟨hlo,hhi⟩ := hp (pow_pos hn₀ 4)
  have hroot : Real.sqrt ((n:ℝ)^4) = (n:ℝ)^2 := by
    rw [show (n:ℝ)^4 = ((n:ℝ)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
  rw [hroot] at hhi
  have hm := fixedBandMobiusTail_error (K := n^2) (pow_pos (by omega : 0 < n) 4)
  push_cast at hm
  rw [Real.log_pow] at hm
  calc
    _ ≤ |dyadicPrimeDeficit ((n:ℝ)^4)-dyadicContrast ((n:ℝ)^4)| +
        |dyadicContrast ((n:ℝ)^4)-fixedBandMobiusTail (n^4) (n^2)| := abs_sub_le _ _ _
    _ ≤ _ := by
      rw [abs_of_nonneg hlo]
      apply (add_le_add hhi (show _ ≤ (n:ℝ)^2*(2*log n) by simpa only [Nat.cast_ofNat] using hm)).trans
      nlinarith only [sq_nonneg (n:ℝ),mul_nonneg (mul_nonneg hK (sq_nonneg (n:ℝ))) (Real.log_nonneg hnR)]

/-- Positive mass of the remaining signed Möbius expression. -/
def fixedBandMobiusMass (m b : ℕ) : ℝ :=
  ∑ n ∈ Icc m b, max (fixedBandMobiusTail (n^4) (n^2)) 0/(n:ℝ)^3

/-- Pointwise square-root times logarithmic errors cost one logarithmic square on a window. -/
theorem fixedBand_positive_mass_error (T : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ {n : ℕ}, 2 ≤ n → |dyadicPrimeDeficit ((n:ℝ)^4)-T n| ≤ C*(n:ℝ)^2*(1+log n))
    {m b : ℕ} (hm : 2 ≤ m) :
    |fixedBandMass m b-(∑ n ∈ Icc m b, max (T n) 0/(n:ℝ)^3)| ≤ C*(1+log b)^2 := by
  have hi := harmonic_le_one_add_log b
  simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] at hi
  unfold fixedBandMass fixedBandSample
  rw [← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ n ∈ Icc m b, (C*(1+log b))*(n:ℝ)⁻¹ := by
      apply sum_le_sum
      intro n hn
      have hn1 : 1 ≤ n := (by omega : 1 ≤ m).trans (mem_Icc.mp hn).1
      have hn₀ : (0:ℝ) < n := Nat.cast_pos.mpr hn1
      have hl := Real.log_le_log hn₀ (Nat.cast_le.mpr (mem_Icc.mp hn).2)
      rw [← sub_div,abs_div,abs_of_nonneg (pow_nonneg hn₀.le 3)]
      apply (div_le_div_of_nonneg_right ((abs_max_sub_max_le_abs _ _ 0).trans (h (hm.trans (mem_Icc.mp hn).1)))
        (pow_nonneg hn₀.le 3)).trans
      calc _ = (C*(1+log n))*(n:ℝ)⁻¹ := by field_simp
           _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC) (by positivity)
    _ ≤ _ := by
      rw [← mul_sum,show C*(1+log b)^2 = (C*(1+log b))*(1+log b) by ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity [Real.log_natCast_nonneg b])
      exact (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_left (by omega : 1 ≤ m))
        (fun n _ _ => inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) n))).trans hi

/-- The replacement of all small divisors and proper prime powers costs only
a logarithmic square on the entire window. -/
theorem fixedBandMobiusMass_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m b : ℕ}, 2 ≤ m →
      |fixedBandMass m b-fixedBandMobiusMass m b| ≤ C*(1+log b)^2 := by
  obtain ⟨C,hC,h⟩ := fixedBandMobius_fourth_error
  exact ⟨C,hC,fun hm => fixedBand_positive_mass_error _ hC (fun hn => h (by omega)) hm⟩

/-- A logarithmic-square error preserves cofinal power bounds with any exponent slack. -/
theorem fixedBand_cofinal_mass_transfer (F H : ℕ → ℕ → ℝ) {C α β δ : ℝ} (hC : 0 ≤ C)
    (he : ∀ {m b : ℕ}, 2 ≤ m → F m b-H m b ≤ C*(1+log b)^2)
    (hα : 0 < α) (hβ : α < β) (hδ₁ : δ ≤ 1)
    (h : ∀ A : ℕ, ∃ m ≥ A, H m ⌈(m:ℝ)^(1+δ)⌉₊ ≤ (m:ℝ)^α) :
    ∀ A : ℕ, ∃ m ≥ A, F m ⌈(m:ℝ)^(1+δ)⌉₊ ≤ (m:ℝ)^β := by
  intro A
  have he₂ : 0 < α/2 := by positivity
  have hl := (isLittleO_log_rpow_atTop he₂).bound (by norm_num : (0:ℝ)<1)
  obtain ⟨T,hT⟩ := Filter.eventually_atTop.mp (hl.and
    ((tendsto_rpow_atTop (sub_pos.mpr hβ)).eventually_ge_atTop (1+9*C)))
  obtain ⟨m,hm,hM⟩ := h (max (max A 2) ⌈T⌉₊)
  have hm2 : 2 ≤ m := by omega
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hm₀ := zero_lt_one.trans_le hmR
  obtain ⟨hlog,hscale⟩ := hT m (Nat.ceil_le.mp ((le_max_right _ _).trans hm))
  change ‖log m‖ ≤ 1*‖(m:ℝ)^(α/2)‖ at hlog
  simp only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hmR),
    abs_of_pos (Real.rpow_pos_of_pos hm₀ _),one_mul] at hlog
  let b := ⌈(m:ℝ)^(1+δ)⌉₊
  have hb₀ : 0 < (b:ℝ) := (Real.rpow_pos_of_pos hm₀ _).trans_le (Nat.le_ceil _)
  have hb : b ≤ m^2 := Nat.ceil_le.mpr (by
    rw [Nat.cast_pow,← Real.rpow_natCast (m:ℝ) 2]
    apply Real.rpow_le_rpow_of_exponent_le hmR
    norm_num; linarith)
  have hlb := Real.log_le_log hb₀ (show (b:ℝ) ≤ (m:ℝ)^2 by exact_mod_cast hb)
  rw [Real.log_pow,Nat.cast_ofNat] at hlb
  have hs := pow_le_pow_left₀ (by positivity [log_natCast_nonneg b] : 0 ≤ 1+log b)
    (show 1+log b ≤ 3*(m:ℝ)^(α/2) by linarith only [hlog,hlb,Real.one_le_rpow hmR he₂.le]) 2
  rw [mul_pow,← Real.rpow_mul_natCast hm₀.le,show α/2*(2:ℕ) = α by ring] at hs
  change H m b ≤ _ at hM
  refine ⟨m,by omega,?_⟩
  calc F m b ≤ (1+9*C)*(m:ℝ)^α := by nlinarith only [hM,he (b := b) hm2,mul_le_mul_of_nonneg_left hs hC]
       _ ≤ (m:ℝ)^(β-α)*(m:ℝ)^α := mul_le_mul_of_nonneg_right hscale (by positivity)
       _ = _ := by rw [← Real.rpow_add hm₀,sub_add_cancel]

/-- Previously available prime-mass exponents also apply to the signed divisor
sum with arbitrarily small exponent slack, on the same cofinal starts. -/
theorem fixedBandMobiusMass_of_prime_windows {α β δ : ℝ} (hα : 0 < α) (hβ : α < β)
    (hδ₁ : δ ≤ 1)
    (h : ∀ A : ℕ, ∃ m ≥ A, fixedBandMass m ⌈(m:ℝ)^(1+δ)⌉₊ ≤ (m:ℝ)^α) :
    ∀ A : ℕ, ∃ m ≥ A, fixedBandMobiusMass m ⌈(m:ℝ)^(1+δ)⌉₊ ≤ (m:ℝ)^β := by
  obtain ⟨C,hC,he⟩ := fixedBandMobiusMass_error
  exact fixedBand_cofinal_mass_transfer _ _ hC (fun {m b} hm => by linarith only [(abs_le.mp (he (b := b) hm)).1])
    hα hβ hδ₁ h

/-- A single exponent for the signed divisor sum gives the same zero half-plane
as the direct prime statistic. -/
theorem zeta_ne_zero_of_fixedBandMobiusMass {α δ : ℝ} (hα : 0 < α)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (h : ∀ A : ℕ, ∃ m ≥ A, fixedBandMobiusMass m ⌈(m:ℝ)^(1+δ)⌉₊ ≤ (m:ℝ)^α)
    {s : ℂ} (hs : 1/2+α/4 < s.re) : riemannZeta s ≠ 0 := by
  let β := (α+4*s.re-2)/2
  have hβ : α < β := by dsimp [β]; linarith
  obtain ⟨C,hC,he⟩ := fixedBandMobiusMass_error
  have hw := fixedBand_cofinal_mass_transfer fixedBandMass fixedBandMobiusMass hC
    (fun hm => (abs_le.mp (he hm)).2) hα hβ hδ₁ h
  exact zeta_ne_zero_of_fixedBandMass (hα.trans hβ) hδ hδ₁ hw (by dsimp [β]; linarith)

/-- Subpower control of the remaining signed divisor rows on cofinal power windows
suffices for the short proof. -/
theorem rh_of_fixedBandMobiusMass_powerWindows
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ A : ℕ, ∃ m ≥ A,
      fixedBandMobiusMass m ⌈(m:ℝ)^(1+δ)⌉₊ ≤ (m:ℝ)^α) : RiemannHypothesis := by
  apply Formalism.VW.rh_of_right
  intro s hs _
  obtain ⟨δ,hδ,hδ₁,hw⟩ := h (s.re-1/2) (by linarith)
  exact zeta_ne_zero_of_fixedBandMobiusMass (by linarith) hδ hδ₁ hw (by linarith)

/-- One can fix the end at m² when bounding every positive exponent. -/
theorem rh_of_fixedBandMobiusMass_squareWindows
    (h : ∀ α : ℝ, 0 < α → ∀ A : ℕ, ∃ m ≥ A, fixedBandMobiusMass m (m^2) ≤ (m:ℝ)^α) :
    RiemannHypothesis := by
  apply rh_of_fixedBandMobiusMass_powerWindows
  intro α hα
  refine ⟨1,one_pos,le_rfl,fun A => ?_⟩
  obtain ⟨m,hm,hw⟩ := h α hα A
  refine ⟨m,hm,?_⟩
  rwa [show (1:ℝ)+1=2 by norm_num,Real.rpow_two,← Nat.cast_pow,Nat.ceil_natCast]

end RiemannGaussian.AlpogeMined
end

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.fixedBand_moebius_identity,
      ``RiemannGaussian.AlpogeMined.fixedBandMobiusTail_error,
      ``RiemannGaussian.AlpogeMined.fixedBandMobiusMass_error,
      ``RiemannGaussian.AlpogeMined.fixedBandMobiusMass_of_prime_windows,
      ``RiemannGaussian.AlpogeMined.zeta_ne_zero_of_fixedBandMobiusMass,
      ``RiemannGaussian.AlpogeMined.rh_of_fixedBandMobiusMass_squareWindows] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
