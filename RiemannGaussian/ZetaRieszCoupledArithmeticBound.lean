/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCoupledSignedBound

/-!
# Independent arithmetic radius bounds for the joined energy minus credit

The ordinary-prime moments have a proved Cauchy radius strictly greater
than one half at each fixed nonzero height. Factor their COMMON total
order before estimating the joined signed incidence. Its entire radius-
matched correlation credit remains negative. The radius is not assumed
to exceed the requested source radius; that distinction is the remaining
arithmetic obstruction at heights beyond the existing zero-free coverage.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszCoupledArithmeticBound
open ZetaRieszCoupledSignedBound ZetaRieszPairPrimePowerPayment

/-- Normalize only for the inequality; the arithmetic carrier stays unchanged. -/
def radiusArray (a : ℕ → ℂ) (q : ℝ) (i : ℕ) : ℂ := a i/(q : ℂ)^i

private theorem product_rescale (a : ℕ → ℂ) {q : ℝ} (hq : 0 < q)
    {N i : ℕ} (hi : i < N) :
    a i*a (N-1-i)=(q : ℂ)^(N-1)*
      (radiusArray a q i*radiusArray a q (N-1-i)) := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  have ht : i+(N-1-i)=N-1 := by omega
  unfold radiusArray
  rw [div_mul_div_comm,←pow_add,ht]
  field_simp

/-- The two different individual orders share EXACTLY one geometric factor.
The signed credit is transported with the sum, rather than bounded separately. -/
theorem energy_sub_credit_rescale (a : ℕ → ℂ) {q : ℝ} (hq : 0 < q)
    (N K : ℕ) (b : ℝ) :
    diagonalEnergy a N K b-correlationCredit a N K b=
      q^(N-1)*(diagonalEnergy (radiusArray a q) N K b-
        correlationCredit (radiusArray a q) N K b) := by
  rw [←joined_real_eq_energy_sub_credit,←joined_real_eq_energy_sub_credit]
  have he : (∑ i∈Finset.range N, (symmetricWeight N K b i : ℂ)*a i*a (N-1-i))=
      (q : ℂ)^(N-1)*∑ i∈Finset.range N,
        (symmetricWeight N K b i : ℂ)*radiusArray a q i*radiusArray a q (N-1-i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_assoc,product_rescale a hq (Finset.mem_range.mp hi)]
    ring
  rw [he,←Complex.ofReal_pow,Complex.re_ofReal_mul]

/-- A signed bound which RETAINS the entire radius-matched correlation credit. -/
theorem energy_sub_credit_le_radius_credit (a : ℕ → ℂ) {q C : ℝ}
    (hq : 0 < q) {N K : ℕ} (b : ℝ)
    (ha : ∀ i < N, ‖a i‖ ≤ C*q^i) :
    diagonalEnergy a N K b-correlationCredit a N K b ≤
      q^(N-1)*(C^2*weightVariation N K b-
        correlationCredit (radiusArray a q) N K b) := by
  have he i (hi : i < N) : ‖radiusArray a q i‖ ≤ C := by
    unfold radiusArray
    rw [norm_div,norm_pow,Complex.norm_real,Real.norm_of_nonneg hq.le]
    exact (div_le_iff₀ (pow_pos hq i)).mpr (ha i hi)
  rw [energy_sub_credit_rescale a hq]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq.le _)
  exact sub_le_sub_right (diagonalEnergy_le_variation _ b he) _

/-- Two-sided control of the joined signed expression, with its correlated
TOTAL order retained. This is not the much larger diagonal energy alone. -/
theorem abs_energy_sub_credit_le_radius (a : ℕ → ℂ) {q C : ℝ}
    (hq : 0 < q) {N K : ℕ} (b : ℝ)
    (ha : ∀ i < N, ‖a i‖ ≤ C*q^i) :
    |diagonalEnergy a N K b-correlationCredit a N K b| ≤
      C^2*q^(N-1)*weightVariation N K b := by
  have hd i (hi : i < N) : ‖radiusArray a q i‖ ≤ C := by
    unfold radiusArray
    rw [norm_div,norm_pow,Complex.norm_real,Real.norm_of_nonneg hq.le]
    exact (div_le_iff₀ (pow_pos hq i)).mpr (ha i hi)
  rw [energy_sub_credit_rescale a hq,←joined_real_eq_energy_sub_credit,
    abs_mul,abs_of_nonneg (pow_nonneg hq.le _)]
  have hh : |(∑ i∈Finset.range N,
      (symmetricWeight N K b i : ℂ)*radiusArray a q i*
        radiusArray a q (N-1-i)).re| ≤ C^2*weightVariation N K b := by
    apply (Complex.abs_re_le_norm _).trans
    apply (norm_sum_le _ _).trans
    unfold weightVariation
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hiN := Finset.mem_range.mp hi
    have hjN : N-1-i < N := by omega
    have hC : 0 ≤ C := (norm_nonneg _).trans (hd i hiN)
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have hp := mul_le_mul (hd i hiN) (hd _ hjN) (norm_nonneg _) hC
    calc
      _ = |symmetricWeight N K b i| *
          (‖radiusArray a q i‖*‖radiusArray a q (N-1-i)‖) := by ring
      _ ≤ |symmetricWeight N K b i| * (C*C) :=
        mul_le_mul_of_nonneg_left hp (abs_nonneg _)
      _ = _ := by ring
  exact (mul_le_mul_of_nonneg_left hh (pow_nonneg hq.le _)).trans_eq (by ring)

private theorem native_central_price {N : ℕ} (hN : 65536 ≤ N) :
    (∑ i∈Finset.range N,
      if 13*N/32 ≤ i ∧ i < N-13*N/32 then 1/((N-i : ℕ) : ℝ) else 0) ≤ (1/2 : ℝ) := by
  let K := 13*N/32
  let S := (Finset.range N).filter (fun i => K ≤ i ∧ i < N-K)
  have hKN : K ≤ N := by dsimp [K]; omega
  have hset : S=Finset.Ico K (N-K) := by
    ext i
    simp only [S,Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
    omega
  have hcard : S.card=N-2*K := by rw [hset,Nat.card_Ico]; omega
  have hden : (0 : ℝ) < ((K+1 : ℕ) : ℝ) := by positivity
  have hi : ∀ i∈S, 1/((N-i : ℕ) : ℝ) ≤ 1/((K+1 : ℕ) : ℝ) := by
    intro i hi
    simp only [S,Finset.mem_filter,Finset.mem_range] at hi
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast (show K+1 ≤ N-i by omega)
  change (∑ i∈Finset.range N, if K ≤ i ∧ i < N-K then _ else _) ≤ _
  rw [←Finset.sum_filter]
  calc
    _ ≤ ∑ _i∈S, (1 : ℝ)/((K+1 : ℕ) : ℝ) := Finset.sum_le_sum hi
    _ = ((N-2*K : ℕ) : ℝ)/((K+1 : ℕ) : ℝ) := by
      simp only [Finset.sum_const,nsmul_eq_mul,hcard,div_eq_mul_inv,one_mul]
    _ ≤ _ := by
      apply (div_le_iff₀ hden).mpr
      have hn : 2*(N-2*K) ≤ K+1 := by dsimp [K]; omega
      have hr : 2*((N-2*K : ℕ) : ℝ) ≤ ((K+1 : ℕ) : ℝ) := by exact_mod_cast hn
      linarith only [hr]

private theorem native_successor_price {N : ℕ} (hN : 65536 ≤ N) :
    (∑ i∈Finset.range N, successorWeight N (13*N/32) i) ≤ (3/2 : ℝ) := by
  let K := 13*N/32
  let S := (Finset.range N).filter (fun i => i ≤ N-K)
  have hK : 0 < K := by dsimp [K]; omega
  have hKN : K ≤ N := by dsimp [K]; omega
  have hset : S=Finset.Icc 0 (N-K) := by
    ext i
    simp only [S,Finset.mem_filter,Finset.mem_range,Finset.mem_Icc]
    omega
  have hcard : S.card=N-K+1 := by rw [hset,Nat.card_Icc]; omega
  have hden : (0 : ℝ) < ((K+1 : ℕ) : ℝ) := by positivity
  have hi : ∀ i∈S, 1/((N+1-i : ℕ) : ℝ) ≤ 1/((K+1 : ℕ) : ℝ) := by
    intro i hi
    simp only [S,Finset.mem_filter,Finset.mem_range] at hi
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast (show K+1 ≤ N+1-i by omega)
  change (∑ i∈Finset.range N, if i ≤ N-K then _ else _) ≤ _
  rw [←Finset.sum_filter]
  calc
    _ ≤ ∑ _i∈S, (1 : ℝ)/((K+1 : ℕ) : ℝ) := Finset.sum_le_sum hi
    _ = ((N-K+1 : ℕ) : ℝ)/((K+1 : ℕ) : ℝ) := by
      simp only [Finset.sum_const,nsmul_eq_mul,hcard,div_eq_mul_inv,one_mul]
    _ ≤ _ := by
      apply (div_le_iff₀ hden).mpr
      have hn : 2*(N-K+1) ≤ 3*(K+1) := by dsimp [K]; omega
      have hr : 2*((N-K+1 : ℕ) : ℝ) ≤ 3*((K+1 : ℕ) : ℝ) := by exact_mod_cast hn
      linarith only [hr]

/-- A finite UNIFORM price for every native order, not a sampled certificate.
The actual signed credit is still retained by the arithmetic inequality below. -/
theorem weightVariation_native_le {N : ℕ} (hN : 65536 ≤ N) {b : ℝ}
    (hbl : 1 ≤ b) (hbu : b ≤ 3/2) :
    weightVariation N (13*N/32) b ≤ (41/12 : ℝ) := by
  have hc := native_central_price hN
  have hp := native_successor_price hN
  have hp0 : 0 ≤ ∑ i∈Finset.range N, successorWeight N (13*N/32) i := by
    unfold successorWeight
    positivity
  have hmul := mul_le_mul hbu hp hp0 (by norm_num : (0 : ℝ) ≤ 3/2)
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hs : separateVariation N (13*N/32) b=
      1+(∑ i∈Finset.range N,
        if 13*N/32 ≤ i ∧ i < N-13*N/32 then 1/((N-i : ℕ) : ℝ) else 0)+
        b*∑ i∈Finset.range N, successorWeight N (13*N/32) i := by
    unfold separateVariation positiveWeight
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.mul_sum]
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    field_simp
  have ht := weightVariation_native_contraction hN hbl
  rw [hs] at ht
  linarith only [ht,hc,hmul]

/-- Apply an independently proved ordinary-prime radius. The bound is for
the actual arithmetic `D-Q`, with EVERY phase and low order retained. -/
theorem ordinary_energy_sub_credit_le {R C u y : ℝ} (hR : 0 < R)
    (hu : 0 < u)
    (hm : ∀ k, ‖zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)‖ ≤ C/R^k)
    (N : ℕ) :
    diagonalEnergy (ordinaryArray u y) N (13*N/32) (lengthFactor u N)-
      correlationCredit (ordinaryArray u y) N (13*N/32) (lengthFactor u N) ≤
      (u/R)^(N-1)*((C*u)^2*weightVariation N (13*N/32) (lengthFactor u N)-
        correlationCredit (radiusArray (ordinaryArray u y) (u/R)) N (13*N/32)
          (lengthFactor u N)) := by
  apply energy_sub_credit_le_radius_credit _ (div_pos hu hR)
  intro k _
  unfold ordinaryArray
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu.le]
  apply (mul_le_mul_of_nonneg_left (hm k) (pow_nonneg hu.le _)).trans_eq
  rw [div_pow,pow_succ]
  ring

/-- A quantitative independent two-sided arithmetic estimate. There is
one `u/R` exponent, not a lost individual-leg or absolute source exponent. -/
theorem abs_ordinary_energy_sub_credit_le {R C u y : ℝ} (hR : 0 < R)
    (hu : 1/2 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hm : ∀ k, ‖zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)‖ ≤ C/R^k)
    {N : ℕ} (hN : 65536 ≤ N) :
    |diagonalEnergy (ordinaryArray u y) N (13*N/32) (lengthFactor u N)-
      correlationCredit (ordinaryArray u y) N (13*N/32) (lengthFactor u N)| ≤
      (41/12 : ℝ)*(C*u)^2*(u/R)^(N-1) := by
  have hu0 : 0 < u := by linarith only [hu]
  have hb := lengthFactor_bounds hu hU hN
  have ha k : ‖ordinaryArray u y k‖ ≤ (C*u)*(u/R)^k := by
    unfold ordinaryArray
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu0.le]
    apply (mul_le_mul_of_nonneg_left (hm k) (pow_nonneg hu0.le _)).trans_eq
    rw [div_pow,pow_succ]
    ring
  exact (abs_energy_sub_credit_le_radius _ (div_pos hu0 hR) _
    (fun k _ => ha k)).trans
      ((mul_le_mul_of_nonneg_left (weightVariation_native_le hN hb.1 hb.2)
        (by positivity : 0 ≤ (C*u)^2*(u/R)^(N-1))).trans_eq (by ring))

/-- The radius here follows from actual zeta nonvanishing on `Re=1`.
It may be smaller than `u`; no exposed zero or source assumption is used. -/
theorem exists_independent_arithmetic_radius {y : ℝ} (hy : 54 ≤ |y|) :
    ∃ R C : ℝ, 1/2 < R ∧ R < 3/4 ∧ 0 < C ∧
      ∀ u : ℝ, 1/2 ≤ u → u ≤ ZetaRieszWideOwnerAudit.radiusCeiling →
        ∀ N : ℕ, 65536 ≤ N →
          |diagonalEnergy (ordinaryArray u y) N (13*N/32) (lengthFactor u N)-
            correlationCredit (ordinaryArray u y) N (13*N/32) (lengthFactor u N)| ≤
              (41/12 : ℝ)*(C*u)^2*(u/R)^(N-1) := by
  obtain ⟨R,C,hRl,hRu,hC,hm⟩ := ZetaRieszJoinedPhaseRadius.exists_ordinary_moment_bound hy
  exact ⟨R,C,hRl,hRu,hC,fun _ hu hU _ hN =>
    abs_ordinary_energy_sub_credit_le (by linarith only [hRl]) hu hU hm hN⟩

/-- A concrete independent bound on the existing proved height range.
The constant depends on height, while the GEOMETRIC ratio is explicit
and uniform over the requested radius strip. No zero hypothesis enters. -/
theorem exists_concrete_arithmetic_bound {y : ℝ} (hy : 54 ≤ |y|)
    (hlog : log (|y|+3) ≤ 1800) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 1/2 ≤ u →
      u ≤ ZetaRieszWideOwnerAudit.radiusCeiling → ∀ N : ℕ, 65536 ≤ N →
        |diagonalEnergy (ordinaryArray u y) N (13*N/32) (lengthFactor u N)-
          correlationCredit (ordinaryArray u y) N (13*N/32) (lengthFactor u N)| ≤
            C^2*(100010/100011 : ℝ)^(N-1) := by
  obtain ⟨C,hC,hm⟩ := ZetaRieszJoinedPhaseRadius.exists_ordinary_bound_concrete_height hy hlog
  refine ⟨C,hC,fun u hu hU N hN => ?_⟩
  have hu0 : 0 ≤ u := by linarith only [hu]
  have hUq : u ≤ (10001/20000 : ℝ) := hU
  have hq : u/(100011/200000 : ℝ) ≤ (100010/100011 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 100011/200000)).mpr
    linarith only [hUq]
  have hs : (41/12 : ℝ)*u^2 ≤ 1 := by
    have hh := pow_le_pow_left₀ hu0 hUq 2
    nlinarith only [hh]
  have hr := pow_le_pow_left₀ (div_nonneg hu0 (by norm_num)) hq (N-1)
  have hq0 : 0 ≤ u/(100011/200000 : ℝ) := div_nonneg hu0 (by norm_num)
  have hb := abs_ordinary_energy_sub_credit_le (by norm_num : (0 : ℝ) < 100011/200000)
    hu hU hm hN
  calc
    _ ≤ (41/12 : ℝ)*(C*u)^2*(u/(100011/200000 : ℝ))^(N-1) := hb
    _ ≤ C^2*(u/(100011/200000 : ℝ))^(N-1) := by
      have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg C)
      have he := mul_le_mul_of_nonneg_right hh
        (pow_nonneg hq0 (N-1))
      simpa only [mul_pow,mul_assoc,mul_comm,mul_left_comm,mul_one] using he
    _ ≤ _ := mul_le_mul_of_nonneg_left hr (sq_nonneg C)

/-- An actual independent cofinal bound for `D-Q`, uniformly in the whole
radius strip at each fixed height ALREADY covered by the proved region.
This does not assert new zero-free coverage at uncovered heights. -/
theorem eventually_energy_sub_credit_lt_target_of_log_height {y : ℝ}
    (hy : 54 ≤ |y|) (hlog : log (|y|+3) ≤ 1800) :
    ∀ᶠ N : ℕ in atTop, ∀ u : ℝ, 1/2 ≤ u →
      u ≤ ZetaRieszWideOwnerAudit.radiusCeiling →
        diagonalEnergy (ordinaryArray u y) N (13*N/32) (lengthFactor u N)-
          correlationCredit (ordinaryArray u y) N (13*N/32) (lengthFactor u N)
            < (399/5000 : ℝ) := by
  obtain ⟨C,_,hb⟩ := exists_concrete_arithmetic_bound hy hlog
  have ht : Tendsto (fun N : ℕ => C^2*(100010/100011 : ℝ)^(N-1))
      atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 100010/100011)
        (by norm_num : (100010/100011 : ℝ) < 1)).comp (tendsto_sub_atTop_nat 1)).const_mul (C^2)
  filter_upwards [eventually_ge_atTop (65536 : ℕ),ht.eventually_lt_const
    (by norm_num : (0 : ℝ) < 399/5000)] with N hN hsmall
  intro u hu hU
  exact ((le_abs_self _).trans (hb u hu hU N hN)).trans_lt hsmall

/-- The new independent arithmetic estimate really tends to zero on this
proved height range, rather than being an assumed bound on a new scalar. -/
theorem tendsto_energy_sub_credit_of_log_height {y u : ℝ} (hy : 54 ≤ |y|)
    (hlog : log (|y|+3) ≤ 1800) (hu : 1/2 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N : ℕ =>
      diagonalEnergy (ordinaryArray u y) N (13*N/32) (lengthFactor u N)-
        correlationCredit (ordinaryArray u y) N (13*N/32) (lengthFactor u N))
      atTop (𝓝 0) := by
  obtain ⟨C,_,hb⟩ := exists_concrete_arithmetic_bound hy hlog
  have ht : Tendsto (fun N : ℕ => C^2*(100010/100011 : ℝ)^(N-1))
      atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 100010/100011)
        (by norm_num : (100010/100011 : ℝ) < 1)).comp (tendsto_sub_atTop_nat 1)).const_mul (C^2)
  exact squeeze_zero_norm' ((eventually_ge_atTop 65536).mono fun N hN => by
    simpa only [Real.norm_eq_abs] using hb u hu hU N hN) ht

/-- The only exposed-source error inserted in the final transfer is an
already proved adjacent-order payment, with its finite source-error mass. -/
def adjacentSourcePrice (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  12*((analyticZetaZeroMultiplicity rho : ℝ)+ZetaRieszJoinedSourceError.sourceErrorMass rho)*
    ZetaRieszJoinedSourceError.sourceErrorMass rho/((N+1 : ℕ) : ℝ)

theorem adjacentSourcePrice_tendsto (rho : NontrivialZetaZero) :
    Tendsto (adjacentSourcePrice rho) atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ =>
    12*((analyticZetaZeroMultiplicity rho : ℝ)+ZetaRieszJoinedSourceError.sourceErrorMass rho)*
      ZetaRieszJoinedSourceError.sourceErrorMass rho/((N+1 : ℕ) : ℝ)) atTop (𝓝 0)
  simpa only [div_eq_mul_inv,one_div,one_mul,mul_zero,Function.comp_def] using
    ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)).const_mul
        (12*((analyticZetaZeroMultiplicity rho : ℝ)+ZetaRieszJoinedSourceError.sourceErrorMass rho)*
          ZetaRieszJoinedSourceError.sourceErrorMass rho)

/-- Transfer the ACTUAL arithmetic target directly to the existing
all-multiplicity endpoint. The target remains a premise at uncovered
heights; no extra credit or source is silently spent in this transfer. -/
theorem false_of_cofinal_energy_sub_credit_bound (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau≠rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (orders : ℕ → ℕ) (horders : Tendsto orders atTop atTop)
    (err : ℕ → ℝ) (he : Tendsto err atTop (𝓝 0))
    (hf : ∃ᶠ j in atTop,
      diagonalEnergy (ordinaryArray (3/2-rho.1.re) rho.1.im) (orders j)
          (13*orders j/32) (lengthFactor (3/2-rho.1.re) (orders j))-
        correlationCredit (ordinaryArray (3/2-rho.1.re) rho.1.im) (orders j)
          (13*orders j/32) (lengthFactor (3/2-rho.1.re) (orders j))
            ≤ 399/5000+err j) : False := by
  let u := 3/2-rho.1.re
  let payment := fun N => adjacentSourcePrice rho N+
    ZetaRieszPairWholeCompletion.wholeCompletionBudget N+
      ZetaRieszPairJointQuadratic.squareBudget u N
  have hu : 0 ≤ u := by dsimp [u]; linarith only [NontrivialZetaZero.re_lt_one rho]
  have hp : Tendsto payment atTop (𝓝 0) := by
    simpa only [payment,add_zero] using
      ((adjacentSourcePrice_tendsto rho).add
        ZetaRieszPairWholeCompletion.wholeCompletionBudget_tendsto).add
          (ZetaRieszPairJointQuadratic.squareBudget_tendsto hu hU)
  apply ZetaRieszPairFloorAllMultiplicity.false_of_prefix_cofinal_bound rho hrho hexposed hU
    orders horders (fun j => err j+payment (orders j))
    (by simpa only [add_zero,Function.comp_def] using he.add (hp.comp horders))
  have hN := horders.eventually (eventually_ge_atTop (65536 : ℕ))
  apply (hf.and_eventually hN).mono
  intro j hj
  have hb := exposed_prefix_signed_upper rho hrho hexposed hU hj.2
  dsimp only [payment,u,adjacentSourcePrice]
  linarith only [hb,hj.1]

end RiemannGaussian.ZetaRieszCoupledArithmeticBound
