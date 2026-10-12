/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorBinaryDensityAudit
import RiemannGaussian.ArithmeticOperatorGammaConeStability

/-!
# Exact finite Gamma calibration does not remove a coherent unit-prime tail

Restore every tower of every deleted ordinary prime up to a chosen head B.
The resulting unit-prime system agrees with actual Mangoldt on the whole
integer prefix and with every corresponding actual Gamma observation.
Nevertheless its complete campaign factorial moments still tend to -2.

The quantifiers are essential: for EVERY finite B there is a control.
No single control is asserted to match all prefixes simultaneously. This
is NOT actual Mangoldt, an RH estimate, or a meromorphic continuation of
the selected Euler product beyond Re(s)>1.
-/

namespace RiemannGaussian.ArithmeticOperatorFiniteGammaControl
noncomputable section
open Complex Filter Topology
open scoped BigOperators Classical
open ArithmeticOperatorBinaryPrimeControl ArithmeticOperatorPrimeTowerControl
open ArithmeticOperatorFactorialUniqueness

/-- Restore a complete prime tower, not merely its labels below B. -/
def base (B : ℕ) (u y : ℝ) (p : ℕ) : ℝ :=
  if p≤B then 1 else retainedBase u y p

/-- The repaired coefficient at every ordinary integer label. -/
def control (B : ℕ) (u y : ℝ) (n : ℕ) : ℝ := towerCoefficient (base B u y) n

theorem base_binary (B : ℕ) (u y : ℝ) (p : ℕ) :
    base B u y p=0 ∨ base B u y p=1 := by
  unfold base
  split_ifs
  · exact Or.inr rfl
  · rcases removedBase_binary u y p with hh | hh <;>
      norm_num [retainedBase,hh]

theorem base_bounds (B : ℕ) (u y : ℝ) (p : ℕ) :
    0≤base B u y p ∧ base B u y p≤1 := by
  rcases base_binary B u y p with hh | hh <;> norm_num [hh]

theorem control_bounds (B : ℕ) (u y : ℝ) (n : ℕ) :
    0≤control B u y n ∧ control B u y n≤ArithmeticFunction.vonMangoldt n :=
  towerCoefficient_bounds _ (base_bounds B u y) n

/-- Repair only adds genuine prime powers; it never deletes extra mass. -/
theorem old_control_le (B : ℕ) (u y : ℝ) (n : ℕ) :
    ArithmeticOperatorBinaryDensityAudit.control u y n≤control B u y n := by
  unfold ArithmeticOperatorBinaryDensityAudit.control control towerCoefficient base
  apply mul_le_mul_of_nonneg_right _ ArithmeticFunction.vonMangoldt_nonneg
  split_ifs
  · exact (binaryBase_bounds u y n.minFac).2.2
  · exact le_rfl

/-- Exact equality at EVERY physical label in the calibrated prefix. -/
theorem control_eq_mangoldt_of_le (B : ℕ) (u y : ℝ) {n : ℕ} (hn : n≤B) :
    control B u y n=ArithmeticFunction.vonMangoldt n := by
  by_cases hn0 : n=0
  · simp [hn0,control,towerCoefficient]
  · have hp : n.minFac≤B := (Nat.minFac_le (Nat.pos_of_ne_zero hn0)).trans hn
    simp [control,towerCoefficient,base,hp]

/-- Every power of a repaired base is actual, even far above the head. -/
theorem control_prime_power (B : ℕ) (u y : ℝ) {p k : ℕ}
    (hp : p.Prime) (hpB : p≤B) (hk : 0<k) :
    control B u y (p^k)=ArithmeticFunction.vonMangoldt (p^k) := by
  rw [control,towerCoefficient_pow _ hp hk]
  simp [base,hpB,ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
    ArithmeticFunction.vonMangoldt_apply_prime hp]

/-- All literal quotient endpoints and all prime powers are matched. -/
theorem factorialPrefix_eq_of_le (B : ℕ) (u y : ℝ) {N : ℕ} (hN : N≤B) :
    factorialPrefix (fun n => (control B u y n : ℂ)) N=
      (Real.log (N.factorial : ℝ) : ℂ) := by
  rw [←factorialPrefix_mangoldt N]
  unfold factorialPrefix
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only
  rw [control_eq_mangoldt_of_le B u y ((Finset.mem_Icc.mp hn).2.trans hN)]

/-- A finite (even nonlinear) observation sees EXACTLY the same prefix. -/
theorem finite_observation_eq {α : Type*} (B : ℕ) (u y : ℝ)
    (F : (Fin (B+1) → ℝ) → α) :
    F (fun n => control B u y n)=F (fun n => ArithmeticFunction.vonMangoldt n) := by
  congr 1
  funext n
  exact control_eq_mangoldt_of_le B u y (by omega)

private theorem ordinary_summable (b : ℕ → ℝ)
    (hb : ∀ p, 0≤b p ∧ b p≤1) (y : ℝ) (k : ℕ) :
    Summable (fun n : ℕ => if n.Prime then
      (towerCoefficient b n : ℂ)*zetaPrimeLogKernel k (3/2+I*y) n else 0) := by
  apply (summable_zetaOrdinaryPrimeLogMoment k (by norm_num :
    1<(3/2+I*(y : ℂ)).re)).norm.of_norm_bounded
  intro n
  by_cases hn : n.Prime
  · simp only [hn,ite_true,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg (towerCoefficient_bounds b hb n).1,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_mul_of_nonneg_right (towerCoefficient_bounds b hb n).2 (norm_nonneg _)
  · simp [hn]

/-- The ordinary correction is just a finite actual-prime head, with
the full complex phase and factorial order unchanged. -/
theorem ordinary_correction_eq (B : ℕ) (u y : ℝ) (k : ℕ) :
    ordinaryMoment (base B u y) u y k-ordinaryMoment (retainedBase u y) u y k=
    ∑ p ∈ (Finset.range (B+1)).filter Nat.Prime,
      ((removedBase u y p*ArithmeticFunction.vonMangoldt p : ℝ) : ℂ)*
        ((u : ℂ)^(k+1)*zetaPrimeLogKernel k (3/2+I*y) p) := by
  unfold ordinaryMoment
  rw [←mul_sub,←(ordinary_summable _ (base_bounds B u y) y k).tsum_sub
    (ordinary_summable _ (fun p => (binaryBase_bounds u y p).2) y k)]
  rw [tsum_eq_sum (s := (Finset.range (B+1)).filter Nat.Prime) (by
    intro p hp
    by_cases hprime : p.Prime
    · have htail : ¬p≤B := by
        intro hh
        exact hp (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hprime⟩)
      simp [hprime,towerCoefficient,base,htail]
    · simp [hprime])]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpB,hprime⟩ := Finset.mem_filter.mp hp
  have hple : p≤B := by have := Finset.mem_range.mp hpB; omega
  simp only [hprime,ite_true,towerCoefficient,hprime.minFac_eq,base,ite_eq_left hple,
    one_mul,retainedBase,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one]
  ring

private theorem normalizedKernel_tendsto (u : ℝ) (s : ℂ) (p : ℕ)
    (hu : 0≤u) (hU : u<1) :
    Tendsto (fun k : ℕ => (u : ℂ)^(k+1)*zetaPrimeLogKernel k s p) atTop (𝓝 0) := by
  apply squeeze_zero_norm (a := fun k => u*zetaPrimeExpWeight (s.re-1) p*u^k) _
    (by simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hu hU).const_mul
      (u*zetaPrimeExpWeight (s.re-1) p)))
  intro k
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu]
  have hk := norm_zetaPrimeLogKernel_le k s p (by norm_num : (0 : ℝ)<1)
  simpa only [inv_one,one_pow,one_mul,pow_succ,mul_assoc,mul_comm,mul_left_comm] using
    mul_le_mul_of_nonneg_left hk (pow_nonneg hu (k+1))

/-- Finite calibration is source-small; no physical completion is used. -/
theorem tendsto_ordinary_correction (B : ℕ) {u : ℝ} (hu : 0≤u) (hU : u<1) (y : ℝ) :
    Tendsto (fun k => ordinaryMoment (base B u y) u y k-
      ordinaryMoment (retainedBase u y) u y k) atTop (𝓝 0) := by
  have ht := tendsto_finsetSum ((Finset.range (B+1)).filter Nat.Prime)
    (fun p _ => (normalizedKernel_tendsto
      u (3/2+I*y) p hu hU).const_mul
        ((removedBase u y p*ArithmeticFunction.vonMangoldt p : ℝ) : ℂ))
  simp only [mul_zero,Finset.sum_const_zero] at ht
  exact ht.congr (fun k => (ordinary_correction_eq B u y k).symm)

/-- No finite repair restores all primes: the deleted coherent tail is
infinite. The proof uses its checked +2 source, not PNT or a zero premise. -/
theorem exists_deleted_prime_gt (B : ℕ) {u : ℝ} (hu : 1/2<u) (hU : u<1)
    {y : ℝ} (hy : y≠0) :
    ∃ p : ℕ, p.Prime ∧ B<p ∧ removedBase u y p=1 := by
  by_contra hh
  push Not at hh
  have hp0 (p : ℕ) (hp : p.Prime) (hpB : B<p) : removedBase u y p=0 :=
    (removedBase_binary u y p).resolve_right (hh p hp hpB)
  have he (k : ℕ) : ordinaryMoment (removedBase u y) u y k=
      ordinaryMoment (base B u y) u y k-ordinaryMoment (retainedBase u y) u y k := by
    rw [ordinary_correction_eq]
    unfold ordinaryMoment
    rw [tsum_eq_sum (s := (Finset.range (B+1)).filter Nat.Prime) (by
      intro p hp
      by_cases hprime : p.Prime
      · have htail : B<p := by
          by_contra hb
          exact hp (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hprime⟩)
        simp [hprime,towerCoefficient,hp0 p hprime htail]
      · simp [hprime])]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hprime := (Finset.mem_filter.mp hp).2
    simp only [hprime,ite_true,towerCoefficient,hprime.minFac_eq,Complex.ofReal_mul]
    ring
  have ht := (tendsto_ordinary_correction B (u := u) (by linarith) hU y).congr
    (fun k => (he k).symm)
  have hbad := tendsto_nhds_unique ht (removedMoment_tendsto u y hu hU hy)
  norm_num at hbad

/-- EVERY chosen finite prime/Gamma head can coexist with the same -2
ordinary source. No hypothetical zeta zero is assumed. -/
theorem ordinary_source (B : ℕ) :
    Tendsto (ordinaryMoment (base B (10001/20000) 54) (10001/20000) 54)
      atTop (𝓝 (-2)) := by
  have ht := ArithmeticOperatorBinaryPrimeControl.retainedMoment_target_tendsto.add
    (tendsto_ordinary_correction B (u := 10001/20000) (by norm_num) (by norm_num) 54)
  simp only [add_zero] at ht
  apply ht.congr
  intro k
  ring

/-- Every proper prime power remains in the full source. The proper-power
error is paid by the existing independent fixed-center theorem. -/
theorem full_source (B : ℕ) :
    Tendsto (fullMoment (base B (10001/20000) 54) (10001/20000) 54)
      atTop (𝓝 (-2)) := by
  have ht := (ordinary_source B).add (tendsto_full_sub_ordinary _
    (base_bounds B (10001/20000) 54) (u := 10001/20000) (by norm_num) (by norm_num) 54)
  simp only [add_zero] at ht
  apply ht.congr
  intro k
  ring

/-- The repaired control retains the actual PNT normalization at ALL
integer cutoffs, independently of its coherent factorial source. -/
theorem tendsto_prefix_density (B : ℕ) {u : ℝ} (hu : 1/2<u) (y : ℝ) :
    Tendsto (fun X : ℕ => (∑ n ∈ Finset.range (X+1),control B u y n)/(X : ℝ))
      atTop (𝓝 1) := by
  have hactual := chebyshevPsi_div_tendsto_one.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (ArithmeticOperatorBinaryDensityAudit.tendsto_control_prefix_density hu y)
    hactual
  · intro X
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg X)
    exact Finset.sum_le_sum (fun n _ => old_control_le B u y n)
  · intro X
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg X)
    have hpsi : Chebyshev.psi X=∑ n ∈ Finset.range (X+1),
        ArithmeticFunction.vonMangoldt n := by
      rw [Chebyshev.psi_eq_sum_Icc]
      simp only [Nat.floor_natCast,←Nat.range_succ_eq_Icc_zero]
    rw [hpsi]
    exact Finset.sum_le_sum (fun n _ => (control_bounds B u y n).2)

/-- Positive ordinary integers generated by the repaired unit-prime set. -/
def kept (B : ℕ) (u y : ℝ) (n : ℕ) : Prop :=
  n≠0 ∧ ∀ p : ℕ, p.Prime → p∣n → base B u y p=1

theorem kept_mul_iff (B : ℕ) (u y : ℝ) (m n : ℕ) :
    kept B u y (m*n) ↔ kept B u y m ∧ kept B u y n := by
  constructor
  · intro hh
    exact ⟨⟨left_ne_zero_of_mul hh.1,fun p hp hpm =>
      hh.2 p hp (dvd_mul_of_dvd_left hpm n)⟩,
      ⟨right_ne_zero_of_mul hh.1,fun p hp hpn =>
      hh.2 p hp (dvd_mul_of_dvd_right hpn m)⟩⟩
  · rintro ⟨hm,hn⟩
    refine ⟨mul_ne_zero hm.1 hn.1,?_⟩
    intro p hp hpn
    rcases hp.dvd_mul.mp hpn with hh | hh
    · exact hm.2 p hp hh
    · exact hn.2 p hp hh

theorem kept_one (B : ℕ) (u y : ℝ) : kept B u y 1 := by
  refine ⟨by norm_num,?_⟩
  intro p hp hh
  exact False.elim (hp.not_dvd_one hh)

theorem kept_prime (B : ℕ) (u y : ℝ) {p : ℕ} (hp : p.Prime) :
    kept B u y p ↔ base B u y p=1 := by
  constructor
  · exact fun hh => hh.2 p hp dvd_rfl
  · intro hh
    refine ⟨hp.ne_zero,?_⟩
    intro q hq hqp
    rcases (Nat.dvd_prime hp).mp hqp with hq1 | hqp'
    · exact False.elim (hq.ne_one hq1)
    · simpa only [hqp'] using hh

/-- Genuine completely multiplicative integer-monoid indicator. -/
def indicatorHom (B : ℕ) (u y : ℝ) : ℕ →*₀ ℂ where
  toFun n := if kept B u y n then 1 else 0
  map_zero' := by simp [kept]
  map_one' := by simp [kept_one]
  map_mul' m n := by
    simp only [kept_mul_iff]
    by_cases hm : kept B u y m <;> by_cases hn : kept B u y n <;> simp [hm,hn]

theorem indicator_prime (B : ℕ) (u y : ℝ) {p : ℕ} (hp : p.Prime) :
    indicatorHom B u y p=(base B u y p : ℂ) := by
  change (if kept B u y p then (1 : ℂ) else 0)=_
  rw [kept_prime B u y hp]
  rcases base_binary B u y p with hh | hh <;> norm_num [hh]

/-- Actual Dirichlet summand of the repaired multiplicative monoid. -/
def summandHom (B : ℕ) (u y : ℝ) {s : ℂ} (hs : s≠0) : ℕ →*₀ ℂ :=
  { toFun := fun n => indicatorHom B u y n*riemannZetaSummandHom hs n
    map_zero' := by simp
    map_one' := by simp
    map_mul' := fun m n => by simp only [map_mul]; ring }

/-- Finite repair preserves the UNIT Euler factors of ordinary primes;
this asserts convergence only in the actual Euler half-plane. -/
theorem hasProd_selected_primes (B : ℕ) (u y : ℝ) {s : ℂ} (hs : 1<s.re) :
    HasProd (fun p : Nat.Primes =>
      (1-(base B u y p : ℂ)*(p : ℂ)^(-s))⁻¹)
      (∑' n, summandHom B u y (ne_zero_of_one_lt_re hs) n) := by
  have hn : Summable (fun n => ‖summandHom B u y (ne_zero_of_one_lt_re hs) n‖) := by
    apply (summable_riemannZetaSummand hs).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro n
    change ‖(if kept B u y n then (1 : ℂ) else 0)*riemannZetaSummandHom _ n‖≤_
    split_ifs <;> simp
  have hh := EulerProduct.eulerProduct_completely_multiplicative_hasProd hn
  convert hh using 1
  funext p
  change (1-(base B u y p : ℂ)*(p : ℂ)^(-s))⁻¹=
    (1-indicatorHom B u y p*riemannZetaSummandHom _ p)⁻¹
  rw [indicator_prime B u y p.prop]
  rfl

/-- Every proper power has the same unit Euler weight as its prime base. -/
theorem coefficient_eq_indicator_mangoldt (B : ℕ) (u y : ℝ) (n : ℕ) :
    (control B u y n : ℂ)=indicatorHom B u y n*(ArithmeticFunction.vonMangoldt n : ℂ) := by
  by_cases hn : IsPrimePow n
  · obtain ⟨p,k,hp,hk,hn'⟩ := (isPrimePow_nat_iff n).mp hn
    rw [←hn',control,towerCoefficient_pow _ hp hk,map_pow,indicator_prime B u y hp,
      ArithmeticFunction.vonMangoldt_apply_pow hk.ne',ArithmeticFunction.vonMangoldt_apply_prime hp,
      Complex.ofReal_mul]
    rcases base_binary B u y p with hh | hh <;> simp [hh,hk.ne']
  · simp [control,towerCoefficient_not_primePow _ hn,
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]

end
end RiemannGaussian.ArithmeticOperatorFiniteGammaControl
