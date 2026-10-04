/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSelbergSourceAudit

/-!
# Pay the whole ordinary-prime / von Mangoldt quadratic difference

The existing four-term signed quadratic is Lipschitz in the l1 distance
of its normalized logged arrays, with an explicit inverse-order factor.
Actual proper-prime-power moments have a uniform summable geometric
majorant. Thus their FULL insertion cost is paid, including every low
logged order, under the already-proved exposed-source array bound.

The main full-von-Mangoldt quadratic stays signed and unpaid. This is not
an independent 399/5000 bound, nor a new carrier or a zero exclusion.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszPairPrimePowerPayment
open ZetaRieszSelbergSourceAudit ZetaRieszPairPrefixConvolution
open ZetaRieszPrimeCountFrequency ZetaRieszSignedSelbergPayment

private theorem product_difference {a b c d : ℂ} {C : ℝ}
    (hb : ‖b‖≤C) (hc : ‖c‖≤C) :
    ‖a*b-c*d‖≤C*(‖a-c‖+‖b-d‖) := by
  have he : a*b-c*d=(a-c)*b+c*(b-d) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul]
  have h1 := mul_le_mul_of_nonneg_left hb (norm_nonneg (a-c))
  have h2 := mul_le_mul_of_nonneg_right hc (norm_nonneg (b-d))
  nlinarith only [h1,h2]

private theorem marginal_sums (e : ℕ → ℝ) (he : ∀ j,0≤e j)
    (N t : ℕ) (ht : t≤N+1) (S : Finset ℕ) (hS : ∀ k∈S,0<k ∧ k≤t) :
    (∑ k∈S,e (k-1))≤∑ j∈Finset.range (N+2),e j ∧
    (∑ k∈S,e (t-k))≤∑ j∈Finset.range (N+2),e j := by
  have hl : S.image (fun k => k-1)⊆Finset.range (N+2) := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
    have := hS k hk
    exact Finset.mem_range.mpr (by omega)
  have hr : S.image (fun k => t-k)⊆Finset.range (N+2) := by
    intro j hj
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (by omega)
  have hil : Set.InjOn (fun k : ℕ => k-1) S := by
    intro a ha b hb h
    have := hS a ha
    have := hS b hb
    dsimp only at h
    omega
  have hir : Set.InjOn (fun k : ℕ => t-k) S := by
    intro a ha b hb h
    have := hS a ha
    have := hS b hb
    dsimp only at h
    omega
  constructor
  · rw [←Finset.sum_image hil]
    exact Finset.sum_le_sum_of_subset_of_nonneg hl (fun j _ _ => he j)
  · rw [←Finset.sum_image hir]
    exact Finset.sum_le_sum_of_subset_of_nonneg hr (fun j _ _ => he j)

private theorem harmonic_difference (a b : ℕ → ℂ) {C : ℝ} (hC : 0≤C)
    (ha : ∀ k,‖a k‖≤C) (hb : ∀ k,‖b k‖≤C)
    {N : ℕ} (hN : 0<N) (t : ℕ) (ht : t≤N+1) (S : Finset ℕ)
    (hS : ∀ k∈S,0<k ∧ k≤t ∧ N≤4*(t+1-k)) :
    ‖(∑ k∈S,a (k-1)*a (t-k)/((t+1-k : ℕ) : ℂ))-
      ∑ k∈S,b (k-1)*b (t-k)/((t+1-k : ℕ) : ℂ)‖≤
      (8*C/(N : ℝ))*∑ j∈Finset.range (N+2),‖a j-b j‖ := by
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  have hp k (hk : k∈S) :
      ‖(a (k-1)*a (t-k)-b (k-1)*b (t-k))/((t+1-k : ℕ) : ℂ)‖≤
        (4*C/(N : ℝ))*(‖a (k-1)-b (k-1)‖+‖a (t-k)-b (t-k)‖) := by
    have hs := hS k hk
    have hden : (0 : ℝ)<((t+1-k : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0<t+1-k)
    have hcomp : (N : ℝ)≤4*((t+1-k : ℕ) : ℝ) := by exact_mod_cast hs.2.2
    have hi : (1 : ℝ)/((t+1-k : ℕ) : ℝ)≤4/(N : ℝ) :=
      (div_le_div_iff₀ hden hNr).mpr (by linarith only [hcomp])
    rw [norm_div,Complex.norm_natCast,div_eq_mul_inv]
    exact (mul_le_mul (product_difference (ha (t-k)) (hb (k-1)))
      (by simpa only [one_div] using hi) (by positivity) (by positivity)).trans_eq (by ring)
  have hm := marginal_sums (fun j => ‖a j-b j‖) (fun j => norm_nonneg _) N t ht S
    (fun k hk => ⟨(hS k hk).1,(hS k hk).2.1⟩)
  rw [←Finset.sum_sub_distrib]
  simp only [←sub_div]
  calc
    _ ≤ ∑ k∈S,(4*C/(N : ℝ))*(‖a (k-1)-b (k-1)‖+‖a (t-k)-b (t-k)‖) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hp)
    _ = (4*C/(N : ℝ))*((∑ k∈S,‖a (k-1)-b (k-1)‖)+∑ k∈S,‖a (t-k)-b (t-k)‖) := by
      rw [←Finset.mul_sum,Finset.sum_add_distrib]
    _ ≤ _ := (mul_le_mul_of_nonneg_left (add_le_add hm.1 hm.2)
      (by positivity : 0≤4*C/(N : ℝ))).trans_eq (by ring)

private theorem trace_difference (a b : ℕ → ℂ) {C : ℝ} (hC : 0≤C)
    (ha : ∀ k,‖a k‖≤C) (hb : ∀ k,‖b k‖≤C) {N : ℕ} (hN : 0<N) :
    ‖(∑ k∈Finset.range N,a k*a (N-1-k))/(N : ℂ)-
      (∑ k∈Finset.range N,b k*b (N-1-k))/(N : ℂ)‖≤
      (2*C/(N : ℝ))*∑ k∈Finset.range (N+2),‖a k-b k‖ := by
  have hP k : ‖a k*a (N-1-k)-b k*b (N-1-k)‖≤
      C*(‖a k-b k‖+‖a (N-1-k)-b (N-1-k)‖) :=
    product_difference (ha (N-1-k)) (hb k)
  have hr : (∑ k∈Finset.range N,‖a (N-1-k)-b (N-1-k)‖)=
      ∑ k∈Finset.range N,‖a k-b k‖ := by
    simpa only using Finset.sum_range_reflect (fun k => ‖a k-b k‖) N
  have he : (∑ k∈Finset.range N,‖a k-b k‖)≤
      ∑ k∈Finset.range (N+2),‖a k-b k‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun k _ _ => norm_nonneg _)
  rw [←sub_div,←Finset.sum_sub_distrib,norm_div,Complex.norm_natCast]
  calc
    _ ≤ (∑ k∈Finset.range N,C*(‖a k-b k‖+‖a (N-1-k)-b (N-1-k)‖))/(N : ℝ) :=
      div_le_div_of_nonneg_right ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => hP k)))
        (Nat.cast_nonneg _)
    _ = (2*C/(N : ℝ))*∑ k∈Finset.range N,‖a k-b k‖ := by
      rw [←Finset.mul_sum,Finset.sum_add_distrib,hr]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)

private theorem length_factor_le {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N) :
    ‖((N+1 : ℕ) : ℂ)/((u : ℂ)*SquarefreeVaughanLogSource.length u N)‖≤3/2 := by
  have hu0 : 0<u := by linarith only [hu]
  have hL := SquarefreeVaughanLogSource.length_pos u N
  have hlo := ZetaRieszPostHingeEnergy.length_ge_rational hN hu0 hU
  have hprod := mul_nonneg (show 0≤u-1/2 by linarith only [hu]) hL.le
  have hNr : (65536 : ℝ)≤N := by exact_mod_cast hN
  rw [norm_div,norm_mul,Complex.norm_natCast,Complex.norm_real,
    Real.norm_of_nonneg hu0.le,Complex.norm_real,Real.norm_of_nonneg hL.le]
  apply (div_le_iff₀ (mul_pos hu0 hL)).mpr
  push_cast
  nlinarith only [hlo,hprod,hNr]

/-- An explicit whole-quadratic perturbation inequality. All signed slots
remain joined; only their actual array difference is estimated. -/
theorem norm_harmonicEvaluation_sub_le (a b : ℕ → ℂ) {C u : ℝ} (hC : 0≤C)
    (ha : ∀ k,‖a k‖≤C) (hb : ∀ k,‖b k‖≤C) (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N) :
    ‖harmonicEvaluation a u N-harmonicEvaluation b u N‖≤
      (22*C/(N : ℝ))*∑ k∈Finset.range (N+2),‖a k-b k‖ := by
  have hN0 : 0<N := by omega
  let E : ℝ := ∑ k∈Finset.range (N+2),‖a k-b k‖
  have hE : 0≤E := Finset.sum_nonneg (fun k _ => norm_nonneg _)
  have ht := trace_difference a b hC ha hb hN0
  have hc := harmonic_difference a b hC ha hb hN0 N (by omega)
    (centralOrders (N+1) (13*N/32)) (by
      intro k hk
      simp only [centralOrders,Finset.mem_filter,Finset.mem_range] at hk
      omega)
  have hp := harmonic_difference a b hC ha hb hN0 (N+1) (by omega)
    (Finset.Icc 1 (N+1-13*N/32)) (by
      intro k hk
      rw [Finset.mem_Icc] at hk
      omega)
  let F : ℂ := ((N+1 : ℕ) : ℂ)/((u : ℂ)*SquarefreeVaughanLogSource.length u N)
  let T (v : ℕ → ℂ) : ℂ := (∑ k∈Finset.range N,v k*v (N-1-k))/(N : ℂ)
  let B (v : ℕ → ℂ) : ℂ := ∑ k∈centralOrders (N+1) (13*N/32),
    v (k-1)*v (N-k)/((N+1-k : ℕ) : ℂ)
  let P (v : ℕ → ℂ) : ℂ := ∑ k∈Finset.Icc 1 (N+1-13*N/32),
    v (k-1)*v (N+1-k)/((N+2-k : ℕ) : ℂ)
  have he : harmonicEvaluation a u N-harmonicEvaluation b u N=
      (T a-T b)+(B a-B b)-F*(P a-P b) := by
    unfold harmonicEvaluation
    dsimp only [T,B,P,F]
    ring
  rw [he]
  apply (norm_sub_le _ _).trans
  have hf : ‖F*(P a-P b)‖≤(3/2 : ℝ)*((8*C/(N : ℝ))*E) := by
    rw [norm_mul]
    exact mul_le_mul (length_factor_le hu hU hN) hp (norm_nonneg _) (by norm_num)
  exact (add_le_add ((norm_add_le _ _).trans (add_le_add ht hc)) hf).trans_eq (by dsimp only [E]; ring)

/-- The existing normalized ordinary-prime logged moments, with all orders
including zero retained. -/
def ordinaryArray (u y : ℝ) (k : ℕ) : ℂ :=
  (u : ℂ)^(k+1)*zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)

/-- The corresponding full von Mangoldt moments. -/
def mangoldtArray (u y : ℝ) (k : ℕ) : ℂ :=
  (u : ℂ)^(k+1)*zetaPrimeLogMoment k (3/2+Complex.I*y)

/-- A fixed, finite arithmetic mass for ALL proper-power logged orders.
Its defining Dirichlet series converges at 3/4>1/2. -/
def powerMass : ℝ := ZetaRieszWideOwnerAudit.radiusCeiling*
  zetaProperPrimePowerExpMass (3/4)/(1-10001/15000)

theorem powerMass_nonneg : 0≤powerMass := by
  unfold powerMass ZetaRieszWideOwnerAudit.radiusCeiling
  exact div_nonneg (mul_nonneg (by norm_num)
    (zetaProperPrimePowerExpMass_nonneg _)) (by norm_num)

/-- The exact difference uses ordinary proper prime powers, not an
abstract array perturbation or a completed masked cofactor. -/
theorem mangoldtArray_sub_ordinaryArray (u y : ℝ) (k : ℕ) :
    mangoldtArray u y k-ordinaryArray u y k=
      (u : ℂ)^(k+1)*zetaProperPrimePowerMoment k (3/2+Complex.I*y) := by
  unfold mangoldtArray ordinaryArray
  rw [zetaPrimeLogMoment_eq_prime_add_proper k (by norm_num)]
  ring

/-- A uniform summable geometric majorant includes logged orders zero
and one. No exposed-zero hypothesis is used for this arithmetic error. -/
theorem norm_array_difference_le {u : ℝ} (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) (k : ℕ) :
    ‖ordinaryArray u y k-mangoldtArray u y k‖≤
      (ZetaRieszWideOwnerAudit.radiusCeiling*zetaProperPrimePowerExpMass (3/4))*
        (10001/15000 : ℝ)^k := by
  have hM := zetaProperPrimePowerExpMass_nonneg (3/4)
  have hp := norm_zetaProperPrimePowerMoment_le k y
    (q := 3/4) (by norm_num) (by norm_num)
  have hr : 4*u/3≤(10001/15000 : ℝ) := by
    unfold ZetaRieszWideOwnerAudit.radiusCeiling at hU
    linarith only [hU]
  rw [norm_sub_rev,mangoldtArray_sub_ordinaryArray,norm_mul,norm_pow,
    Complex.norm_real,Real.norm_of_nonneg hu]
  calc
    _ ≤ u^(k+1)*((4/3 : ℝ)^k*zetaProperPrimePowerExpMass (3/4)) :=
      mul_le_mul_of_nonneg_left (by norm_num at hp ⊢; exact hp) (pow_nonneg hu _)
    _ = (u*zetaProperPrimePowerExpMass (3/4))*(4*u/3)^k := by
      simp only [pow_succ,div_pow,mul_pow]
      ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right hU hM)
      (pow_le_pow_left₀ (by positivity) hr _) (by positivity)
        (mul_nonneg (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]) hM)

/-- The entire proper-prime-power array has one finite l1 price,
uniform in height, radius and the number of included factorial orders. -/
theorem sum_norm_array_difference_le {u : ℝ} (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) (M : ℕ) :
    (∑ k∈Finset.range M,‖ordinaryArray u y k-mangoldtArray u y k‖)≤powerMass := by
  have hs := summable_geometric_of_lt_one
    (by norm_num : (0 : ℝ)≤10001/15000) (by norm_num : (10001/15000 : ℝ)<1)
  have hf := hs.sum_le_tsum (Finset.range M) (fun k _ => by positivity)
  rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ)≤10001/15000)
    (by norm_num : (10001/15000 : ℝ)<1)] at hf
  calc
    _ ≤ ∑ k∈Finset.range M,
        (ZetaRieszWideOwnerAudit.radiusCeiling*zetaProperPrimePowerExpMass (3/4))*
          (10001/15000 : ℝ)^k :=
      Finset.sum_le_sum (fun k _ => norm_array_difference_le hu hU y k)
    _ = (ZetaRieszWideOwnerAudit.radiusCeiling*zetaProperPrimePowerExpMass (3/4))*
        ∑ k∈Finset.range M,(10001/15000 : ℝ)^k := by rw [Finset.mul_sum]
    _ ≤ powerMass := (mul_le_mul_of_nonneg_left hf (by
      unfold ZetaRieszWideOwnerAudit.radiusCeiling
      exact mul_nonneg (by norm_num) (zetaProperPrimePowerExpMass_nonneg _))).trans_eq
        (by simp only [powerMass,div_eq_mul_inv])

/-- A concrete GLOBAL payment for the proper-power correction to the
four joined signed slots. The whole main remains signed and unpaid.
The only conditional input is the two complete-array bounds. -/
theorem norm_ordinary_sub_mangoldt_quadratic_le {u C : ℝ} (hC : 0≤C)
    (hu : 1/2≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ)
    (ho : ∀ k,‖ordinaryArray u y k‖≤C)
    (hm : ∀ k,‖mangoldtArray u y k‖≤C) {N : ℕ} (hN : 65536≤N) :
    ‖harmonicEvaluation (ordinaryArray u y) u N-
      harmonicEvaluation (mangoldtArray u y) u N‖≤22*C*powerMass/(N : ℝ) :=
  (norm_harmonicEvaluation_sub_le _ _ hC ho hm hu hU hN).trans
    ((mul_le_mul_of_nonneg_left (sum_norm_array_difference_le
      (by linarith only [hu] : 0≤u) hU y (N+2)) (by positivity)).trans_eq (by ring))

/-- Two-sided control of the REAL difference. The remaining main is not
replaced by its norm or by separate positive allowances. -/
theorem abs_re_ordinary_sub_mangoldt_le {u C : ℝ} (hC : 0≤C)
    (hu : 1/2≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ)
    (ho : ∀ k,‖ordinaryArray u y k‖≤C)
    (hm : ∀ k,‖mangoldtArray u y k‖≤C) {N : ℕ} (hN : 65536≤N) :
    |(harmonicEvaluation (ordinaryArray u y) u N).re-
      (harmonicEvaluation (mangoldtArray u y) u N).re|≤22*C*powerMass/(N : ℝ) := by
  simpa only [Complex.sub_re] using
    (Complex.abs_re_le_norm _).trans
      (norm_ordinary_sub_mangoldt_quadratic_le hC hu hU y ho hm hN)

/-- At every exposed right-half zero, both complete-array bounds are
already proved. No simple-zero assumption or new bilinear estimate is
added. This pays the whole correction with one explicit 1/N rate. -/
theorem exists_exposed_quadratic_power_payment (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho→
      3/2-rho.1.re<‖(3/2:ℂ)+Complex.I*rho.1.im-tau.1‖)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∃ C : ℝ,1≤C ∧
      (∀ k,‖ordinaryArray (3/2-rho.1.re) rho.1.im k‖≤C) ∧
      (∀ k,‖mangoldtArray (3/2-rho.1.re) rho.1.im k‖≤C) ∧
      ∀ N : ℕ,65536≤N→
        ‖harmonicEvaluation (ordinaryArray (3/2-rho.1.re) rho.1.im) (3/2-rho.1.re) N-
          harmonicEvaluation (mangoldtArray (3/2-rho.1.re) rho.1.im) (3/2-rho.1.re) N‖≤
            22*C*powerMass/(N : ℝ) := by
  obtain ⟨A,hA,ha⟩ := ZetaExposedPrimeMoments.exists_normalized_ordinary_prime_moment_bound
    rho hrho hexposed
  obtain ⟨B,hB,hb⟩ := ZetaExposedPrimeMoments.exists_normalized_prime_moment_bound
    rho hrho hexposed
  have hu : 1/2≤3/2-rho.1.re := by linarith only [NontrivialZetaZero.re_lt_one rho]
  have ho : ∀ k,‖ordinaryArray (3/2-rho.1.re) rho.1.im k‖≤1+A+B := by
    intro k
    exact (ha k).trans (by linarith only [hB])
  have hm : ∀ k,‖mangoldtArray (3/2-rho.1.re) rho.1.im k‖≤1+A+B := by
    intro k
    exact (hb k).trans (by linarith only [hA])
  refine ⟨1+A+B,by linarith only [hA,hB],ho,hm,?_⟩
  intro N hN
  exact norm_ordinary_sub_mangoldt_quadratic_le (by linarith only [hA,hB]) hu hU
    rho.1.im ho hm hN

/-- The global proper-power correction tends to zero, retaining ALL
low logged orders and every analytic zero multiplicity. -/
theorem tendsto_exposed_quadratic_power_difference (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho→
      3/2-rho.1.re<‖(3/2:ℂ)+Complex.I*rho.1.im-tau.1‖)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N : ℕ =>
      harmonicEvaluation (ordinaryArray (3/2-rho.1.re) rho.1.im) (3/2-rho.1.re) N-
        harmonicEvaluation (mangoldtArray (3/2-rho.1.re) rho.1.im) (3/2-rho.1.re) N)
      atTop (𝓝 0) := by
  obtain ⟨C,_,_,_,hc⟩ := exists_exposed_quadratic_power_payment rho hrho hexposed hU
  have ht : Tendsto (fun N : ℕ => 22*C*powerMass/(N : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero,div_eq_mul_inv,one_div,one_mul] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (22*C*powerMass)
  exact squeeze_zero_norm' ((eventually_ge_atTop 65536).mono fun N hN => hc N hN) ht

private theorem polynomial_congr_pos (a b : ℕ → ℂ)
    (hab : ∀ k,0<k→a k=b k) (N : ℕ) (L : ℝ) :
    momentPolynomial a N L=momentPolynomial b N L := by
  have hc (M K : ℕ) : (∑ k∈centralOrders M K,a k*a (M-k))=
      ∑ k∈centralOrders M K,b k*b (M-k) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [centralOrders,Finset.mem_filter,Finset.mem_range] at hk
    rw [hab k (by omega),hab (M-k) (by omega)]
  have hp : (∑ k∈(Finset.range (13*N/32+1)).filter (fun k => 0<k),
      (k : ℂ)*a k*a (N+2-k))=
      ∑ k∈(Finset.range (13*N/32+1)).filter (fun k => 0<k),
        (k : ℂ)*b k*b (N+2-k) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_filter,Finset.mem_range] at hk
    rw [hab k (by omega),hab (N+2-k) (by omega)]
  have ht : (∑ k∈Finset.range N,
      ((k+1 : ℕ) : ℂ)*((N-k : ℕ) : ℂ)*a (k+1)*a (N-k))=
      ∑ k∈Finset.range N,
        ((k+1 : ℕ) : ℂ)*((N-k : ℕ) : ℂ)*b (k+1)*b (N-k) := by
    apply Finset.sum_congr rfl
    intro k hk
    have := Finset.mem_range.mp hk
    rw [hab (k+1) (by omega),hab (N-k) (by omega)]
  unfold momentPolynomial
  rw [hc,hc,hp,ht]

private theorem finite_model_pos (A : Finset ℕ) {u : ℝ} (hu : u≠0)
    (s : ℂ) {k : ℕ} (hk : 0<k) :
    modelMoment (fun j => (u : ℂ)^(j+1)*ZetaRieszHeadOrders.cofactorMoment A j s) u k=
      ZetaRieszPrimePairConvolution.finiteMoment A k s := by
  have huk : (u : ℂ)≠0 := by exact_mod_cast hu
  have hkc : (k : ℂ)≠0 := by exact_mod_cast hk.ne'
  unfold modelMoment
  dsimp only
  rw [ZetaRieszPrimePairConvolution.cofactorMoment_eq_succ,
    show k-1+1=k by omega]
  field_simp [huk,hkc]

/-- The paid evaluator is EXACTLY the existing finite factorial
quadratic, not a different completed or filtered carrier. -/
theorem normalized_finite_quadratic_eq_harmonic (A : Finset ℕ)
    {u : ℝ} (hu : u≠0) (y : ℝ) (N : ℕ) :
    (u : ℂ)^(N+1)*ZetaRieszPairJointQuadratic.factorialQuadratic A N
      (SquarefreeVaughanLogSource.length u N) (3/2+Complex.I*y)=
      harmonicEvaluation (fun k => (u : ℂ)^(k+1)*
        ZetaRieszHeadOrders.cofactorMoment A k (3/2+Complex.I*y)) u N := by
  rw [factorialQuadratic_eq_polynomial,←model_polynomial_eq_harmonic _ hu N]
  congr 1
  exact polynomial_congr_pos _ _ (fun k hk => (finite_model_pos A hu _ hk).symm) N _

private theorem harmonic_tendsto (a : ℕ → ℕ → ℂ) (b : ℕ → ℂ)
    (hab : ∀ k,Tendsto (fun P => a P k) atTop (𝓝 (b k))) (u : ℝ) (N : ℕ) :
    Tendsto (fun P => harmonicEvaluation (a P) u N) atTop (𝓝 (harmonicEvaluation b u N)) := by
  unfold harmonicEvaluation
  exact (((tendsto_finsetSum _ (fun k _ => (hab k).mul (hab (N-1-k)))).div_const _).add
    (tendsto_finsetSum _ (fun k _ => ((hab (k-1)).mul (hab (N-k))).div_const _))).sub
      ((tendsto_finsetSum _ (fun k _ => ((hab (k-1)).mul (hab (N+1-k))).div_const _)).const_mul _)

/-- Exhausting actual ordinary primes gives the existing complete
quadratic at each fixed N. Whole symmetric support completion, already
paid elsewhere, is the only support bridge used below. -/
theorem finite_quadratic_tendsto {u : ℝ} (hu : u≠0) (y : ℝ) (N : ℕ) :
    Tendsto (fun P : ℕ => (u : ℂ)^(N+1)*
      ZetaRieszPairJointQuadratic.factorialQuadratic (ZetaRieszSignedSelbergPayment.primePrefix P) N
        (SquarefreeVaughanLogSource.length u N) (3/2+Complex.I*y)) atTop
      (𝓝 (harmonicEvaluation (ordinaryArray u y) u N)) := by
  have ha k := (ZetaRieszSignedSelbergPayment.cofactorMoment_prefix_tendsto k
    (by norm_num : 1<(3/2+Complex.I*(y : ℂ)).re)).const_mul ((u : ℂ)^(k+1))
  exact (harmonic_tendsto _ (ordinaryArray u y) ha u N).congr
    (fun P => (normalized_finite_quadratic_eq_harmonic _ hu y N).symm)

/-- The literal prefix target differs from the FULL von Mangoldt
quadratic by three paid quantities: whole symmetric completion, its one
square diagonal, and the new 1/N proper-power cost. No main-term norm
or independent arithmetic floor is asserted. -/
theorem norm_prefix_sub_mangoldt_le {u C : ℝ} (hC : 0≤C)
    (hu : 1/2≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (ho : ∀ k,‖ordinaryArray u y k‖≤C)
    (hm : ∀ k,‖mangoldtArray u y k‖≤C) {N : ℕ} (hN : 65536≤N) :
    ‖ZetaRieszPairPrefixPayment.prefixPairDefect u y N-
      harmonicEvaluation (mangoldtArray u y) u N‖≤
        ZetaRieszPairWholeCompletion.wholeCompletionBudget N+
          ZetaRieszPairJointQuadratic.squareBudget u N+22*C*powerMass/(N : ℝ) := by
  have hu0 : u≠0 := by linarith only [hu]
  have ht := ((tendsto_const_nhds (x := ZetaRieszPairPrefixPayment.prefixPairDefect u y N)).sub
    (finite_quadratic_tendsto hu0 y N)).norm
  have hb : ‖ZetaRieszPairPrefixPayment.prefixPairDefect u y N-
      harmonicEvaluation (ordinaryArray u y) u N‖≤
      ZetaRieszPairWholeCompletion.wholeCompletionBudget N+
        ZetaRieszPairJointQuadratic.squareBudget u N :=
    le_of_tendsto ht
      (ZetaRieszPairJointQuadratic.eventually_norm_prefix_sub_quadratic_le hu hU hy hN)
  exact (norm_sub_le_norm_sub_add_norm_sub _ (harmonicEvaluation (ordinaryArray u y) u N) _).trans
    (add_le_add hb (norm_ordinary_sub_mangoldt_quadratic_le hC hu hU y ho hm hN))

private theorem payment_tendsto {u : ℝ} (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (C : ℝ) :
    Tendsto (fun N : ℕ => ZetaRieszPairWholeCompletion.wholeCompletionBudget N+
      ZetaRieszPairJointQuadratic.squareBudget u N+22*C*powerMass/(N : ℝ)) atTop (𝓝 0) := by
  have hp : Tendsto (fun N : ℕ => 22*C*powerMass/(N : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero,div_eq_mul_inv,one_div,one_mul] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (22*C*powerMass)
  simpa only [add_zero] using
    ((ZetaRieszPairWholeCompletion.wholeCompletionBudget_tendsto).add
      (ZetaRieszPairJointQuadratic.squareBudget_tendsto hu hU)).add hp

/-- The same LITERAL signed prefix is source-equivalent to the joined
von Mangoldt quadratic. This pays a difference, not the selected source;
no simplicity hypothesis and no new main-term bound enter. -/
theorem tendsto_prefix_sub_mangoldt (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho→
      3/2-rho.1.re<‖(3/2:ℂ)+Complex.I*rho.1.im-tau.1‖)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|rho.1.im|) :
    Tendsto (fun N : ℕ =>
      ZetaRieszPairPrefixPayment.prefixPairDefect (3/2-rho.1.re) rho.1.im N-
        harmonicEvaluation (mangoldtArray (3/2-rho.1.re) rho.1.im) (3/2-rho.1.re) N)
      atTop (𝓝 0) := by
  obtain ⟨C,hC,ho,hm,_⟩ := exists_exposed_quadratic_power_payment rho hrho hexposed hU
  have hu : 1/2≤3/2-rho.1.re := by linarith only [NontrivialZetaZero.re_lt_one rho]
  exact squeeze_zero_norm' ((eventually_ge_atTop 65536).mono fun N hN =>
    norm_prefix_sub_mangoldt_le (by linarith only [hC]) hu hU hy ho hm hN)
      (payment_tendsto (by linarith only [hu]) hU C)

/-- Spend the three correction costs ONCE in the original native floor
ledger. The only unpaid main is still the exact signed four-slot
quadratic. A 399/5000 upper bound for that main is NOT assumed or proved. -/
theorem exists_native_mangoldt_payment_simple (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho→
      3/2-rho.1.re<‖(3/2:ℂ)+Complex.I*rho.1.im-tau.1‖)
    (hsimple : analyticZetaZeroMultiplicity rho=1)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|rho.1.im|) :
    ∃ A C : ℝ,1≤A ∧ 1≤C ∧
      Tendsto (fun j => nativeSelbergBudget (3/2-rho.1.re) rho.1.im A j+
        ZetaRieszPairPrefixPayment.prefixBudget (dyadicMomentOrder j)+
        (ZetaRieszPairWholeCompletion.wholeCompletionBudget (dyadicMomentOrder j)+
          ZetaRieszPairJointQuadratic.squareBudget (3/2-rho.1.re) (dyadicMomentOrder j)+
            22*C*powerMass/(dyadicMomentOrder j : ℝ))) atTop (𝓝 0) ∧
      ∀ᶠ j in atTop,
        -(harmonicEvaluation (mangoldtArray (3/2-rho.1.re) rho.1.im)
          (3/2-rho.1.re) (dyadicMomentOrder j)).re-
          (nativeSelbergBudget (3/2-rho.1.re) rho.1.im A j+
            ZetaRieszPairPrefixPayment.prefixBudget (dyadicMomentOrder j)+
            (ZetaRieszPairWholeCompletion.wholeCompletionBudget (dyadicMomentOrder j)+
              ZetaRieszPairJointQuadratic.squareBudget (3/2-rho.1.re) (dyadicMomentOrder j)+
                22*C*powerMass/(dyadicMomentOrder j : ℝ)))≤
        ((((3/2-rho.1.re : ℝ) : ℂ)^(dyadicMomentOrder j+1))*
          ZetaRieszParityPacket.coreResponse (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j)
            (ZetaRieszNearCriticalCountPayment.countCeiling j)).re := by
  obtain ⟨A,hA,ha,hfloor⟩ := ZetaRieszPairPrefixPayment.exists_native_prefix_payment_simple
    rho hrho hexposed hsimple hU hy
  obtain ⟨C,hC,ho,hm,_⟩ := exists_exposed_quadratic_power_payment rho hrho hexposed hU
  have hu : 1/2≤3/2-rho.1.re := by linarith only [NontrivialZetaZero.re_lt_one rho]
  refine ⟨A,C,hA,hC,?_,?_⟩
  · simpa only [add_zero,Function.comp_def] using ha.add
      ((payment_tendsto (by linarith only [hu]) hU C).comp tendsto_dyadicMomentOrder)
  · filter_upwards [hfloor,tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop 65536)]
      with j hj hN
    have hp := norm_prefix_sub_mangoldt_le (by linarith only [hC]) hu hU hy ho hm hN
    have he := Complex.re_le_norm
      (ZetaRieszPairPrefixPayment.prefixPairDefect (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j)-
        harmonicEvaluation (mangoldtArray (3/2-rho.1.re) rho.1.im)
          (3/2-rho.1.re) (dyadicMomentOrder j))
    rw [Complex.sub_re] at he
    linarith only [hj,hp,he]

end RiemannGaussian.ZetaRieszPairPrimePowerPayment
