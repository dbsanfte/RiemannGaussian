/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSmallDescendants
import Mathlib.Algebra.BigOperators.Module
import Mathlib.NumberTheory.Chebyshev

/-!
# Bounding all in-core extensions of a balanced triple

The full radial core, not a polynomial prime cutoff, limits the additional
factor. Composite extensions cancel exactly. Chebyshev's elementary bound
controls every surviving prime extension, including exponentially large
primes. The original allocation, selections and phases are retained.
These are local signed comparisons with an unchanged complementary sum;
they do not supply the independent floor for the whole core.
-/

namespace RiemannGaussian.ZetaRieszCoreExtensions
noncomputable section
open scoped BigOperators Classical
open Filter Topology ZetaRieszJointAllocation ZetaRieszSmallDescendants

private theorem theta_prefix (k : ℕ) :
    (∑ i ∈ Finset.range k, if (i+1).Prime then Real.log (i+1 : ℕ) else 0) =
      Chebyshev.theta k := by
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast,
    ← Nat.range_succ_eq_Icc_zero, Finset.sum_filter, Finset.sum_range_succ']
  simp

/-- An explicit logarithmic prime budget from Chebyshev, with no prime
density approximation or unproved error term. -/
theorem prime_log_reciprocal_le (M : ℕ) :
    (∑ p ∈ Nat.primesLE M, Real.log p/(p : ℝ)) ≤
      Real.log 4*(1+Real.log M) := by
  let g : ℕ → ℝ := fun i => if (i+1).Prime then Real.log (i+1 : ℕ) else 0
  have heq : (∑ p ∈ Nat.primesLE M, Real.log p/(p : ℝ)) =
      ∑ i ∈ Finset.range M, ((i+1 : ℕ) : ℝ)⁻¹*g i := by
    rw [Nat.primesLE_eq_filter_Icc_zero, Finset.sum_filter,
      ← Nat.range_succ_eq_Icc_zero, Finset.sum_range_succ']
    simp only [Nat.not_prime_zero, if_false, add_zero]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [g]
    split_ifs <;> ring
  rw [heq]
  by_cases hM : M = 0
  · subst M
    simpa using Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
  have hMp : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hb := Finset.sum_range_by_parts
    (fun i : ℕ => ((i+1 : ℕ) : ℝ)⁻¹) g M
  simp only [smul_eq_mul] at hb
  have hpref (k : ℕ) : (∑ i ∈ Finset.range k, g i) = Chebyshev.theta k :=
    theta_prefix k
  simp_rw [hpref] at hb
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hM)] at hb
  have hend : (M : ℝ)⁻¹*Chebyshev.theta M ≤ Real.log 4 := by
    rw [mul_comm, ← div_eq_mul_inv]
    exact (div_le_iff₀ hMp).mpr (Chebyshev.theta_le_log4_mul_x hMp.le)
  have hsum : -(Real.log 4*(∑ i ∈ Finset.range (M-1), ((i+2 : ℕ) : ℝ)⁻¹)) ≤
      ∑ i ∈ Finset.range (M-1),
        (((i+1+1 : ℕ) : ℝ)⁻¹-((i+1 : ℕ) : ℝ)⁻¹)*Chebyshev.theta ((i+1 : ℕ) : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hi : (0 : ℝ) < (i+1 : ℕ) := by positivity
    have hi' : (0 : ℝ) < (i+2 : ℕ) := by positivity
    have hneg : ((i+1+1 : ℕ) : ℝ)⁻¹-((i+1 : ℕ) : ℝ)⁻¹ ≤ 0 := by
      apply sub_nonpos.mpr
      exact inv_anti₀ hi (by norm_num)
    have h := mul_le_mul_of_nonpos_left
      (Chebyshev.theta_le_log4_mul_x hi.le) hneg
    apply le_trans ?_ h
    apply le_of_eq
    push_cast
    field_simp
    ring
  have hh : 1+(∑ i ∈ Finset.range (M-1), ((i+2 : ℕ) : ℝ)⁻¹) = (harmonic M : ℝ) := by
    nth_rw 2 [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hM)]
    rw [harmonic, Finset.sum_range_succ']
    push_cast
    simp
    ring
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  calc
    _ ≤ Real.log 4*(harmonic M : ℝ) := by rw [hb, ← hh]; nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log M) hlog4

/-- Any selected prime set bounded in logarithmic size obeys the same
explicit budget. The set may retain all original physical masks. -/
theorem prime_log_mass_le (D : Finset ℕ) {x : ℝ} (hx : 0 ≤ x)
    (hD : ∀ p ∈ D, p.Prime ∧ Real.log p ≤ x) :
    (∑ p ∈ D, Real.log p*Real.exp (-Real.log p)) ≤ Real.log 4*(1+x) := by
  let M := ⌊Real.exp x⌋₊
  have hsub : D ⊆ Nat.primesLE M := by
    intro p hp
    obtain ⟨hpp, hpx⟩ := hD p hp
    apply Nat.mem_primesLE.mpr
    refine ⟨?_, hpp⟩
    apply Nat.le_floor
    simpa only [Real.exp_log (by exact_mod_cast hpp.pos : (0 : ℝ) < p)] using
      Real.exp_le_exp.mpr hpx
  have hM : (1 : ℕ) ≤ M := (Nat.one_le_floor_iff (Real.exp x)).mpr
    (Real.one_le_exp_iff.mpr hx)
  have hl : Real.log M ≤ x := by
    have h := Real.log_le_log (by exact_mod_cast hM : (0 : ℝ) < M)
      (Nat.floor_le (Real.exp_nonneg x))
    simpa only [Real.log_exp] using h
  calc
    _ = ∑ p ∈ D, Real.log p/(p : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Real.exp_neg, Real.exp_log (by exact_mod_cast (hD p hp).1.pos), div_eq_mul_inv]
    _ ≤ ∑ p ∈ Nat.primesLE M, Real.log p/(p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    _ ≤ Real.log 4*(1+Real.log M) := prime_log_reciprocal_le M
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (Real.log_nonneg (by norm_num))

private theorem log_one_add_quadratic {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.log (1+x) ≤ x-x^2/6 := by
  have hd : 0 < 1+x/2 := by linarith
  have hx0 : 0 < 1+x := by linarith
  have h1 := Real.log_le_sub_one_of_pos hd
  have h2 := Real.log_le_sub_one_of_pos (div_pos hx0 hd)
  rw [Real.log_div hx0.ne' hd.ne'] at h2
  have hh : Real.log (1+x) ≤ x/2+(1+x)/(1+x/2)-1 := by linarith
  have h := mul_le_mul_of_nonneg_right hh hd.le
  have he : (x/2+(1+x)/(1+x/2)-1)*(1+x/2) = x+x^2/4 := by
    field_simp
    ring
  rw [he] at h
  apply (mul_le_mul_iff_right₀ hd).mp
  nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 1-x by linarith)]

/-- The original factorial kernel has an extra geometric saving for
extensions whose logarithm is a fixed positive fraction of the order.
No prime-density approximation or phase replacement is used. -/
theorem norm_kernel_extension_geometric {N : ℕ} (hN : 0 < N) (y : ℝ)
    {m a : ℕ} (hm : 1 < m) (ha : 0 < a)
    (hT : 2*(N : ℝ) ≤ Real.log m) {δ : ℝ} (hδ : 0 ≤ δ)
    (hlo : δ*N ≤ Real.log a) (hhi : Real.log a ≤ (3/100 : ℝ)*N) :
    ‖zetaPrimeLogKernel N (3/2+Complex.I*y) (m*a)‖ ≤
      Real.exp (-(δ^2/24)*(N : ℝ))*Real.exp (-Real.log a)*
        ‖zetaPrimeLogKernel N (3/2+Complex.I*y) m‖ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hTm : 0 < Real.log m := by linarith
  have hl : 0 ≤ Real.log a := Real.log_natCast_nonneg a
  have he : Real.log (a*m : ℕ) = Real.log a+Real.log m := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast ha.ne')
      (by exact_mod_cast (show m ≠ 0 by omega))]
  have hratio : Real.log (a*m : ℕ)/Real.log m ≤ 1+Real.log a/(2*(N : ℝ)) := by
    rw [he, add_div, div_self hTm.ne']
    have h := div_le_div_of_nonneg_left hl (by positivity : 0 < 2*(N : ℝ)) hT
    linarith
  have hx : 0 ≤ Real.log a/(2*(N : ℝ)) := by positivity
  have hx1 : Real.log a/(2*(N : ℝ)) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith)
  have hlog := mul_le_mul_of_nonneg_left (log_one_add_quadratic hx hx1) hn.le
  have halg : (N : ℝ)*(Real.log a/(2*N)-(Real.log a/(2*N))^2/6) =
      Real.log a/2-(Real.log a)^2/(24*N) := by field_simp; ring
  rw [halg] at hlog
  have hsquare := pow_le_pow_left₀ (mul_nonneg hδ hn.le) hlo 2
  have hsave : (δ^2/24)*(N : ℝ) ≤ (Real.log a)^2/(24*N) := by
    apply (le_div_iff₀ (by positivity : 0 < 24*(N : ℝ))).mpr
    nlinarith
  have hp : (Real.log (a*m : ℕ)/Real.log m)^N ≤
      Real.exp (Real.log a/2-(δ^2/24)*(N : ℝ)) := by
    calc
      _ ≤ (1+Real.log a/(2*(N : ℝ)))^N :=
        pow_le_pow_left₀ (div_nonneg (Real.log_natCast_nonneg _) hTm.le) hratio N
      _ = Real.exp ((N : ℝ)*Real.log (1+Real.log a/(2*(N : ℝ)))) := by
        rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  rw [Nat.mul_comm m a, ZetaRieszTypeII.kernel_mul_transport N _ ha hm]
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Real.log_natCast_nonneg _) hTm.le), norm_zetaPrimeFeature]
  have hphase : zetaPrimeExpWeight (3/2+Complex.I*(y : ℂ)).re a =
      Real.exp (-(3/2 : ℝ)*Real.log a) := by norm_num [zetaPrimeExpWeight]
  rw [hphase]
  calc
    _ ≤ (Real.exp (Real.log a/2-(δ^2/24)*(N : ℝ))*
        Real.exp (-(3/2 : ℝ)*Real.log a))*
        ‖zetaPrimeLogKernel N (3/2+Complex.I*y) m‖ := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring

/-- Staying in the original core gives the entire extension budget.
There is no quadratic-head cutoff or additional count restriction. -/
theorem core_extension_geometry {N p q r a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (ha : 0 < a) {L : ℝ}
    (hL : (137/100 : ℝ)*N ≤ L) (hLu : L ≤ (7/5 : ℝ)*N)
    (hpbox : Real.log p ≤ (67/100 : ℝ)*N)
    (hqbox : Real.log q ≤ (67/100 : ℝ)*N)
    (hrbox : Real.log r ≤ (67/100 : ℝ)*N)
    (hT : 2*(N : ℝ) ≤ Real.log (p*(q*r) : ℕ))
    (hwindow : Real.log (p*(q*(r*a)) : ℕ) ≤ (203/100 : ℝ)*N) :
    Real.log a ≤ (3/100 : ℝ)*N ∧
      Real.log p+Real.log q+Real.log a ≤ L ∧
      Real.log p+Real.log r+Real.log a ≤ L ∧
      Real.log q+Real.log r+Real.log a ≤ L ∧
      L ≤ Real.log p+Real.log q+Real.log r ∧
      Real.log (p*(q*(r*a)) : ℕ) ≤ 2*L := by
  have hlogm : Real.log (p*(q*r) : ℕ) = Real.log p+Real.log q+Real.log r := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast Nat.mul_ne_zero hq.ne_zero hr.ne_zero), Nat.cast_mul,
      Real.log_mul (by exact_mod_cast hq.ne_zero) (by exact_mod_cast hr.ne_zero)]
    ring
  have hlogn : Real.log (p*(q*(r*a)) : ℕ) = Real.log (p*(q*r) : ℕ)+Real.log a := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.cast_mul,
      Real.log_mul
        (by exact_mod_cast Nat.mul_ne_zero (Nat.mul_ne_zero hp.ne_zero hq.ne_zero) hr.ne_zero)
        (by exact_mod_cast ha.ne'), Nat.mul_assoc]
  have hn := Nat.cast_nonneg (α := ℝ) N
  have hd : Real.log a ≤ (3/100 : ℝ)*N := by linarith
  rw [hlogm] at hT
  refine ⟨hd, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

private theorem norm_prime_budget (D : Finset ℕ) (f : ℕ → ℂ) {x γ K : ℝ}
    (hx : 0 ≤ x) (hγ : 0 ≤ γ) (hK : 0 ≤ K)
    (hlog : ∀ a ∈ D, a.Prime → Real.log a ≤ x)
    (hb : ∀ a ∈ D, ‖f a‖ ≤ if a.Prime then
      2*γ*K*(Real.log a*Real.exp (-Real.log a)) else 0) :
    ‖∑ a ∈ D, f a‖ ≤ 2*γ*K*(Real.log 4*(1+x)) := by
  have hm := prime_log_mass_le (D.filter Nat.Prime) hx (by
    intro a ha
    obtain ⟨haD,hap⟩ := Finset.mem_filter.mp ha
    exact ⟨hap, hlog a haD hap⟩)
  calc
    _ ≤ ∑ a ∈ D, ‖f a‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ D, if a.Prime then 2*γ*K*(Real.log a*Real.exp (-Real.log a)) else 0 :=
      Finset.sum_le_sum hb
    _ = 2*γ*K*(∑ a ∈ D.filter Nat.Prime, Real.log a*Real.exp (-Real.log a)) := by
      rw [← Finset.sum_filter, Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)

private theorem norm_core_extensions_of_kernel (A D : Finset ℕ) {N : ℕ}
    (y : ℝ) {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    {L : ℝ} (hL0 : 0 < L)
    (hL : (137/100 : ℝ)*N ≤ L) (hLu : L ≤ (7/5 : ℝ)*N)
    (hpbox : Real.log p ≤ (67/100 : ℝ)*N)
    (hqbox : Real.log q ≤ (67/100 : ℝ)*N)
    (hrbox : Real.log r ≤ (67/100 : ℝ)*N)
    (hT : 2*(N : ℝ) ≤ Real.log (p*(q*r) : ℕ))
    (hD : ∀ a ∈ D, a ≠ 1 ∧ Squarefree (p*(q*(r*a))) ∧
      Real.log (p*(q*(r*a)) : ℕ) ≤ (203/100 : ℝ)*N)
    {x γ : ℝ} (hx : 0 ≤ x) (hγ : 0 ≤ γ)
    (hlog : ∀ a ∈ D, a.Prime → Real.log a ≤ x)
    (hkernel : ∀ a ∈ D, a.Prime →
      ‖zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*(r*a)))‖ ≤
        γ*Real.exp (-Real.log a)*‖zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*r))‖) :
    ‖∑ a ∈ D, residualCoefficient A L N (p*(q*(r*a)))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*(r*a)))‖ ≤
      2*γ*‖zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*r))‖*
        (Real.log 4*(1+x)) := by
  apply norm_prime_budget D _ hx hγ (norm_nonneg _) hlog
  intro a haD
  obtain ⟨ha1,hs,hw⟩ := hD a haD
  have ha0 : 0 < a := Nat.pos_of_ne_zero hs.of_mul_right.of_mul_right.of_mul_right.ne_zero
  obtain ⟨_,h1,h2,h3,h4,h5⟩ := core_extension_geometry hp hq hr ha0 hL hLu
    hpbox hqbox hrbox hT hw
  have hc := norm_residual_extension_le A N hp hq hr hs ha1 hL0 h1 h2 h3 h4 h5
  split_ifs at hc ⊢ with hap
  · rw [norm_mul]
    have h := mul_le_mul hc (hkernel a haD hap) (norm_nonneg _) (by positivity)
    convert h using 1 <;> first | rfl | ring
  · rw [norm_le_zero_iff.mp hc, zero_mul, norm_zero]

/-- The complete selected in-core extension sum has a two-scale budget.
The small logarithmic head costs its actual prime mass; the entire larger
head gains the exact factorial curvature factor. Composite extensions
vanish before estimation. All masks and phases stay literal. -/
theorem norm_core_extensions_split (A D : Finset ℕ) {N : ℕ} (hN : 0 < N)
    (y : ℝ) {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    {L : ℝ} (hL0 : 0 < L)
    (hL : (137/100 : ℝ)*N ≤ L) (hLu : L ≤ (7/5 : ℝ)*N)
    (hpbox : Real.log p ≤ (67/100 : ℝ)*N)
    (hqbox : Real.log q ≤ (67/100 : ℝ)*N)
    (hrbox : Real.log r ≤ (67/100 : ℝ)*N)
    (hT : 2*(N : ℝ) ≤ Real.log (p*(q*r) : ℕ))
    (hD : ∀ a ∈ D, a ≠ 1 ∧ Squarefree (p*(q*(r*a))) ∧
      Real.log (p*(q*(r*a)) : ℕ) ≤ (203/100 : ℝ)*N)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    ‖∑ a ∈ D, residualCoefficient A L N (p*(q*(r*a)))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*(r*a)))‖ ≤
      2*Real.log 4*(1+δ*N+(1+(3/100 : ℝ)*N)*Real.exp (-(δ^2/24)*(N : ℝ)))*
        ‖zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*r))‖ := by
  let f := fun a => residualCoefficient A L N (p*(q*(r*a)))*
    zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*(r*a)))
  have hm : 1 < p*(q*r) := hp.one_lt.trans_le
    (Nat.le_mul_of_pos_right p (Nat.mul_pos hq.pos hr.pos))
  have hlo := norm_core_extensions_of_kernel A (D.filter (fun a => Real.log a ≤ δ*N))
    y hp hq hr hL0 hL hLu hpbox hqbox hrbox hT
    (fun a ha => hD a (Finset.mem_filter.mp ha).1)
    (mul_nonneg hδ (Nat.cast_nonneg N)) (γ := 1) zero_le_one
    (fun a ha _ => (Finset.mem_filter.mp ha).2) (by
      intro a _ hap
      simpa only [one_mul, Nat.mul_assoc] using norm_kernel_extension_le N y hm hap.pos hT)
  have hhi := norm_core_extensions_of_kernel A (D.filter (fun a => ¬Real.log a ≤ δ*N))
    y hp hq hr hL0 hL hLu hpbox hqbox hrbox hT
    (fun a ha => hD a (Finset.mem_filter.mp ha).1)
    (x := (3/100 : ℝ)*N) (by positivity)
    (γ := Real.exp (-(δ^2/24)*(N : ℝ))) (Real.exp_nonneg _) (by
      intro a ha hap
      exact (core_extension_geometry hp hq hr hap.pos hL hLu hpbox hqbox hrbox hT
        (hD a (Finset.mem_filter.mp ha).1).2.2).1) (by
      intro a ha hap
      have haD := (Finset.mem_filter.mp ha).1
      have htop := (core_extension_geometry hp hq hr hap.pos hL hLu hpbox hqbox hrbox hT
        (hD a haD).2.2).1
      have hbot : δ*N ≤ Real.log a := le_of_lt (lt_of_not_ge (Finset.mem_filter.mp ha).2)
      simpa only [Nat.mul_assoc] using norm_kernel_extension_geometric hN y hm hap.pos hT hδ hbot htop)
  have he := Finset.sum_filter_add_sum_filter_not D (fun a => Real.log a ≤ δ*N) f
  change ‖∑ a ∈ D, f a‖ ≤ _
  rw [← he]
  exact (norm_add_le _ _).trans ((add_le_add hlo hhi).trans_eq (by ring))

/-- A quantitative relative bound for the entire extension sum, with
no bound on an individual inserted prime other than the original core.
The base allocation premise is supplied eventually by the existing
balanced-allocation theorem. This is not an absolute source-scale error. -/
theorem relative_extensions_split (A D : Finset ℕ) {N : ℕ} (hN : 0 < N)
    (y : ℝ) {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {L : ℝ} (hL0 : 0 < L)
    (hL : (137/100 : ℝ)*N ≤ L) (hLu : L ≤ (7/5 : ℝ)*N)
    (hpbox : Real.log p ≤ (67/100 : ℝ)*N)
    (hqbox : Real.log q ≤ (67/100 : ℝ)*N)
    (hrbox : Real.log r ≤ (67/100 : ℝ)*N)
    (hT : 2*(N : ℝ) ≤ Real.log (p*(q*r) : ℕ))
    (hshare : (1/2 : ℝ) ≤ 1-boundedShare A N (p*(q*r)))
    (hD : ∀ a ∈ D, a ≠ 1 ∧ Squarefree (p*(q*(r*a))) ∧
      Real.log (p*(q*(r*a)) : ℕ) ≤ (203/100 : ℝ)*N)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    ‖∑ a ∈ D, residualCoefficient A L N (p*(q*(r*a)))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*(r*a)))‖ ≤
      12*(1/(N : ℝ)+δ+(1/(N : ℝ)+3/100)*Real.exp (-(δ^2/24)*(N : ℝ)))*
        ‖residualCoefficient A L N (p*(q*r))*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*r))‖ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hb := base_atom_norm_lower A N y hp hq hr hpq hpr hqr hL0
    (by linarith : L ≤ (3/2 : ℝ)*N)
    (by linarith) (by linarith) (by linarith) hT hshare
  have hK : ‖zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*r))‖ ≤
      4/(N : ℝ)*‖residualCoefficient A L N (p*(q*r))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*r))‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hn]
    linarith
  have hlog4 : 2*Real.log 4 ≤ (3 : ℝ) := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9]
  have he : 0 ≤ 1+δ*N+(1+(3/100 : ℝ)*N)*Real.exp (-(δ^2/24)*(N : ℝ)) := by positivity
  have h := norm_core_extensions_split A D hN y hp hq hr hL0 hL hLu
    hpbox hqbox hrbox hT hD hδ
  calc
    _ ≤ 3*(1+δ*N+(1+(3/100 : ℝ)*N)*Real.exp (-(δ^2/24)*(N : ℝ)))*
        ‖zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*r))‖ :=
      h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlog4 he)
        (norm_nonneg _))
    _ ≤ 3*(1+δ*N+(1+(3/100 : ℝ)*N)*Real.exp (-(δ^2/24)*(N : ℝ)))*
        (4/(N : ℝ)*‖residualCoefficient A L N (p*(q*r))*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*r))‖) :=
      mul_le_mul_of_nonneg_left hK (by positivity)
    _ = _ := by field_simp; ring

private theorem eventually_split_budget_lt {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      12*(1/(N : ℝ)+ε/48+(1/(N : ℝ)+3/100)*
        Real.exp (-((ε/48)^2/24)*(N : ℝ))) < ε := by
  have hi : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hr : Real.exp (-((ε/48)^2/24)) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    have hp : 0 < (ε/48)^2/24 := by positivity
    linarith
  have he : Tendsto (fun N : ℕ => Real.exp (-((ε/48)^2/24)*(N : ℝ))) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_nonneg _) hr
    convert h using 1
    funext N
    rw [mul_comm, Real.exp_nat_mul]
  have ht := ((hi.add_const (ε/48)).add ((hi.add_const (3/100)).mul he)).const_mul 12
  have hlim : 12*(0+ε/48+(0+3/100)*0) < ε := by linarith
  simpa only [Function.comp_def, one_div] using ht.eventually (gt_mem_nhds hlim)

/-- A finite numerical threshold for the displayed relative budget.
The chamber and allocation hypotheses of `relative_extensions_split`
are still required. This is not an absolute source allowance. -/
theorem split_budget_lt_thousandth {N : ℕ} (hN : 1000000000000 ≤ N) :
    12*(1/(N : ℝ)+1/50000+(1/(N : ℝ)+3/100)*
      Real.exp (-((1/50000 : ℝ)^2/24)*(N : ℝ))) < 1/1000 := by
  have hn : (1000000000000 : ℝ) ≤ N := by exact_mod_cast hN
  have hi : 1/(N : ℝ) ≤ (1/100000 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hex : Real.exp (-((1/50000 : ℝ)^2/24)*(N : ℝ)) ≤ 1/1000 := by
    have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 10) 6
    norm_num [Finset.sum_range_succ] at he
    calc
      _ ≤ Real.exp (-10) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := by
        rw [Real.exp_neg]
        simpa only [one_div] using
          inv_anti₀ (by norm_num : (0 : ℝ) < 1000) (show 1000 ≤ Real.exp 10 by linarith)
  calc
    _ ≤ 12*((1/100000 : ℝ)+1/50000+(1/100000+3/100)*(1/1000)) := by gcongr
    _ < _ := by norm_num

/-- The same finite budget is already below one thousandth on the
unchanged original dyadic schedule from index 32. -/
theorem dyadic_split_budget_lt (j : ℕ) (hj : 32 ≤ j) :
    12*(1/(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j : ℝ)+1/50000+
      (1/(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j : ℝ)+3/100)*
        Real.exp (-((1/50000 : ℝ)^2/24)*
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j : ℝ))) < 1/1000 := by
  apply split_budget_lt_thousandth
  have hk : 34359738368 ≤ ZetaRieszPrimeCountFrequency.dyadicPrimeCount j := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2)
      (show 32+3 ≤ j+3 by omega)
    norm_num at h
    exact h
  unfold ZetaRieszPrimeCountFrequency.dyadicMomentOrder
  nlinarith

/-- All in-core extensions of these balanced triples have vanishing
relative mass, uniformly over moving heights, all finite selected masks
and the original allocation. Every composite extension vanishes exactly;
all prime sizes allowed by the core are included in the upper bound.
This is relative to the base atom, not to the hypothetical-zero source. -/
theorem eventually_extensions_relative_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (A D : Finset ℕ) (y : ℝ) (p q r : ℕ) (L : ℝ),
      p.Prime → q.Prime → r.Prime → p ≠ q → p ≠ r → q ≠ r →
      0 < L → (137/100 : ℝ)*N ≤ L → L ≤ (7/5 : ℝ)*N →
      Real.log p ≤ (67/100 : ℝ)*N → Real.log q ≤ (67/100 : ℝ)*N →
      Real.log r ≤ (67/100 : ℝ)*N → 2*(N : ℝ) ≤ Real.log (p*(q*r) : ℕ) →
      (1/2 : ℝ) ≤ 1-boundedShare A N (p*(q*r)) →
      (∀ a ∈ D, a ≠ 1 ∧ Squarefree (p*(q*(r*a))) ∧
        Real.log (p*(q*(r*a)) : ℕ) ≤ (203/100 : ℝ)*N) →
      ‖∑ a ∈ D, residualCoefficient A L N (p*(q*(r*a)))*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*(r*a)))‖ ≤
        ε*‖residualCoefficient A L N (p*(q*r))*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*r))‖ := by
  filter_upwards [eventually_split_budget_lt hε, eventually_ge_atTop (1 : ℕ)]
    with N hb hN A D y p q r L hp hq hr hpq hpr hqr hL0 hL hLu hpbox hqbox hrbox hT hshare hD
  exact (relative_extensions_split A D (by omega) y hp hq hr hpq hpr hqr hL0 hL hLu
    hpbox hqbox hrbox hT hshare hD (δ := ε/48) (by positivity)).trans
      (mul_le_mul_of_nonneg_right hb.le (norm_nonneg _))

/-- The relative estimate gives a two-sided signed comparison while
retaining any complementary carrier verbatim. In particular it is not
an instruction to norm or clip that complement. -/
theorem joint_signed_bounds {B D W : ℂ} {ε : ℝ} (h : ‖D‖ ≤ ε*‖B‖) :
    (W+B).re-ε*‖B‖ ≤ (W+(B+D)).re ∧
      (W+(B+D)).re ≤ (W+B).re+ε*‖B‖ := by
  have hlo := Complex.re_le_norm (-D)
  have hhi := Complex.re_le_norm D
  simp only [Complex.neg_re, norm_neg] at hlo
  simp only [Complex.add_re]
  constructor <;> linarith

/-- Even every in-core extension cannot repair a fixed negative phase
fraction of its base. The rest remains in the same signed expression. -/
theorem joint_negative_block {B D W : ℂ} {ε : ℝ}
    (h : ‖D‖ ≤ ε*‖B‖) (hphase : B.re ≤ -(1/2 : ℝ)*‖B‖) :
    (W+(B+D)).re ≤ W.re+(ε-1/2)*‖B‖ := by
  have hb := (joint_signed_bounds (W := W) h).2
  simp only [Complex.add_re] at hb ⊢
  nlinarith

/-- The actual prime boxes already used by the positive/negative phase
audits eventually satisfy the sharper balanced chamber. Their existence
is not replaced by the numerical equal-logarithm model. -/
theorem eventually_prime_boxes_in_core_chamber {C h : ℝ} (hh : 0 ≤ h) :
    ∀ᶠ N : ℕ in atTop, ∀ b : ℝ, (2/3 : ℝ)*N ≤ b → b ≤ (2/3 : ℝ)*N+C →
      ∀ n ∈ ZetaRieszAllowancePrimeBoxes.tripleProducts b h,
        2*(N : ℝ) ≤ Real.log n ∧
          ∀ p ∈ n.primeFactors, Real.log p ≤ (67/100 : ℝ)*N := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
    (300*(C+3*h+1))] with N hN b hb hb' n hn
  have hdata := ZetaRieszAllowancePrimeBoxes.tripleProducts_bounds hh hn
  constructor
  · linarith [hdata.2.2.1]
  · intro p hp
    have hl := hdata.2.2.2.2 p hp
    linarith

end
end RiemannGaussian.ZetaRieszCoreExtensions
