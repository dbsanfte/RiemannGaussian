/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCompletionPayment
import RiemannGaussian.ZetaRieszCofactorBoundary

/-!
# Saturation pays the unshifted marked-mode cofactor

The exact least-prime factorial selection is retained. The composite
cofactor hinge vanishes below the original Riesz length; its remaining
tail has geometric decay at the complementary orders of the rectangle.
No composite cofactor is completed and no prime phase is approximated.
-/

namespace RiemannGaussian.ZetaRieszUnshiftedCofactor
noncomputable section
open scoped BigOperators Classical
open Complex Filter MeasureTheory Set Topology
open ZetaRieszJointAllocation ZetaRieszParityOrderTail ZetaRieszSkewAllocation
open ZetaRieszMarkedEuler ZetaRieszJointPrimeTransfer ZetaRieszJointCofactor

/-- Every cofactor order is retained except the literal least-prime
rectangle mask; the complementary total order is exact. -/
def allocations (N j a : ℕ) : Finset (ℕ → ℕ) :=
  (Finset.piAntidiag a.primeFactors (N+1-j)).filter
    (fun d => d a.minFac ∈ rectangleOrders N j)

/-- The finite factorial probability of that exact cofactor selection. -/
def share (N j a : ℕ) : ℝ :=
  ∑ d ∈ allocations N j a,
    allocationWeight a.primeFactors (fun p => Real.log p/Real.log a) d

/-- This is the literal product of ordinary-prime factorial kernels,
including every zero order allowed by the original selection. -/
def allocationKernel (N j a : ℕ) (s : ℂ) : ℂ :=
  ∑ d ∈ allocations N j a, ∏ p ∈ a.primeFactors, zetaPrimeLogKernel (d p) s p

theorem share_nonneg (N j a : ℕ) : 0 ≤ share N j a := by
  exact Finset.sum_nonneg (fun d _ => allocationWeight_nonneg _ _
    (fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg a)) d)

theorem share_le_one {a : ℕ} (ha : Squarefree a) (ha1 : 1 < a) (N j : ℕ) :
    share N j a ≤ 1 := by
  have hx (p : ℕ) (_hp : p ∈ a.primeFactors) : 0 ≤ Real.log p/Real.log a :=
    div_nonneg (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg a)
  have hsum : (∑ p ∈ a.primeFactors, Real.log p/Real.log a) = 1 := by
    rw [← Finset.sum_div,← CoprimeEulerPhase.squarefree_log_eq_prime_sum ha]
    exact div_self (Real.log_pos (by exact_mod_cast ha1)).ne'
  calc
    _ ≤ ∑ d ∈ Finset.piAntidiag a.primeFactors (N+1-j),
        allocationWeight a.primeFactors (fun p => Real.log p/Real.log a) d :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun d _ _ => allocationWeight_nonneg _ _ hx d)
    _ = _ := by
      simp only [allocationWeight]
      rw [← Finset.sum_pow_eq_sum_piAntidiag,hsum,one_pow]

/-- The common full complex phase is exact before taking a norm. -/
theorem allocationKernel_eq {a : ℕ} (ha : Squarefree a) (ha1 : 1 < a)
    (N j : ℕ) (s : ℂ) :
    allocationKernel N j a s = (share N j a : ℂ)*zetaPrimeLogKernel (N+1-j) s a := by
  unfold allocationKernel share
  rw [Complex.ofReal_sum,Finset.sum_mul]
  exact Finset.sum_congr rfl (fun d hd =>
    (allocation_kernel ha ha1 (Finset.mem_filter.mp hd).1 s).symm)

/-- No artificial cofactor order is introduced when the marked
rectangle is empty. -/
theorem allocationKernel_eq_zero {N j : ℕ} (hj : rectangleOrders N j = ∅)
    (a : ℕ) (s : ℂ) : allocationKernel N j a s = 0 := by
  simp [allocationKernel,allocations,hj]

/-- The unshifted marked term sees the original cofactor hinge. -/
def orderResponse (T : Finset ℕ) (N j : ℕ) (L : ℝ) (s : ℂ) : ℂ :=
  ∑ a ∈ T, (VaughanLogAverage.riesz L a : ℂ)*allocationKernel N j a s

/-- Saturation is used before the absolute allowance. The displayed
bound pays the full surviving cofactor mass and retains all selections. -/
theorem orderResponse_bound (T : Finset ℕ)
    (hT : ∀ a ∈ T, Squarefree a ∧ 1 < a ∧ ¬a.Prime)
    (N j : ℕ) (y : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ‖orderResponse T N j L (3/2+Complex.I*y)‖ ≤
      L*(1024/255 : ℝ)^(N+1-j)*Real.exp (-L/4)*divisorSquareDirichletMass (1025/1024) := by
  have hb (a : ℕ) (ha : a ∈ T) :
      ‖(VaughanLogAverage.riesz L a : ℂ)*allocationKernel N j a (3/2+Complex.I*y)‖ ≤
        (L*(1024/255 : ℝ)^(N+1-j)*Real.exp (-L/4))*
          ((a.divisors.card : ℝ)^2*(a : ℝ)^(-(1025/1024 : ℝ))) := by
    obtain ⟨hs,ha1,hp⟩ := hT a ha
    have he : boundaryCoefficient 0 L a = (VaughanLogAverage.riesz L a : ℂ) := by
      unfold boundaryCoefficient
      rw [if_pos ⟨hs,by omega,hp,by simpa using hs.ne_zero⟩]
    rw [allocationKernel_eq hs ha1,mul_left_comm,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (share_nonneg N j a)]
    apply (mul_le_of_le_one_left (norm_nonneg _) (share_le_one hs ha1 N j)).trans
    rw [← he]
    exact boundary_atom_bound 0 a (N+1-j) y hL
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum hb).trans
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    ((summable_card_divisors_sq_mul_rpow_neg (by norm_num : (1 : ℝ) < 1025/1024)).sum_le_tsum T
      (fun _ _ => by positivity)) (by positivity)

/-- The complementary order is at most 19N/40+1. Its saturated tail
beats the worst source radius by a fixed exponential factor. -/
theorem complementary_rate {N j h : ℕ} (hj : j ∈ Finset.range (N+2))
    (hh : h ∈ rectangleOrders N j) {u L : ℝ} (hu : 0 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hL : (11/8 : ℝ)*N ≤ L) :
    u^(N+1-j)*(1024/255 : ℝ)^(N+1-j)*Real.exp (-L/4) ≤
      3*Real.exp (-(N : ℝ)/100) := by
  have hb := (Finset.mem_filter.mp hh).2
  have hjM : j ≤ N+1 := by have := Finset.mem_range.mp hj; omega
  have hjr : 21*(N : ℝ) ≤ 40*j := by exact_mod_cast hb.2.1
  have hkR : ((N+1-j : ℕ) : ℝ) ≤ 19/40*(N : ℝ)+1 := by
    rw [Nat.cast_sub hjM,Nat.cast_add,Nat.cast_one]
    linarith
  have hlog : Real.log (ZetaRieszWideOwnerAudit.radiusCeiling*(1024/255)) ≤ 7/10 := by
    apply (Real.log_le_iff_le_exp (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])).mpr
    have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 7/10) 7
    norm_num [Finset.sum_range_succ,ZetaRieszWideOwnerAudit.radiusCeiling] at he ⊢
    linarith
  have hlu : Real.log (u*(1024/255)) ≤ 7/10 :=
    (Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_right hU (by norm_num))).trans hlog
  rw [← mul_pow,show (u*(1024/255))^(N+1-j) =
    Real.exp ((N+1-j : ℕ)*Real.log (u*(1024/255))) by
      rw [Real.exp_nat_mul,Real.exp_log (by positivity)],← Real.exp_add]
  have he : ((N+1-j : ℕ) : ℝ)*Real.log (u*(1024/255))-L/4 ≤ 7/10-(N : ℝ)/100 := by
    have hmul := mul_le_mul_of_nonneg_left hlu (Nat.cast_nonneg (α := ℝ) (N+1-j))
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  rw [neg_div,← sub_eq_add_neg]
  apply (Real.exp_le_exp.mpr he).trans
  rw [Real.exp_sub]
  have he3 : Real.exp (7/10 : ℝ) ≤ 3 := by
    apply (Real.exp_le_exp.mpr (by norm_num : (7/10 : ℝ) ≤ 1)).trans
    exact Real.exp_one_lt_d9.le.trans (by norm_num)
  calc
    _ ≤ 3/Real.exp ((N : ℝ)/100) := div_le_div_of_nonneg_right he3 (Real.exp_pos _).le
    _ = _ := by rw [neg_div,Real.exp_neg]; ring

/-- The exact arithmetic unshifted-mode contribution. Its selected-mode
coefficient is kept, rather than assigned an absolute Fourier cost. -/
def unshiftedResponse (T : Finset ℕ) (N : ℕ) (L y : ℝ) (z : ℂ) : ℂ :=
  -((N+1 : ℕ) : ℂ)/(L : ℂ)*
    ∑ j ∈ Finset.range (N+2), ((-z)⁻¹)^j/(j : ℂ)*
      orderResponse T N j L (3/2+Complex.I*y)

theorem scaled_mode_le {u : ℝ} (hu : 0 < u) {z : ℂ} (hz : u ≤ ‖z‖)
    {N j : ℕ} (hj : j ≤ N+1) :
    u^(N+1)*‖(-z)⁻¹‖^j ≤ u^(N+1-j) := by
  have hi : ‖(-z)⁻¹‖ ≤ u⁻¹ := by
    rw [norm_inv,norm_neg]
    exact (inv_le_inv₀ (hu.trans_le hz) hu).mpr hz
  apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hi j) (pow_nonneg hu.le _)).trans_eq
  have hp : u^j ≠ 0 := pow_ne_zero j hu.ne'
  calc
    _ = (u^j*u^(N+1-j))*(u^j)⁻¹ := by rw [← pow_add,Nat.add_sub_of_le hj,inv_pow]
    _ = _ := by field_simp

/-- This bound includes the selected source denominator |z|=u. Exact
composite saturation makes the unshifted contribution decay nonetheless. -/
theorem unshiftedResponse_bound (T : Finset ℕ)
    (hT : ∀ a ∈ T, Squarefree a ∧ 1 < a ∧ ¬a.Prime)
    (N : ℕ) (y : ℝ) {u L : ℝ} (hu : 0 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hL0 : 0 < L)
    (hL : (11/8 : ℝ)*N ≤ L) {z : ℂ} (hz : u ≤ ‖z‖) :
    ‖(u : ℂ)^(N+1)*unshiftedResponse T N L y z‖ ≤
      3*divisorSquareDirichletMass (1025/1024)*((N : ℝ)+1)*((N : ℝ)+2)*
        Real.exp (-(N : ℝ)/100) := by
  have hmass : 0 ≤ divisorSquareDirichletMass (1025/1024) := divisorSquareDirichletMass_nonneg _
  have hb (j : ℕ) (hj : j ∈ Finset.range (N+2)) :
      ‖(u : ℂ)^(N+1)*(((-z)⁻¹)^j/(j : ℂ)*orderResponse T N j L (3/2+Complex.I*y))‖ ≤
        3*L*divisorSquareDirichletMass (1025/1024)*Real.exp (-(N : ℝ)/100) := by
    by_cases hempty : rectangleOrders N j = ∅
    · simp only [orderResponse,allocationKernel_eq_zero hempty,mul_zero,Finset.sum_const_zero,norm_zero]
      positivity
    obtain ⟨h,hh⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hj0 := ZetaRieszMarkedLogDerivative.marked_order_pos hh
    have hjM : j ≤ N+1 := by have := Finset.mem_range.mp hj; omega
    have hnorm : ‖((-z)⁻¹)^j/(j : ℂ)‖ ≤ ‖(-z)⁻¹‖^j := by
      rw [norm_div,norm_pow,Complex.norm_natCast]
      exact div_le_self (by positivity) (by exact_mod_cast hj0)
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu,norm_mul]
    apply (mul_le_mul_of_nonneg_left
      (mul_le_mul hnorm (orderResponse_bound T hT N j y hL0.le) (norm_nonneg _) (by positivity))
      (pow_nonneg hu.le _)).trans
    calc
      _ = (u^(N+1)*‖(-z)⁻¹‖^j)*
          ((1024/255 : ℝ)^(N+1-j)*Real.exp (-L/4))*(L*divisorSquareDirichletMass (1025/1024)) := by ring
      _ ≤ u^(N+1-j)*((1024/255 : ℝ)^(N+1-j)*Real.exp (-L/4))*
          (L*divisorSquareDirichletMass (1025/1024)) := by
        gcongr
        exact scaled_mode_le hu hz hjM
      _ ≤ (3*Real.exp (-(N : ℝ)/100))*(L*divisorSquareDirichletMass (1025/1024)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa only [mul_assoc] using complementary_rate hj hh hu hU hL
      _ = _ := by ring
  have hsum : ‖(u : ℂ)^(N+1)*(∑ j ∈ Finset.range (N+2),
      ((-z)⁻¹)^j/(j : ℂ)*orderResponse T N j L (3/2+Complex.I*y))‖ ≤
        ((N : ℝ)+2)*(3*L*divisorSquareDirichletMass (1025/1024)*Real.exp (-(N : ℝ)/100)) := by
    rw [Finset.mul_sum]
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum hb).trans_eq
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat]
  unfold unshiftedResponse
  rw [mul_left_comm,norm_mul,norm_div,norm_neg,Complex.norm_natCast,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL0]
  apply (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq
  push_cast
  field_simp

/-- Both Fourier signs of the same finite composite cofactor selection. -/
def cofactorPair (T : Finset ℕ) (N j : ℕ) (s : ℂ) (L xi : ℝ) : ℂ :=
  ∑ a ∈ T, allocationKernel N j a s*ZetaRieszPrimeFourier.primePair a L xi

/-- The geometric estimate is for a literal signed Fourier component:
all divisor cancellations and all finite factorial weights are exact. -/
theorem orderResponse_eq_integral (T : Finset ℕ)
    (hT : ∀ a ∈ T, Squarefree a ∧ 1 < a ∧ ¬a.Prime)
    (N j : ℕ) (s : ℂ) (L : ℝ) :
    orderResponse T N j L s = -(1/(2*(Real.pi : ℂ)))*
      ∫ xi : ℝ in Ioi 0, cofactorPair T N j s L xi/(xi : ℂ)^2 := by
  have hi (a : ℕ) (ha : a ∈ T) :=
    (ZetaRieszPrimeFourier.integrable_primePair_div_sq (hT a ha).1
      (by have := (hT a ha).2.1; omega) L).const_mul (allocationKernel N j a s)
  simp_rw [cofactorPair,Finset.sum_div,mul_div_assoc]
  rw [integral_finsetSum _ hi,Finset.mul_sum]
  unfold orderResponse
  apply Finset.sum_congr rfl
  intro a ha
  rw [ZetaRieszPrimeFourier.riesz_eq_primePair_integral L (hT a ha).1
    (by have := (hT a ha).2.1; omega) (hT a ha).2.2,integral_const_mul]
  ring

/-- The integral retains exactly the original least-prime rectangular
selection, rather than a limiting log-share indicator. -/
theorem selected_cofactor_identity {a : ℕ} (ha1 : 1 < a)
    (N j : ℕ) (s : ℂ) (xi : ℝ) :
    ZetaRieszPrimeFourier.primeProduct a xi*allocationKernel N j a s =
      ∑ h ∈ rectangleOrders N j, PowerSeries.coeff h (leg s xi a.minFac)*
        PowerSeries.coeff (N+1-j-h) (∏ p ∈ a.primeFactors.erase a.minFac, leg s xi p) := by
  have hr : a.minFac ∈ a.primeFactors :=
    (Nat.minFac_prime ha1.ne').mem_primeFactors (Nat.minFac_dvd a) (by omega)
  have hh := selected_single a.primeFactors hr (fun p => leg s xi p) (N+1-j)
    (fun h => h ∈ rectangleOrders N j)
  have he : (∑ d ∈ Finset.piAntidiag a.primeFactors (N+1-j),
      if d a.minFac ∈ rectangleOrders N j then
        ∏ p ∈ a.primeFactors, PowerSeries.coeff (d p) (leg s xi p) else 0) =
        ZetaRieszPrimeFourier.primeProduct a xi*allocationKernel N j a s := by
    rw [← Finset.sum_filter]
    simp only [coeff_leg,Finset.prod_mul_distrib,← Finset.mul_sum]
    rfl
  rw [he] at hh
  have hsub : rectangleOrders N j ⊆ Finset.range (N+1-j+1) := Finset.filter_subset _ _
  rw [hh,← Finset.sum_filter,Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr hsub]

end
end RiemannGaussian.ZetaRieszUnshiftedCofactor
