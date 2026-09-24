/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszZeroParityCascade

/-!
# The literal middle split does not have a uniform negative phase

The rectangle bounds the aggregate middle order. Splitting that cofactor
over two distinct middle primes retains order zero. Its factorial atom is
nonzero, but `weightedFinite ... 0` is identically zero. Thus the existing
uniform prime-phase theorem cannot be applied to every selected leg.
This is an exact range obstruction, not a lower bound on the total mass of
the exceptional orders or a disproof of a separately paid tail argument.
-/

namespace RiemannGaussian.ZetaRieszZeroParityOrders
noncomputable section
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszSkewAllocation ZetaRieszMatchedMiddle

/-- The literal binary splitting of the aggregate middle factorial order. -/
def middleSplitOrders (N j h : ℕ) : Finset ℕ :=
  Finset.range (N+1-j-h+1)

/-- Expanding the middle share preserves the original finite rectangle
weight exactly. It does not add an individual lower order cutoff. -/
theorem rectangleMass_middle_split (N : ℕ) (p c x : ℝ) :
    rectangleMass N (1-p) c =
      ∑ j ∈ Finset.range (N+2), mass (N+1) j p *
        ∑ h ∈ rectangleOrders N j, mass (N+1-j) h c *
          ∑ k ∈ middleSplitOrders N j h, mass (N+1-j-h) k x := by
  simp [middleSplitOrders, mass_total, rectangleMass]

/-- Zero remains selected at every outer rectangle order. -/
theorem zero_mem_middleSplitOrders (N j h : ℕ) : 0 ∈ middleSplitOrders N j h := by
  simp [middleSplitOrders]

/-- The zero-order share is positive for two positive middle-prime logs. -/
theorem zero_middle_mass_pos (N j h : ℕ) {x : ℝ} (hx : x < 1) :
    0 < mass (N+1-j-h) 0 x := by
  simp only [mass, pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one,
    one_mul, mul_one]
  exact pow_pos (by linarith) _

/-- The actual factorial kernel on a product has the same split, with
the full complex phases. This is a finite identity, not completion. -/
theorem middle_kernel_split (M : ℕ) (s : ℂ) {a b : ℕ} (ha : a.Prime) (hb : b.Prime) :
    zetaPrimeLogKernel M s (a*b) =
      ∑ k ∈ Finset.range (M+1), zetaPrimeLogKernel k s a*zetaPrimeLogKernel (M-k) s b := by
  rw [ZetaPrimeCofactorCompletion.logKernel_product M s ha.pos hb.pos, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold zetaPrimeLogKernel
  ring

/-- The retained zero-order atom is nonzero on actual prime arguments;
it is not an empty formal index in the convolution. -/
theorem zero_middle_kernel_ne_zero (M : ℕ) (s : ℂ) {a b : ℕ}
    (ha : a.Prime) (hb : b.Prime) :
    zetaPrimeLogKernel 0 s a*zetaPrimeLogKernel M s b ≠ 0 := by
  have haLog : (Real.log a : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast ha.one_lt)).ne'
  have hbLog : (Real.log b : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hb.one_lt)).ne'
  unfold zetaPrimeLogKernel
  apply mul_ne_zero
  · exact mul_ne_zero (div_ne_zero (pow_ne_zero _ haLog)
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))) (Complex.exp_ne_zero _)
  · exact mul_ne_zero (div_ne_zero (pow_ne_zero _ hbLog)
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))) (Complex.exp_ne_zero _)

/-- The extra derivative factor in `weightedFinite` kills order zero.
No zero hypothesis can change this exact unit phase error. -/
theorem zero_order_phase_error (u y : ℝ) (N : ℕ) :
    ‖weightedFinite u y N 0+1‖ = 1 := by simp [weightedFinite]

/-- Therefore the existing negative-phase estimate is false when
quantified over every literal middle split, even at arbitrarily large N. -/
theorem not_uniform_phase_on_middle_split (u y : ℝ) (N j h : ℕ)
    {ε : ℝ} (hε : ε < 1) :
    ¬ ∀ k ∈ middleSplitOrders N j h, ‖weightedFinite u y N k+1‖ ≤ ε := by
  intro hall
  have hh := hall 0 (zero_mem_middleSplitOrders N j h)
  rw [zero_order_phase_error] at hh
  linarith

/-- A concrete cofinal sequence of selected outer orders. All three
aggregate orders are in range; one individual middle leg still has order zero. -/
theorem concrete_rectangle_split {m : ℕ} (hm : 1 ≤ m) :
    8*m-1 ∈ rectangleOrders (400*m) (220*m) ∧
      400*m+1-220*m-(8*m-1) = 172*m+2 ∧
        0 ∈ middleSplitOrders (400*m) (220*m) (8*m-1) ∧
          ¬400*m ≤ 100*(0 : ℕ) := by
  constructor
  · simp only [rectangleOrders, ZetaRieszWideOwnerAudit.ownerOrders,
      Finset.mem_filter, Finset.mem_range]
    omega
  · exact ⟨by omega, zero_mem_middleSplitOrders _ _ _, by omega⟩

/-- The range failure occurs at every sufficiently large order, so it
cannot be avoided by restricting to the original dyadic schedule. -/
theorem selected_zero_every_large_order {N : ℕ} (hN : 100 ≤ N) :
    N/50 ∈ rectangleOrders N (11*N/20) ∧
      0 ∈ middleSplitOrders N (11*N/20) (N/50) ∧ ¬N ≤ 100*(0 : ℕ) := by
  constructor
  · simp only [rectangleOrders, ZetaRieszWideOwnerAudit.ownerOrders,
      Finset.mem_filter, Finset.mem_range]
    omega
  · exact ⟨zero_mem_middleSplitOrders _ _ _, by omega⟩

/-- No cofinal moment schedule admits the proposed uniform replacement
on all literal split orders. This includes the existing dyadic schedule. -/
theorem not_eventually_uniform_literal_split (u y : ℝ) (orders : ℕ → ℕ)
    (horders : Filter.Tendsto orders Filter.atTop Filter.atTop)
    {ε : ℝ} (hε : ε < 1) :
    ¬ ∀ᶠ t : ℕ in Filter.atTop, ∀ j < orders t+2,
      ∀ h ∈ rectangleOrders (orders t) j,
        ∀ k ∈ middleSplitOrders (orders t) j h,
          ‖weightedFinite u y (orders t) k+1‖ ≤ ε := by
  intro h
  obtain ⟨t, ht, htN⟩ := (h.and (horders.eventually (Filter.eventually_ge_atTop 100))).exists
  obtain ⟨hh, _, _⟩ := selected_zero_every_large_order htN
  have hj : 11*orders t/20 < orders t+2 := by omega
  exact not_uniform_phase_on_middle_split u y (orders t) (11*orders t/20) (orders t/50)
    hε (ht _ hj _ hh)

/-- On those four separate legs the proposed parity replacement has
unit error, not convergence to the fourth power of minus one. This does
not assert unit error after summing their factorial weights. -/
theorem concrete_product_phase_error (u y : ℝ) (m : ℕ) :
    ‖weightedFinite u y (400*m) (220*m)*weightedFinite u y (400*m) 0 *
      weightedFinite u y (400*m) (172*m+2)*weightedFinite u y (400*m) (8*m)-
        (-1 : ℂ)^4‖ = 1 := by
  simp [weightedFinite]

end
end RiemannGaussian.ZetaRieszZeroParityOrders
