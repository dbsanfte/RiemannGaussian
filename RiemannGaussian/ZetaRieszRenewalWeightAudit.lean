/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszLeastPrimeRenewal

/-!
# Quantitative transport checks for least-prime renewal

Prime deletion changes the literal unit log cell and transports the entire
factorial kernel, not a fixed smooth weight. The density-compensated kernel
is nondecreasing up to its gamma saddle. Thus a strict contraction cannot
be supplied merely by prime deletion and that kernel. These are precise
obstructions to an autonomous unweighted renewal estimate, not a disproof
of cancellation for the actual signed, masked arithmetic form.
-/

namespace RiemannGaussian.ZetaRieszTypeII
noncomputable section
open scoped BigOperators

/-- Exact prime-insertion transport of the original complex factorial
kernel. Both its logarithmic ratio and its full prime phase remain. -/
theorem kernel_mul_transport (N : ℕ) (s : ℂ) {r m : ℕ} (hr : 0 < r) (hm : 1 < m) :
    zetaPrimeLogKernel N s (r * m) =
      ((Real.log (r * m : ℕ) / Real.log m : ℝ) : ℂ) ^ N *
        zetaPrimeFeature s r * zetaPrimeLogKernel N s m := by
  have hlog : (Real.log m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.log_pos (by exact_mod_cast hm : (1 : ℝ) < m)).ne'
  rw [zetaPrimeLogKernel, zetaPrimeLogKernel,
    CoprimeEulerPhase.feature_mul s hr (by omega), Complex.ofReal_div, div_pow]
  field_simp

/-- Cell normalization leaves the same exact multiplicative transport;
it does not remove the order-dependent logarithmic ratio. -/
theorem cellKernel_mul_transport (N k : ℕ) (y : ℝ) {r m : ℕ}
    (hr : 0 < r) (hm : 1 < m) :
    cellKernel N k y (r * m) =
      ((Real.log (r * m : ℕ) / Real.log m : ℝ) : ℂ) ^ N *
        zetaPrimeFeature (3 / 2 + Complex.I * y) r * cellKernel N k y m := by
  simp only [cellKernel, kernel_mul_transport N _ hr hm]
  ring

/-- Deleting any prime at least three leaves the original unit logarithmic
cell. Its support indicator therefore cannot be silently inherited by the child. -/
theorem prime_deletion_changes_cell {r m : ℕ} (hr : 3 ≤ r) (hm : 0 < m) :
    ⌊Real.log (r * m : ℕ)⌋₊ ≠ ⌊Real.log m⌋₊ := by
  have hlogr : 1 < Real.log r := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
      (by exact_mod_cast hr : (3 : ℝ) ≤ r)
    linarith [Real.log_three_gt_d9]
  have he : Real.log (r * m : ℕ) = Real.log r + Real.log m := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast (show r ≠ 0 by omega))
      (by exact_mod_cast hm.ne')]
  intro h
  have hlo := Nat.floor_le (Real.log_natCast_nonneg m)
  have hhi := Nat.lt_floor_add_one (Real.log (r * m : ℕ))
  rw [h, he] at hhi
  linarith

/-- The literal cell mask is not closed under prime deletion, regardless
of the other support restrictions. No removed child is declared paid. -/
theorem cellBand_not_closed {u : ℝ} {N K k r m : ℕ} (hr : 3 ≤ r) (hm : 0 < m)
    (hn : r * m ∈ cellBand u N K k) : m ∉ cellBand u N K k := by
  intro hchild
  exact prime_deletion_changes_cell hr hm
    ((Finset.mem_filter.mp hn).2.trans (Finset.mem_filter.mp hchild).2.symm)

/-- The gamma amplitude including the coefficient's additional logarithm
increases all the way to its actual saddle at twice the order plus two. -/
theorem gamma_amplitude_monotone (N : ℕ) :
    MonotoneOn (fun x : ℝ => x ^ (N + 1) * Real.exp (-x / 2))
      (Set.Icc 0 (2 * (N + 1 : ℝ))) := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => x ^ (N + 1) * Real.exp (-x / 2))
      (x ^ N * Real.exp (-x / 2) * ((N + 1 : ℝ) - x / 2)) x := by
    have hp : HasDerivAt (fun x : ℝ => x ^ (N + 1)) ((N + 1 : ℝ) * x ^ N) x := by
      simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using
        (hasDerivAt_pow (N + 1) x)
    have he : HasDerivAt (fun x : ℝ => Real.exp (-x / 2))
        (Real.exp (-x / 2) * (-(1 : ℝ) / 2)) x :=
      ((hasDerivAt_id x).neg.div_const 2).exp
    apply (hp.mul he).congr_deriv
    rw [pow_succ]
    ring
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · fun_prop
  · intro x _
    exact (hd x).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioo 0 (2 * (N + 1 : ℝ)) := by simpa only [interior_Icc] using hx
    rw [(hd x).deriv]
    exact mul_nonneg (mul_nonneg (pow_nonneg hx'.1.le _) (Real.exp_pos _).le) (by linarith [hx'.2])

/-- The density-compensated literal kernel, including the extra coefficient
logarithm, is exactly the gamma amplitude divided by the original factorial. -/
theorem density_kernel_eq (N : ℕ) (y : ℝ) {m : ℕ} (hm : 0 < m) :
    (m : ℝ) * Real.log m * ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) m‖ =
      Real.log m ^ (N + 1) * Real.exp (-Real.log m / 2) / (N.factorial : ℝ) := by
  rw [norm_zetaPrimeLogKernel]
  have hs : (3 / 2 + Complex.I * (y : ℂ)).re = (3 / 2 : ℝ) := by norm_num
  rw [hs, zetaPrimeExpWeight]
  have he : (m : ℝ) * Real.exp (-(3 / 2 : ℝ) * Real.log m) =
      Real.exp (-Real.log m / 2) := by
    calc
      _ = Real.exp (Real.log m) * Real.exp (-(3 / 2 : ℝ) * Real.log m) := by
        rw [Real.exp_log (by exact_mod_cast hm : (0 : ℝ) < m)]
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ = (Real.log m ^ (N + 1) / (N.factorial : ℝ)) *
        ((m : ℝ) * Real.exp (-(3 / 2 : ℝ) * Real.log m)) := by rw [pow_succ]; ring
    _ = _ := by rw [he]; ring

/-- Through the lower half of the actual narrow window, deleting a
prime does not give a strict decrease of the density-compensated factorial
weight. This is an inequality for the literal kernel, at every height. -/
theorem density_kernel_noncontracting (N : ℕ) (y : ℝ) {r m : ℕ}
    (hr : 1 ≤ r) (hm : 0 < m) (hupper : Real.log (r * m : ℕ) ≤ 2 * (N + 1 : ℝ)) :
    Real.log m * ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) m‖ ≤
      (r : ℝ) * Real.log (r * m : ℕ) *
        ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) (r * m)‖ := by
  have hrm : 0 < r * m := Nat.mul_pos (by omega) hm
  have hlog : Real.log m ≤ Real.log (r * m : ℕ) := by
    apply Real.log_le_log (by exact_mod_cast hm)
    exact_mod_cast (show m ≤ r * m by nlinarith)
  have hg := gamma_amplitude_monotone N
    ⟨Real.log_natCast_nonneg m, hlog.trans hupper⟩
    ⟨Real.log_natCast_nonneg _, hupper⟩ hlog
  have hh := div_le_div_of_nonneg_right hg (show (0 : ℝ) ≤ N.factorial by positivity)
  rw [← density_kernel_eq N y hm, ← density_kernel_eq N y hrm, Nat.cast_mul] at hh
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h' : (m : ℝ) * (Real.log m * ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) m‖) ≤
      (m : ℝ) * ((r : ℝ) * Real.log (r * m : ℕ) *
        ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) (r * m)‖) := by
    simpa only [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using hh
  exact (mul_le_mul_iff_right₀ hmR).mp h'

/-- No uniform factor strictly below one can be obtained from this
prime-deletion kernel transport below its saddle. Arithmetic sign and
correlation estimates would have to supply the missing saving. -/
theorem no_strict_density_contraction (N : ℕ) (y : ℝ) {r m : ℕ}
    (hr : 1 ≤ r) (hm : 1 < m) (hupper : Real.log (r * m : ℕ) ≤ 2 * (N + 1 : ℝ))
    {c : ℝ} (hc : c < 1) :
    ¬(r : ℝ) * Real.log (r * m : ℕ) *
        ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) (r * m)‖ ≤
      c * (Real.log m * ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) m‖) := by
  have hh := density_kernel_noncontracting N y hr (by omega) hupper
  have hpos : 0 < Real.log m * ‖zetaPrimeLogKernel N (3 / 2 + Complex.I * y) m‖ := by
    rw [norm_zetaPrimeLogKernel, zetaPrimeExpWeight]
    have hlog := Real.log_pos (by exact_mod_cast hm : (1 : ℝ) < m)
    positivity
  intro h
  nlinarith

end
end RiemannGaussian.ZetaRieszTypeII
