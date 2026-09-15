/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeCofactorCompletion

/-!
# Power decay for the completed quadratic cofactor head

The exact damped integer floor gives a physical length growing at least
linearly in N. For every selected cofactor set in [1,N^2], its completed
head has normalized bound C*N^(-(beta-1/2)) at exposed right-half zeros.
Constants and eventual thresholds may depend on the zero and fixed filter.
Transfer to the actual finite semiprime band is proved in later modules.
-/

namespace RiemannGaussian.ZetaRieszCompletedCofactor
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaExposedZero
open ZetaExposedPrimeMoments
open ZetaPrimeCofactorCompletion

/-- Both logarithms in the cofactor mass are paid by any positive
real-power slack, using the first two terms of the exponential series. -/
theorem cofactor_log_mass_atom_le (beta : ℝ) {eps : ℝ} (heps : 0 < eps)
    (a : ℕ) :
    Real.log a * (1 + Real.log a) * Real.exp (-beta * Real.log a) ≤
      (eps⁻¹ + 2 * eps⁻¹ ^ 2) * Real.exp (-(beta - eps) * Real.log a) := by
  have h1 := logMoment_exp_envelope 1 (Real.log_natCast_nonneg a) heps beta
  have h2 := logMoment_exp_envelope 2 (Real.log_natCast_nonneg a) heps beta
  norm_num at h1 h2
  simp only [neg_sub, neg_mul, inv_pow] at h1 h2 ⊢
  nlinarith

/-- Every positive finite cofactor prefix has a full arithmetic mass
bound. Prime restriction is optional, so any cofactor subset inherits it. -/
theorem cofactor_log_mass_prefix_le {beta eps : ℝ} (heps : 0 < eps)
    (halpha : 0 < 1 - beta + eps) (A : Finset ℕ) (K : ℕ)
    (hA : ∀ a ∈ A, 0 < a ∧ a ≤ K) :
    (∑ a ∈ A, Real.log a * (1 + Real.log a) * Real.exp (-beta * Real.log a)) ≤
      (eps⁻¹ + 2 * eps⁻¹ ^ 2) * (1 + 1 / (1 - beta + eps)) *
        (K : ℝ) ^ (1 - beta + eps) := by
  have hC : 0 ≤ eps⁻¹ + 2 * eps⁻¹ ^ 2 := by positivity
  calc
    _ ≤ (eps⁻¹ + 2 * eps⁻¹ ^ 2) *
        ∑ a ∈ A, (a : ℝ) ^ ((1 - beta + eps) - 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro a ha
      apply (cofactor_log_mass_atom_le beta heps a).trans_eq
      congr 1
      rw [Real.rpow_def_of_pos (by exact_mod_cast (hA a ha).1)]
      congr 1
      ring
    _ ≤ (eps⁻¹ + 2 * eps⁻¹ ^ 2) *
        ∑ a ∈ Finset.Icc 1 K, (a : ℝ) ^ ((1 - beta + eps) - 1) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro a ha
        exact Finset.mem_Icc.mpr ⟨(hA a ha).1, (hA a ha).2⟩
      · intro a _ _
        exact Real.rpow_nonneg (Nat.cast_nonneg a) _
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (ZetaRieszGeneralCofactorTilt.sum_rpow_prefix_le halpha K) hC

/-- The actual physical length eventually dominates a positive
linear function of moment order. The integer floor is retained. -/
theorem eventually_linear_length_lower {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * N ≤ SquarefreeVaughanLogSource.length u N := by
  have hui : 1 < u⁻¹ := (one_lt_inv₀ hu).mpr hu1
  obtain ⟨r, hr, hru⟩ := exists_between hui
  have hur : u * r < 1 := by
    have h := mul_lt_mul_of_pos_left hru hu
    rwa [mul_inv_cancel₀ hu.ne'] at h
  refine ⟨2 * Real.log r, mul_pos (by norm_num) (Real.log_pos hr), ?_⟩
  filter_upwards [ZetaVaughanCutoffBudget.eventually_geometricCutoff_lt_linearDampedCutoff hu hr.le hur]
    with N hN
  have hfloor : r ^ N < (zetaMoebiusGeometricCutoff r N : ℝ) + 1 := Nat.lt_floor_add_one (r ^ N)
  have hcast : (zetaMoebiusGeometricCutoff r N : ℝ) <
      ZetaVaughanCutoffBudget.linearDampedCutoff u N := by exact_mod_cast hN
  have hle : r ^ N ≤ (ZetaVaughanCutoffBudget.linearDampedCutoff u N : ℝ) + 2 := by linarith
  have hlog := Real.log_le_log (pow_pos (by linarith : 0 < r) N) hle
  rw [Real.log_pow] at hlog
  rw [SquarefreeVaughanLogSource.length, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith

/-- An explicit negative power controls the quadratic cofactor mass
at the physical length. Constants may depend on beta and u, but no
prime restriction, filter choice or zero hypothesis is needed. -/
theorem exists_quadratic_cofactor_mass_power_bound {beta u : ℝ}
    (hb : 1 / 2 < beta) (hb1 : beta < 1) (hu : 0 < u) (hu1 : u < 1)
    (A : ℕ → Finset ℕ) (hA : ∀ N a, a ∈ A N → 0 < a ∧ a ≤ N ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      (∑ a ∈ A N, Real.log a * (1 + Real.log a) * Real.exp (-beta * Real.log a)) /
        SquarefreeVaughanLogSource.length u N ≤ C * (N : ℝ) ^ (-(beta - 1 / 2)) := by
  let eps : ℝ := (beta - 1 / 2) / 2
  let alpha : ℝ := 1 - beta + eps
  have heps : 0 < eps := by dsimp [eps]; linarith
  have halpha : 0 < alpha := by dsimp [alpha, eps]; linarith
  obtain ⟨c, hc, hlength⟩ := eventually_linear_length_lower hu hu1
  let D : ℝ := (eps⁻¹ + 2 * eps⁻¹ ^ 2) * (1 + 1 / alpha)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D / c, div_nonneg hD hc.le, ?_⟩
  filter_upwards [hlength, eventually_ge_atTop 1] with N hL hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hmass := cofactor_log_mass_prefix_le heps halpha (A N) (N ^ 2) (hA N)
  change _ ≤ D * ((N ^ 2 : ℕ) : ℝ) ^ alpha at hmass
  have hpow : ((N ^ 2 : ℕ) : ℝ) ^ alpha = (N : ℝ) ^ (2 * alpha) := by
    rw [Nat.cast_pow]
    simpa using (Real.rpow_natCast_mul (Nat.cast_nonneg N) 2 alpha).symm
  rw [hpow] at hmass
  calc
    _ ≤ (D * (N : ℝ) ^ (2 * alpha)) / SquarefreeVaughanLogSource.length u N :=
      div_le_div_of_nonneg_right hmass (SquarefreeVaughanLogSource.length_pos u N).le
    _ ≤ (D * (N : ℝ) ^ (2 * alpha)) / (c * N) :=
      div_le_div_of_nonneg_left (mul_nonneg hD (Real.rpow_nonneg (Nat.cast_nonneg N) _))
        (mul_pos hc hN0) hL
    _ = D / c * ((N : ℝ) ^ (2 * alpha) / N) := by ring
    _ = _ := by
      rw [← Real.rpow_sub_one hN0.ne']
      congr 2
      dsimp [alpha, eps]
      ring

/-- The explicit cofactor mass through N squared, divided by the
actual physical length, tends to zero for every beta strictly above one
half and below one. This is an arithmetic allowance, with no zero premise. -/
theorem tendsto_quadratic_cofactor_mass_div_length {beta u : ℝ}
    (hb : 1 / 2 < beta) (hb1 : beta < 1) (hu : 0 < u) (hu1 : u < 1)
    (A : ℕ → Finset ℕ) (hA : ∀ N a, a ∈ A N → 0 < a ∧ a ≤ N ^ 2) :
    Tendsto (fun N : ℕ =>
      (∑ a ∈ A N, Real.log a * (1 + Real.log a) * Real.exp (-beta * Real.log a)) /
        SquarefreeVaughanLogSource.length u N) atTop (𝓝 0) := by
  obtain ⟨C, _hC, hbound⟩ := exists_quadratic_cofactor_mass_power_bound hb hb1 hu hu1 A hA
  have hp := (tendsto_rpow_neg_atTop (show 0 < beta - 1 / 2 by linarith)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply squeeze_zero' ?_ hbound (by simpa using hp.const_mul C)
  exact Filter.Eventually.of_forall (fun N => div_nonneg
    (Finset.sum_nonneg fun a _ => by positivity) (SquarefreeVaughanLogSource.length_pos u N).le)

/-- The whole completed prime-factor head through N squared decays
at an exposed right-half zero, with the original physical length and any
fixed polynomial filter. Returning to the finite band is still separate. -/
theorem tendsto_completed_quadratic_cofactor_head (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (P : Polynomial ℂ) (A : ℕ → Finset ℕ)
    (hA : ∀ N a, a ∈ A N → 0 < a ∧ a ≤ N ^ 2) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      completedCofactorHead (A N) P N (3 / 2 + Complex.I * (rho.1.im : ℂ))
        (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_completedCofactorHead_bound rho hrho hexposed
  let u : ℝ := 3 / 2 - rho.1.re
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  let F : ℝ := ∑ k ∈ P.support, ‖P.coeff k‖ * u⁻¹ ^ k
  have hlim := (tendsto_quadratic_cofactor_mass_div_length hrho
    (NontrivialZetaZero.re_lt_one rho) hu hu1 A hA).const_mul (C * F)
  apply squeeze_zero_norm (fun N => ?_) (by simpa only [mul_zero] using hlim)
  have h := hbound (A N) (fun a ha => (hA N a ha).1) P N
    (SquarefreeVaughanLogSource.length u N) (SquarefreeVaughanLogSource.length_pos u N)
  exact h.trans_eq (by dsimp [F]; ring)

/-- The completed quadratic head has a concrete negative-power rate,
with the same complete filter and original physical floor. This bound is
not yet a deletion theorem for the finite semiprime band. -/
theorem exists_completed_quadratic_head_power_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (P : Polynomial ℂ) (A : ℕ → Finset ℕ)
    (hA : ∀ N a, a ∈ A N → 0 < a ∧ a ≤ N ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        completedCofactorHead (A N) P N (3 / 2 + Complex.I * (rho.1.im : ℂ))
          (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)‖ ≤
        C * (N : ℝ) ^ (-(rho.1.re - 1 / 2)) := by
  obtain ⟨C, hC, hbound⟩ := exists_completedCofactorHead_bound rho hrho hexposed
  let u : ℝ := 3 / 2 - rho.1.re
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  let F : ℝ := ∑ k ∈ P.support, ‖P.coeff k‖ * u⁻¹ ^ k
  have hF : 0 ≤ F := Finset.sum_nonneg fun k _ => by positivity
  obtain ⟨D, hD, hmass⟩ := exists_quadratic_cofactor_mass_power_bound hrho
    (NontrivialZetaZero.re_lt_one rho) hu hu1 A hA
  refine ⟨C * F * D, by positivity, ?_⟩
  filter_upwards [hmass] with N hN
  have h := hbound (A N) (fun a ha => (hA N a ha).1) P N
    (SquarefreeVaughanLogSource.length u N) (SquarefreeVaughanLogSource.length_pos u N)
  apply h.trans
  calc
    _ = (C * F) * ((∑ a ∈ A N, Real.log a * (1 + Real.log a) *
        Real.exp (-rho.1.re * Real.log a)) / SquarefreeVaughanLogSource.length u N) := by
      dsimp [F]
      ring
    _ ≤ (C * F) * (D * (N : ℝ) ^ (-(rho.1.re - 1 / 2))) :=
      mul_le_mul_of_nonneg_left hN (mul_nonneg hC hF)
    _ = _ := by ring

end
end RiemannGaussian.ZetaRieszCompletedCofactor
