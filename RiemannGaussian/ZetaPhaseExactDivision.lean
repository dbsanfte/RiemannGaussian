/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseDivisionStability
import RiemannGaussian.ZetaPhaseDivisionData

/-!
# Enclosing the exact high-frequency quotients

The rational synthetic arrays are now connected to actual Chebyshev
polynomials divided at the proved exact contacts. The signed recurrence
and all eight intermediate carriers remain available; bounds are taken
only after the exact identities have been established.
-/

open scoped Classical Polynomial
open Polynomial

namespace RiemannGaussian

noncomputable section

set_option maxHeartbeats 4000000 in
private theorem division_base_polynomial (i : Fin 3) :
    Chebyshev.T ℝ (phaseContactFrequency ⟨i.val + 6, by omega⟩ : ℤ) =
      ∑ k : Fin 25, C (phaseContactDivisionCenterQ i 0 k.val : ℝ) * X ^ k.val := by
  have h0 : Chebyshev.T ℝ 0 = 1 := Chebyshev.T_zero ℝ
  have h1 : Chebyshev.T ℝ 1 = X := Chebyshev.T_one ℝ
  have h2 : Chebyshev.T ℝ 2 = (-1) * X ^ 0 + (2) * X ^ 2 := by
    calc
      _ = 2 * X * Chebyshev.T ℝ 1 - Chebyshev.T ℝ 0 := Chebyshev.T_add_two ℝ 0
      _ = _ := by rw [h1, h0]; ring
  have h3 : Chebyshev.T ℝ 3 = (-3) * X ^ 1 + (4) * X ^ 3 := by
    calc
      _ = 2 * X * Chebyshev.T ℝ 2 - Chebyshev.T ℝ 1 := Chebyshev.T_add_two ℝ 1
      _ = _ := by rw [h2, h1]; ring
  have h4 : Chebyshev.T ℝ 4 = (1) * X ^ 0 + (-8) * X ^ 2 + (8) * X ^ 4 := by
    calc
      _ = 2 * X * Chebyshev.T ℝ 3 - Chebyshev.T ℝ 2 := Chebyshev.T_add_two ℝ 2
      _ = _ := by rw [h3, h2]; ring
  have h5 : Chebyshev.T ℝ 5 = (5) * X ^ 1 + (-20) * X ^ 3 + (16) * X ^ 5 := by
    calc
      _ = 2 * X * Chebyshev.T ℝ 4 - Chebyshev.T ℝ 3 := Chebyshev.T_add_two ℝ 3
      _ = _ := by rw [h4, h3]; ring
  have h6 : Chebyshev.T ℝ 6 = (-1) * X ^ 0 + (18) * X ^ 2 + (-48) * X ^ 4 + (32) * X ^ 6 := by
    calc
      _ = 2 * X * Chebyshev.T ℝ 5 - Chebyshev.T ℝ 4 := Chebyshev.T_add_two ℝ 4
      _ = _ := by rw [h5, h4]; ring
  have h7 : Chebyshev.T ℝ 7 = (-7) * X ^ 1 + (56) * X ^ 3 + (-112) * X ^ 5 + (64) * X ^ 7 := by
    calc
      _ = 2 * X * Chebyshev.T ℝ 6 - Chebyshev.T ℝ 5 := Chebyshev.T_add_two ℝ 5
      _ = _ := by rw [h6, h5]; ring
  have h8 : Chebyshev.T ℝ 8 = (1) * X ^ 0 + (-32) * X ^ 2 + (160) * X ^ 4 + (-256) * X ^ 6 + (128) * X ^ 8 := by
    calc
      _ = 2 * X * Chebyshev.T ℝ 7 - Chebyshev.T ℝ 6 := Chebyshev.T_add_two ℝ 6
      _ = _ := by rw [h7, h6]; ring
  have h9 : Chebyshev.T ℝ 9 = (9) * X ^ 1 + (-120) * X ^ 3 + (432) * X ^ 5 + (-576) * X ^ 7 + (256) * X ^ 9 := by
    calc
      _ = 2 * X * Chebyshev.T ℝ 8 - Chebyshev.T ℝ 7 := Chebyshev.T_add_two ℝ 7
      _ = _ := by rw [h8, h7]; ring
  have h10 : Chebyshev.T ℝ 10 = (-1) * X ^ 0 + (50) * X ^ 2 + (-400) * X ^ 4 + (1120) * X ^ 6 + (-1280) * X ^ 8 + (512) * X ^ 10 := by
    calc
      _ = 2 * X * Chebyshev.T ℝ 9 - Chebyshev.T ℝ 8 := Chebyshev.T_add_two ℝ 8
      _ = _ := by rw [h9, h8]; ring
  have h11 : Chebyshev.T ℝ 11 = (-11) * X ^ 1 + (220) * X ^ 3 + (-1232) * X ^ 5 + (2816) * X ^ 7 + (-2816) * X ^ 9 + (1024) * X ^ 11 := by
    calc
      _ = 2 * X * Chebyshev.T ℝ 10 - Chebyshev.T ℝ 9 := Chebyshev.T_add_two ℝ 9
      _ = _ := by rw [h10, h9]; ring
  have h12 : Chebyshev.T ℝ 12 = (1) * X ^ 0 + (-72) * X ^ 2 + (840) * X ^ 4 + (-3584) * X ^ 6 + (6912) * X ^ 8 + (-6144) * X ^ 10 + (2048) * X ^ 12 := by
    calc
      _ = 2 * X * Chebyshev.T ℝ 11 - Chebyshev.T ℝ 10 := Chebyshev.T_add_two ℝ 10
      _ = _ := by rw [h11, h10]; ring
  have h13 : Chebyshev.T ℝ 13 = (13) * X ^ 1 + (-364) * X ^ 3 + (2912) * X ^ 5 + (-9984) * X ^ 7 + (16640) * X ^ 9 + (-13312) * X ^ 11 + (4096) * X ^ 13 := by
    calc
      _ = 2 * X * Chebyshev.T ℝ 12 - Chebyshev.T ℝ 11 := Chebyshev.T_add_two ℝ 11
      _ = _ := by rw [h12, h11]; ring
  have h14 : Chebyshev.T ℝ 14 = (-1) * X ^ 0 + (98) * X ^ 2 + (-1568) * X ^ 4 + (9408) * X ^ 6 + (-26880) * X ^ 8 + (39424) * X ^ 10 + (-28672) * X ^ 12 + (8192) * X ^ 14 := by
    calc
      _ = 2 * X * Chebyshev.T ℝ 13 - Chebyshev.T ℝ 12 := Chebyshev.T_add_two ℝ 12
      _ = _ := by rw [h13, h12]; ring
  have h15 : Chebyshev.T ℝ 15 = (-15) * X ^ 1 + (560) * X ^ 3 + (-6048) * X ^ 5 + (28800) * X ^ 7 + (-70400) * X ^ 9 + (92160) * X ^ 11 + (-61440) * X ^ 13 + (16384) * X ^ 15 := by
    calc
      _ = 2 * X * Chebyshev.T ℝ 14 - Chebyshev.T ℝ 13 := Chebyshev.T_add_two ℝ 13
      _ = _ := by rw [h14, h13]; ring
  have h16 : Chebyshev.T ℝ 16 = (1) * X ^ 0 + (-128) * X ^ 2 + (2688) * X ^ 4 + (-21504) * X ^ 6 + (84480) * X ^ 8 + (-180224) * X ^ 10 + (212992) * X ^ 12 + (-131072) * X ^ 14 + (32768) * X ^ 16 := by
    calc
      _ = 2 * X * Chebyshev.T ℝ 15 - Chebyshev.T ℝ 14 := Chebyshev.T_add_two ℝ 14
      _ = _ := by rw [h15, h14]; ring
  have h17 : Chebyshev.T ℝ 17 = (17) * X ^ 1 + (-816) * X ^ 3 + (11424) * X ^ 5 + (-71808) * X ^ 7 + (239360) * X ^ 9 + (-452608) * X ^ 11 + (487424) * X ^ 13 + (-278528) * X ^ 15 + (65536) * X ^ 17 := by
    calc
      _ = 2 * X * Chebyshev.T ℝ 16 - Chebyshev.T ℝ 15 := Chebyshev.T_add_two ℝ 15
      _ = _ := by rw [h16, h15]; ring
  have h18 : Chebyshev.T ℝ 18 = (-1) * X ^ 0 + (162) * X ^ 2 + (-4320) * X ^ 4 + (44352) * X ^ 6 + (-228096) * X ^ 8 + (658944) * X ^ 10 + (-1118208) * X ^ 12 + (1105920) * X ^ 14 + (-589824) * X ^ 16 + (131072) * X ^ 18 := by
    calc
      _ = 2 * X * Chebyshev.T ℝ 17 - Chebyshev.T ℝ 16 := Chebyshev.T_add_two ℝ 16
      _ = _ := by rw [h17, h16]; ring
  have h19 : Chebyshev.T ℝ 19 = (-19) * X ^ 1 + (1140) * X ^ 3 + (-20064) * X ^ 5 + (160512) * X ^ 7 + (-695552) * X ^ 9 + (1770496) * X ^ 11 + (-2723840) * X ^ 13 + (2490368) * X ^ 15 + (-1245184) * X ^ 17 + (262144) * X ^ 19 := by
    calc
      _ = 2 * X * Chebyshev.T ℝ 18 - Chebyshev.T ℝ 17 := Chebyshev.T_add_two ℝ 17
      _ = _ := by rw [h18, h17]; ring
  have h20 : Chebyshev.T ℝ 20 = (1) * X ^ 0 + (-200) * X ^ 2 + (6600) * X ^ 4 + (-84480) * X ^ 6 + (549120) * X ^ 8 + (-2050048) * X ^ 10 + (4659200) * X ^ 12 + (-6553600) * X ^ 14 + (5570560) * X ^ 16 + (-2621440) * X ^ 18 + (524288) * X ^ 20 := by
    calc
      _ = 2 * X * Chebyshev.T ℝ 19 - Chebyshev.T ℝ 18 := Chebyshev.T_add_two ℝ 18
      _ = _ := by rw [h19, h18]; ring
  have h21 : Chebyshev.T ℝ 21 = (21) * X ^ 1 + (-1540) * X ^ 3 + (33264) * X ^ 5 + (-329472) * X ^ 7 + (1793792) * X ^ 9 + (-5870592) * X ^ 11 + (12042240) * X ^ 13 + (-15597568) * X ^ 15 + (12386304) * X ^ 17 + (-5505024) * X ^ 19 + (1048576) * X ^ 21 := by
    calc
      _ = 2 * X * Chebyshev.T ℝ 20 - Chebyshev.T ℝ 19 := Chebyshev.T_add_two ℝ 19
      _ = _ := by rw [h20, h19]; ring
  have h22 : Chebyshev.T ℝ 22 = (-1) * X ^ 0 + (242) * X ^ 2 + (-9680) * X ^ 4 + (151008) * X ^ 6 + (-1208064) * X ^ 8 + (5637632) * X ^ 10 + (-16400384) * X ^ 12 + (30638080) * X ^ 14 + (-36765696) * X ^ 16 + (27394048) * X ^ 18 + (-11534336) * X ^ 20 + (2097152) * X ^ 22 := by
    calc
      _ = 2 * X * Chebyshev.T ℝ 21 - Chebyshev.T ℝ 20 := Chebyshev.T_add_two ℝ 20
      _ = _ := by rw [h21, h20]; ring
  have h23 : Chebyshev.T ℝ 23 = (-23) * X ^ 1 + (2024) * X ^ 3 + (-52624) * X ^ 5 + (631488) * X ^ 7 + (-4209920) * X ^ 9 + (17145856) * X ^ 11 + (-44843008) * X ^ 13 + (76873728) * X ^ 15 + (-85917696) * X ^ 17 + (60293120) * X ^ 19 + (-24117248) * X ^ 21 + (4194304) * X ^ 23 := by
    calc
      _ = 2 * X * Chebyshev.T ℝ 22 - Chebyshev.T ℝ 21 := Chebyshev.T_add_two ℝ 21
      _ = _ := by rw [h22, h21]; ring
  have h24 : Chebyshev.T ℝ 24 = (1) * X ^ 0 + (-288) * X ^ 2 + (13728) * X ^ 4 + (-256256) * X ^ 6 + (2471040) * X ^ 8 + (-14057472) * X ^ 10 + (50692096) * X ^ 12 + (-120324096) * X ^ 14 + (190513152) * X ^ 16 + (-199229440) * X ^ 18 + (132120576) * X ^ 20 + (-50331648) * X ^ 22 + (8388608) * X ^ 24 := by
    calc
      _ = 2 * X * Chebyshev.T ℝ 23 - Chebyshev.T ℝ 22 := Chebyshev.T_add_two ℝ 22
      _ = _ := by rw [h23, h22]; ring
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ C (phaseContactDivisionCenterQ i 0 k : ℝ) * X ^ k) 25]
  fin_cases i <;>
    norm_num [phaseContactFrequency, phaseContactDivisionCenterQ_initial, Finset.sum_range_succ, C_ofNat] <;>
    first | (rw [h10]; ring) | (rw [h13]; ring) | (rw [h24]; ring)

private theorem division_base_coeff (i : Fin 3) (k : Fin 25) :
    (Chebyshev.T ℝ (phaseContactFrequency ⟨i.val + 6, by omega⟩ : ℤ)).coeff k.val =
      (phaseContactDivisionCenterQ i 0 k.val : ℝ) := by
  rw [division_base_polynomial]
  simp [Fin.val_inj]

/-- The exact-root high-frequency carrier after any intermediate division. -/
def phaseContactExactDivision (i : Fin 3) (j : ℕ) : ℝ[X] :=
  phaseContactDivisionStage (fun k ↦ phaseContactExactRoot (phaseContactCosineCoordinate k))
    (Chebyshev.T ℝ (phaseContactFrequency ⟨i.val + 6, by omega⟩ : ℤ)) j

private theorem exactDivision_degree (i : Fin 3) (j : ℕ) :
    (phaseContactExactDivision i j).natDegree ≤ 24 := by
  apply (phaseContactDivisionStage_natDegree_le _ _ _).trans
  simp only [Chebyshev.natDegree_T, Int.natAbs_natCast]
  fin_cases i <;> norm_num [phaseContactFrequency]

private theorem exactDivision_point (j : Fin 8) :
    phaseContactDivisionPoint (fun k ↦ phaseContactExactRoot (phaseContactCosineCoordinate k)) j.val =
      phaseContactExactRoot ⟨j.val / 2, by omega⟩ := by
  dsimp only [phaseContactDivisionPoint, phaseContactCosineCoordinate]
  congr 1
  apply Fin.ext
  exact Nat.mod_eq_of_lt (by omega)

/-- Every intermediate true coefficient is enclosed using the checked
rational recurrence residual and the independently isolated exact root. -/
theorem abs_phaseContactExactDivision_sub_center_le (i : Fin 3) (j : Fin 9) (k : Fin 25) :
    |(phaseContactExactDivision i j.val).coeff k.val -
      (phaseContactDivisionCenterQ i j k.val : ℝ)| ≤ (50 : ℝ) ^ j.val / 10 ^ 24 := by
  have hstage (n : ℕ) (hn : n ≤ 8) : ∀ k : Fin 25,
      |(phaseContactExactDivision i n).coeff k.val -
        (phaseContactDivisionCenterQ i ⟨n, by omega⟩ k.val : ℝ)| ≤ (50 : ℝ) ^ n / 10 ^ 24 := by
    induction n with
    | zero =>
      intro k
      change |(Chebyshev.T ℝ (phaseContactFrequency ⟨i.val + 6, by omega⟩ : ℤ)).coeff k.val -
        (phaseContactDivisionCenterQ i 0 k.val : ℝ)| ≤ _
      rw [division_base_coeff]
      norm_num
    | succ n ih =>
      have hn' : n ≤ 8 := by omega
      have ih' := ih hn'
      let j' : Fin 8 := ⟨n, by omega⟩
      let q := phaseContactExactRoot ⟨n / 2, by omega⟩
      let c := (phaseContactRootCenterQ ⟨n / 2, by omega⟩ : ℝ)
      have hq : |q| ≤ 1 := by
        exact (abs_phaseContactExactRoot_cosine_lt_one ⟨n / 2, by omega⟩).le
      have hqc : |q - c| ≤ (1 / 10 ^ 38 : ℝ) := by
        have h := (norm_le_pi_norm (phaseContactExactRoot - phaseContactRootCenter)
          ⟨n / 2, by omega⟩).trans phaseContactExactRoot_dist_le_refined
        exact h.trans (by norm_num)
      have he : 0 ≤ (50 : ℝ) ^ n / 10 ^ 24 := by positivity
      have h50 : (1 : ℝ) ≤ 50 ^ n := one_le_pow₀ (by norm_num)
      intro k
      have h := abs_coeff_divByMonic_sub_center_le
        (p := phaseContactExactDivision i n) (q := q) (c := c)
        (e := (50 : ℝ) ^ n / 10 ^ 24) (r := 1 / 10 ^ 38) (M := 10 ^ 9) (d := 1 / 10 ^ 25)
        (u := fun l ↦ (phaseContactDivisionCenterQ i ⟨n, by omega⟩ l : ℝ))
        (v := fun l ↦ (phaseContactDivisionCenterQ i ⟨n + 1, by omega⟩ l : ℝ))
        (exactDivision_degree i n) hq he (by norm_num) (by norm_num) (by norm_num) hqc
        (fun l hl ↦ ih' ⟨l, by omega⟩)
        (fun l _ ↦ by exact_mod_cast abs_phaseContactDivisionCenterQ_le i ⟨n + 1, by omega⟩ l)
        (by exact_mod_cast phaseContactDivisionCenterQ_top_eq_zero i j')
        (fun l hl ↦ by
          have h := (Rat.cast_le (K := ℝ)).mpr
            (phaseContactDivisionCenterQ_residual i j' ⟨l, by omega⟩)
          push_cast at h
          exact h)
        (k := k.val) (by omega)
      have hpoint := exactDivision_point j'
      have hstep : phaseContactExactDivision i (n + 1) =
          phaseContactExactDivision i n /ₘ (X - C q) := by
        unfold phaseContactExactDivision
        rw [phaseContactDivisionStage, hpoint]
      rw [hstep]
      apply h.trans
      rw [pow_succ (50 : ℝ) n]
      nlinarith only [h50]
  exact hstage j.val (by omega) k

/-- All coefficients of each of the three canonical high-frequency
quotients are within `10⁻¹⁰` of the checked rational center. -/
theorem abs_phaseContactDeflate_high_coeff_sub_center_le (i : Fin 3) (k : Fin 25) :
    |(phaseContactDeflate (fun j ↦ phaseContactExactRoot (phaseContactCosineCoordinate j))
        (Chebyshev.T ℝ (phaseContactFrequency ⟨i.val + 6, by omega⟩ : ℤ))).coeff k.val -
      (phaseContactDivisionCenterQ i 8 k.val : ℝ)| ≤ (1 / 10 ^ 10 : ℝ) := by
  have h := abs_phaseContactExactDivision_sub_center_le i 8 k
  change |(phaseContactDivisionStage _ _ 8).coeff k.val - _| ≤ _ at h
  rw [phaseContactDivisionStage_eight] at h
  exact h.trans (by norm_num)

end

end RiemannGaussian
