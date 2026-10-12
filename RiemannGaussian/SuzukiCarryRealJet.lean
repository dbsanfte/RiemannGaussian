/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryCellCertificate
import RiemannGaussian.SuzukiCarryExceptionalPhase

/-!
# Positivity of the actual real-exponent quadratic carry jet

The small-cell lower bound and the large-cell sign are certified by finite
rational Bernstein identities. No boundary-model identification is used.
-/
namespace RiemannGaussian.SuzukiCarryRealJet
noncomputable section
open Complex MeasureTheory Set Filter
open SuzukiCarryMellinLimit SuzukiCarryMellinJet SuzukiCarryMellinBranches
open SuzukiCarrySmallCell SuzukiCarryExceptionalPhase
open scoped BigOperators Topology
set_option maxHeartbeats 0
set_option maxRecDepth 4096

private def bernstein (n i : ℕ) (x : ℝ) : ℝ :=
  (n.choose i : ℝ)*x^i*(1-x)^(n-i)

private theorem bernstein_nonneg (n i : ℕ) {x : ℝ} (hx : x ∈ Icc 0 1) :
    0 ≤ bernstein n i x := by
  have h0 := hx.1
  have h1 : 0 ≤ 1-x := sub_nonneg.mpr hx.2
  unfold bernstein
  positivity

private def smallCertificate (v : ℕ) : Fin 3 → Fin 5 → ℚ := match v with
  | 0 => ![![(1/8), (1/8), (109/864), (37/288), (19/144)],
      ![(1/8), (1/8), (109/864), (887/6912), (227/1728)],
      ![(1/8), (1/8), (109/864), (443/3456), (2713/20736)]]
  | 1 => ![![(19/144), (13/96), (121/864), (7/48), (11/72)],
      ![(227/1728), (929/6912), (239/1728), (247/1728), (4/27)],
      ![(2713/20736), (173/1296), (709/5184), (91/648), (187/1296)]]
  | 2 => ![![(11/72), (83/576), (59/432), (25/192), (1/8)],
      ![(4/27), (119/864), (221/1728), (91/768), (7/64)],
      ![(187/1296), (919/6912), (211/1728), (343/3072), (13/128)]]
  | 3 => ![![(1/8), (23/192), (13/108), (73/576), (5/36)],
      ![(7/64), (27/256), (23/216), (193/1728), (13/108)],
      ![(13/128), (305/3072), (233/2304), (61/576), (73/648)]]
  | 4 => ![![(5/36), (7/48), (125/864), (13/96), (17/144)],
      ![(13/108), (113/864), (227/1728), (851/6912), (185/1728)],
      ![(73/648), (1313/10368), (2687/20736), (2569/20736), (2315/20736)]]
  | 5 => ![![(17/144), (29/288), (65/864), (1/24), 0],
      ![(185/1728), (629/6912), (29/432), (7/192), 0],
      ![(2315/20736), (229/2304), (557/6912), (11/192), (1/32)]]
  | 6 => ![![0, (1/24), (65/864), (29/288), (17/144)],
      ![0, (3/64), (1/12), (763/6912), (223/1728)],
      ![(1/32), (5/64), (781/6912), (955/6912), (3227/20736)]]
  | 7 => ![![(17/144), (13/96), (125/864), (7/48), (5/36)],
      ![(223/1728), (1021/6912), (91/576), (139/864), (17/108)],
      ![(3227/20736), (3589/20736), (3791/20736), (1937/10368), (121/648)]]
  | 8 => ![![(5/36), (73/576), (13/108), (23/192), (1/8)],
      ![(17/108), (245/1728), (29/216), (103/768), (9/64)],
      ![(121/648), (287/1728), (361/2304), (481/3072), (21/128)]]
  | 9 => ![![(1/8), (25/192), (59/432), (83/576), (11/72)],
      ![(9/64), (109/768), (251/1728), (65/432), (17/108)],
      ![(21/128), (487/3072), (271/1728), (365/2304), (211/1296)]]
  | 10 => ![![(11/72), (7/48), (121/864), (13/96), (19/144)],
      ![(17/108), (257/1728), (245/1728), (943/6912), (229/1728)],
      ![(211/1296), (197/1296), (745/5184), (713/5184), (2761/20736)]]
  | 11 => ![![(19/144), (37/288), (109/864), (1/8), (1/8)],
      ![(229/1728), (889/6912), (109/864), (1/8), (1/8)],
      ![(2761/20736), (445/3456), (109/864), (1/8), (1/8)]]
  | _ => 0

private theorem smallCertificate_nonneg {v : ℕ} (hv : v < 12) (i : Fin 3) (j : Fin 5) :
    0 ≤ (smallCertificate v i j : ℝ) := by
  have hq : ∀ i : Fin 3, ∀ j : Fin 5, 0 ≤ smallCertificate v i j := by
    interval_cases v <;> decide +kernel
  exact_mod_cast hq i j

private theorem smallCertificate_identity {v : ℕ} (hv : v < 12) (x t : ℝ) :
    smallMoment 1 v x t^2-smallMoment 0 v x t*smallMoment 2 v x t+1/8 =
      ∑ i : Fin 3, ∑ j : Fin 5, (smallCertificate v i j : ℝ)*
        bernstein 2 i.val x*bernstein 4 j.val t := by
  interval_cases v <;>
    norm_num [smallMoment, smallCoefficient, smallTable, smallCertificate, bernstein, Nat.choose,
      Fin.sum_univ_succ] <;>
    ring

/-- The negative part of the literal quadratic density is uniformly small
at the accumulating grid; all twelve fractional cell types are retained. -/
theorem quadraticDensity_small_lower {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    -x^2/8 ≤ quadraticDensity x := by
  let v := ⌊12/x⌋₊%12
  let t := 12/x-(⌊12/x⌋₊ : ℝ)
  have hv : v < 12 := Nat.mod_lt _ (by norm_num)
  have ht : t ∈ Icc 0 1 := by
    constructor
    · exact sub_nonneg.mpr (Nat.floor_le (by positivity : 0 ≤ 12/x))
    · dsimp [t]
      have h := Nat.lt_floor_add_one (12/x)
      linarith
  have hn : 0 ≤ smallMoment 1 v x t^2-smallMoment 0 v x t*smallMoment 2 v x t+1/8 := by
    rw [smallCertificate_identity hv]
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (mul_nonneg (smallCertificate_nonneg hv i j)
      (bernstein_nonneg _ _ ⟨hx.le,hx1⟩)) (bernstein_nonneg _ _ ht)
  unfold quadraticDensity
  rw [moment_eq_small (j := 0) (by norm_num) hx,
    moment_eq_small (j := 1) (by norm_num) hx,
    moment_eq_small (j := 2) (by norm_num) hx]
  change -x^2/8 ≤ (x*smallMoment 1 v x t)^2-
    (x*smallMoment 0 v x t)*(x*smallMoment 2 v x t)
  nlinarith [mul_nonneg (sq_nonneg x) hn]

private def largeCertificate (n : ℕ) : Fin 5 → ℚ := match n with
  | 4 => ![(108/625), (27/125), (9/40), (27/160), 0]
  | 5 => ![0, (1/20), (1/10), (18/125), (108/625)]
  | 6 => ![(540/2401), (72/343), (17/98), (3/28), 0]
  | 7 => ![(27/128), (405/1792), (369/1568), (81/343), (540/2401)]
  | 8 => ![(8/81), (5/54), (5/48), (9/64), (27/128)]
  | 9 => ![(36/625), (7/125), (41/675), (2/27), (8/81)]
  | 10 => ![(144/14641), (108/6655), (78/3025), (54/1375), (36/625)]
  | 11 => ![0, 0, (1/726), (6/1331), (144/14641)]
  | _ => 0

private theorem largeCertificate_nonneg {n : ℕ} (hn : n ∈ Icc 4 11) (i : Fin 5) :
    0 ≤ (largeCertificate n i : ℝ) := by
  rcases hn with ⟨hlo,hhi⟩
  have hq : ∀ i : Fin 5, 0 ≤ largeCertificate n i := by
    interval_cases n <;> decide +kernel
  exact_mod_cast hq i

private theorem largeCertificate_identity {n : ℕ} (hn : n ∈ Icc 4 11) (t : ℝ) :
    branchB n (12/(n+1 : ℕ)+(12/(n : ℝ)-12/(n+1 : ℕ))*t) =
      ∑ i : Fin 5, (largeCertificate n i : ℝ)*bernstein 4 i.val t := by
  rcases hn with ⟨hlo,hhi⟩
  interval_cases n <;>
    norm_num [branchB, branchMoment, powerPrefix, Finset.sum_range_succ,
      largeCertificate, bernstein, Nat.choose, Fin.sum_univ_succ] <;> ring

private theorem largeBranch_nonneg {n : ℕ} (hn : n ∈ Icc 4 11) {x : ℝ}
    (hx : x ∈ Icc ((12 : ℝ)/(n+1 : ℕ)) (12/(n : ℝ))) : 0 ≤ branchB n x := by
  rcases hn with ⟨hn4,hn11⟩
  have hd : 0 < 12/(n : ℝ)-12/(n+1 : ℕ) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hn1 : (0 : ℝ) < (n+1 : ℕ) := by positivity
    apply sub_pos.mpr
    apply div_lt_div_of_pos_left (by norm_num) hn0
    norm_num
  let t := (x-12/(n+1 : ℕ))/(12/(n : ℝ)-12/(n+1 : ℕ))
  have ht : t ∈ Icc 0 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) hd.le
    · rw [div_le_iff₀ hd, one_mul]
      linarith [hx.2]
  have he : x = 12/(n+1 : ℕ)+(12/(n : ℝ)-12/(n+1 : ℕ))*t := by
    dsimp [t]
    rw [mul_comm _ ((x-12/(n+1 : ℕ))/(12/(n : ℝ)-12/(n+1 : ℕ))),
      div_mul_cancel₀ _ hd.ne']
    ring
  rw [he, largeCertificate_identity ⟨hn4,hn11⟩]
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (largeCertificate_nonneg ⟨hn4,hn11⟩ i) (bernstein_nonneg _ _ ht)

/-- The whole upper half of the literal profile has nonnegative quadratic
jet. This is a density sign, not a signed arithmetic statistic estimate. -/
theorem quadraticDensity_nonneg_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ quadraticDensity x := by
  have hx0 : 0 < x := by linarith
  let n := ⌊12/x⌋₊
  have hn : n ≤ 12 := by
    apply Nat.floor_le_of_le
    change 12/x ≤ (12 : ℝ)
    rw [div_le_iff₀ hx0]
    nlinarith
  rw [quadraticDensity_eq_branch hx0]
  change 0 ≤ branchB n x
  by_cases h4 : 4 ≤ n
  · by_cases h12 : n = 12
    · have hx1 : x = 1 := by
        have h := Nat.floor_le (by positivity : 0 ≤ 12/x)
        change (n : ℝ) ≤ 12/x at h
        rw [h12, le_div_iff₀ hx0] at h
        norm_num at h
        linarith
      rw [h12,hx1]
      norm_num [branchB,branchMoment,powerPrefix,Finset.sum_range_succ]
    · have hn' : n ∈ Icc 4 11 := ⟨h4,by omega⟩
      apply largeBranch_nonneg hn'
      constructor
      · apply (div_le_iff₀ (show (0 : ℝ) < (n+1 : ℕ) by positivity)).mpr
        have h := Nat.lt_floor_add_one (12/x)
        have h' : 12/x < (n+1 : ℕ) := by
          simpa only [n,Nat.cast_add,Nat.cast_one] using h
        simpa only [mul_comm] using (div_lt_iff₀ hx0).mp h' |>.le
      · apply (le_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast (show 0 < n by omega))).mpr
        have h := Nat.floor_le (by positivity : 0 ≤ 12/x)
        simpa only [n,mul_comm] using (le_div_iff₀ hx0).mp h
  · have hn3 : n ≤ 3 := by omega
    have he : branchB n x = 0 := by
      interval_cases n <;>
        norm_num [branchB,branchMoment,powerPrefix,Finset.sum_range_succ] <;> ring
    rw [he]

/-- A rational interior subinterval supplies an explicit positive density. -/
theorem quadraticDensity_interior {x : ℝ} (hx : x ∈ Icc (9/4) (11/4)) :
    243/2048 ≤ quadraticDensity x := by
  have hx0 : 0 < x := by linarith [hx.1]
  let n := ⌊12/x⌋₊
  have h4 : 4 ≤ n := Nat.le_floor ((le_div_iff₀ hx0).mpr (by norm_num; linarith [hx.2]))
  have h5 : n ≤ 5 := by
    have hh : 12/x < 6 := (div_lt_iff₀ hx0).mpr (by linarith [hx.1])
    have h : (n : ℝ) < 6 := (Nat.floor_le (by positivity : 0 ≤ 12/x)).trans_lt hh
    have hn6 : n < 6 := by exact_mod_cast h
    omega
  have he : quadraticDensity x = x^2*(x-2)*(3-x)/8 := by
    rw [quadraticDensity_eq_branch hx0]
    change branchB n x = _
    interval_cases n <;> norm_num [branchB,branchMoment,powerPrefix,Finset.sum_range_succ] <;> ring
  rw [he]
  have hp : 3/16 ≤ (x-2)*(3-x) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)]
  have hx2 : 81/16 ≤ x^2 := by nlinarith [hx.1]
  have hm := mul_le_mul hx2 hp (by norm_num : (0 : ℝ) ≤ 3/16) (sq_nonneg x)
  nlinarith

private theorem interior_exp_lower {beta t : ℝ} (hb : 15/16 ≤ beta)
    (ht : Real.log (9/4) ≤ t) : 2 ≤ Real.exp (beta*t) := by
  have ha : 0 < Real.log (9/4) := Real.log_pos (by norm_num)
  have hb0 : 0 ≤ beta := by linarith
  have hp : (2 : ℝ)^16 < (9/4)^15 := by norm_num
  have hl := Real.log_lt_log (by positivity : (0 : ℝ) < 2^16) hp
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hba : (15/16)*Real.log (9/4) ≤ beta*t :=
    (mul_le_mul_of_nonneg_right hb ha.le).trans (mul_le_mul_of_nonneg_left ht hb0)
  have hbt : Real.log 2 ≤ beta*t := by linarith
  simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hbt

/-- A uniform rational lower bound for the actual real-exponent jet.
The proof pays only the small-x negative density and uses a positive
interior interval; it contains no floating coefficient evaluation. -/
theorem B_ofReal_re_lower {beta : ℝ} (hb : 15/16 ≤ beta) :
    1/2000 ≤ (B (beta : ℂ)).re := by
  have hb0 : 0 < beta := by linarith
  have hb2 : 0 < beta+2 := by linarith
  let a := Real.log (9/4)
  let b := Real.log (11/4)
  have ha : 0 < a := Real.log_pos (by norm_num)
  have hab : a ≤ b := Real.log_le_log (by norm_num) (by norm_num)
  let neg : ℝ → ℝ := (Iic 0).indicator (fun t => -(1/8)*Real.exp ((beta+2)*t))
  let pos : ℝ → ℝ := (Icc a b).indicator (fun _ => 243/1024)
  have hn : Integrable neg := (integrable_indicator_iff measurableSet_Iic).mpr
    ((integrableOn_exp_mul_Iic hb2 0).const_mul (-(1/8)))
  have hp : Integrable pos := (integrable_indicator_iff measurableSet_Icc).mpr
    (integrableOn_const (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hg : Integrable (fun t : ℝ => Real.exp (beta*t)*quadraticDensity (Real.exp t)) := by
    convert (integrable_B (s := (beta : ℂ)) (by simpa using hb0)).re using 1
    funext t
    change _ = Complex.re _
    simp [← Complex.ofReal_mul, ← Complex.ofReal_exp]
  have hi := integral_mono (hn.add hp) hg (show ∀ t : ℝ,
      neg t+pos t ≤ Real.exp (beta*t)*quadraticDensity (Real.exp t) from by
    intro t
    by_cases ht : t ≤ 0
    · have hnot : t ∉ Icc a b := by intro h; linarith [h.1]
      dsimp only [neg,pos]
      rw [indicator_of_mem (show t ∈ Iic (0 : ℝ) from ht),
        indicator_of_notMem hnot, add_zero]
      have hx1 : Real.exp t ≤ 1 := by simpa using Real.exp_le_exp.mpr ht
      have hh := mul_le_mul_of_nonneg_left
        (quadraticDensity_small_lower (Real.exp_pos t) hx1) (Real.exp_pos (beta*t)).le
      have he : Real.exp (beta*t)*(-Real.exp t^2/8) =
          -(1/8)*Real.exp ((beta+2)*t) := by
        calc
          _ = -(1/8)*(Real.exp (beta*t)*(Real.exp t)^2) := by ring
          _ = _ := by
            rw [← Real.exp_nat_mul, ← Real.exp_add]
            congr 2
            norm_num
            ring
      exact he ▸ hh
    · have hx1 : 1 ≤ Real.exp t := by
        simpa using Real.exp_le_exp.mpr (le_of_lt (lt_of_not_ge ht))
      have hnon := quadraticDensity_nonneg_of_one_le hx1
      dsimp only [neg,pos]
      rw [indicator_of_notMem (show t ∉ Iic (0 : ℝ) from ht), zero_add]
      by_cases hti : t ∈ Icc a b
      · rw [indicator_of_mem hti]
        have hx : Real.exp t ∈ Icc (9/4) (11/4) := by
          constructor
          · simpa only [a,Real.exp_log (by norm_num : (0 : ℝ) < 9/4)] using
              Real.exp_le_exp.mpr hti.1
          · simpa only [b,Real.exp_log (by norm_num : (0 : ℝ) < 11/4)] using
              Real.exp_le_exp.mpr hti.2
        have hh := mul_le_mul (interior_exp_lower hb hti.1)
          (quadraticDensity_interior hx) (by norm_num : (0 : ℝ) ≤ 243/2048)
            (Real.exp_pos (beta*t)).le
        norm_num at hh
        exact hh
      · rw [indicator_of_notMem hti]
        exact mul_nonneg (Real.exp_pos _).le hnon)
  have he : (∫ t, neg t+pos t) =
      (243/1024)*(b-a)-1/(8*(beta+2)) := by
    rw [integral_add hn hp]
    dsimp only [neg,pos]
    rw [integral_indicator measurableSet_Iic, integral_const_mul,
      integral_exp_mul_Iic hb2, integral_indicator measurableSet_Icc, setIntegral_const]
    simp only [mul_zero, Real.exp_zero, Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab), smul_eq_mul]
    field_simp [hb2.ne']
    ring
  have hl : 2/11 ≤ b-a := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 11/9)
    dsimp [a,b]
    rw [← Real.log_div (by norm_num : (11/4 : ℝ) ≠ 0)
      (by norm_num : (9/4 : ℝ) ≠ 0)]
    norm_num at h ⊢
    exact h
  have hneg : 1/(8*(beta+2)) ≤ 2/47 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8*(beta+2))).mpr
    nlinarith
  change (∫ t, neg t+pos t) ≤ _ at hi
  rw [he] at hi
  have hbRe : (B (beta : ℂ)).re =
      ∫ t : ℝ, Real.exp (beta*t)*quadraticDensity (Real.exp t) := by rw [B_ofReal]; rfl
  rw [hbRe]
  linarith

theorem B_ofReal_ne_zero {beta : ℝ} (hb : 15/16 ≤ beta) : B (beta : ℂ) ≠ 0 := by
  intro hz
  have h := B_ofReal_re_lower hb
  rw [hz,Complex.zero_re] at h
  norm_num at h

end
end RiemannGaussian.SuzukiCarryRealJet
