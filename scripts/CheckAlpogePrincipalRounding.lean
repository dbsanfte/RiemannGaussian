import CheckAlpogePrincipalLattice
import Formalism.SharpRestriction.AdmissibleParameterJoins.SumLogPrimeFactorsLe

/-! # The contribution of large residue primes to the division slope -/

namespace RiemannGaussian.AlpogeWindow
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.FrobeniusOrbits Classical

noncomputable def roundingAt {D : D7} (L : SizeData₂ D) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) : ℝ :=
  2 * SizeData₂.lwP w * Int.fract (DV.ur D w (L.sg u w))

private theorem rounding_nonneg {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) (w : D.what₂.places.Pl) :
    0 ≤ roundingAt L u w :=
  mul_nonneg (mul_nonneg (by norm_num) (J.logWeight_nonneg w)) (Int.fract_nonneg _)

/-- The signed floor errors all have the same sign, so the absolute slope error
is exactly the sum of the weighted fractional parts. -/
theorem slope_error_eq_rounding {D : D7} (L : SizeData₂ D) (u : D.what₂.Word)
    (hd : DV.NprimeDef D L) (hfg : (D.div.Nu u).L.FG) (hr : 0 < (D.div.Nu u).rank) :
    |(D.div.Nu u).mu - (L.NuH u).mu - ∑ w ∈ L.supp, SizeData₂.sz w (L.sg u w)| =
      ∑ w ∈ L.supp, roundingAt L u w := by
  rw [J.mu_diff D L hd u (D.div_good.2 u) hfg (J.ne_bot_of_rank_pos _ hr), ← Finset.sum_sub_distrib]
  have h : (∑ w ∈ L.supp, (2 * SizeData₂.lwP w * (⌊DV.ur D w (L.sg u w)⌋ : ℝ) -
      SizeData₂.sz w (L.sg u w))) = -(∑ w ∈ L.supp, roundingAt L u w) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold roundingAt Int.fract SizeData₂.sz DV.ur
    ring
  rw [h, abs_neg, abs_of_nonneg (Finset.sum_nonneg fun w _ => rounding_nonneg L u w)]

private theorem rounding_small_primes {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) :
    ∑ w ∈ L.supp.filter (fun w => ¬ L.sc.X'' D.R.n < (D.what₂.places.resChar w : ℝ)), roundingAt L u w ≤
      (2 * Real.log 4) * L.sc.X'' D.R.n := by
  let X := L.sc.X'' D.R.n
  let N := ⌊X⌋₊
  let S := L.supp.filter (fun w => ¬ X < (D.what₂.places.resChar w : ℝ))
  let P := (Finset.range (N + 1)).filter Nat.Prime
  have hm : ∀ w ∈ S, D.what₂.places.resChar w ∈ P := by
    intro w hw
    have hle := le_of_not_gt (Finset.mem_filter.mp hw).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hle)),
      D.what₂.places.resChar_prime w⟩
  have hX : 0 ≤ X := (one_pos.trans L.sc.one_lt_alt).le.trans (J.x_le_Xpp L.sc D.R)
  have hsum := (J.sum_lwP_le_primes D S P hm).trans (J.sum_log_primes_le N)
  change ∑ w ∈ S, roundingAt L u w ≤ (2 * Real.log 4) * X
  calc
    _ ≤ ∑ w ∈ S, 2 * SizeData₂.lwP w := Finset.sum_le_sum fun w _ =>
      mul_le_of_le_one_right (mul_nonneg (by norm_num) (J.logWeight_nonneg w)) (Int.fract_lt_one _).le
    _ = 2 * ∑ w ∈ S, SizeData₂.lwP w := (Finset.mul_sum ..).symm
    _ ≤ 2 * ((N : ℝ) * Real.log 4) := by linarith only [hsum]
    _ ≤ (2 * Real.log 4) * X := by
      have h := mul_le_mul_of_nonneg_right (Nat.floor_le hX) (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))
      dsimp [N] at *
      linarith only [h]

/-- Summing the level-prime correction over all lifts clears its denominator
four, since the number of lifts is even and the weight parameter is odd. -/
private theorem level_correction_integral (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) :
    ∃ z : ℕ, (z : ℝ) = (D.R.m : ℝ) * EatT D u w := by
  unfold EatT
  split
  · obtain ⟨a, ha⟩ := D.R.m_even
    obtain ⟨b, hb⟩ := D.R.t_odd
    refine ⟨D.R.m * (2 * ∑ τ, Wtau D u τ + D.R.f * D.R.N D.R.m) +
      (topsOf D.host D.eTau).card * (b + 1) * a * (D.R.m + 1), ?_⟩
    have hm : (D.R.m : ℝ) = a + a := by exact_mod_cast ha
    have ht : (D.R.t : ℝ) = 2 * b + 1 := by exact_mod_cast hb
    push_cast
    unfold Nm
    rw [hm, ht]
    ring
  · exact ⟨0, by simp⟩

private theorem rounding_eq_zero_above {ε : ℝ} (Fm : FamP ε) {x : ℝ} (hx : Fm.x1 < x)
    (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word) (w : (Fm.D x i).what₂.places.Pl)
    (hX : (Fm.L x i).sc.X'' (Fm.D x i).R.n < ((Fm.D x i).what₂.places.resChar w : ℝ))
    (hg : (Fm.D x i).what₂.places.resChar w ∉ ({(Fm.D x i).host.g 0, (Fm.D x i).host.g 1} : Finset ℕ))
    (hd : (Fm.D x i).what₂.places.resChar w ≠ (Fm.D x i).host.d) : roundingAt (Fm.L x i) u w = 0 := by
  let D := Fm.D x i
  let L := Fm.L x i
  let p := D.what₂.places.resChar w
  let e := if p = (D.mem u).A.T then EatT D u w else (padicValNat p (D.mem u).C.DGam : ℝ)
  change p ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) at hg
  have hv (j : ℕ) (hj : j ∈ SizeData₂.lifts D) : L.E u j w = e := by
    have h0 : p ≠ D.host.g 0 := fun h => hg (by simp [h])
    have h1 : p ≠ D.host.g 1 := fun h => hg (by simp [h])
    have h2 : D.host.cls p ≠ PrimeClass.ramD := fun h => hd (cls_ramD h)
    have h3 : ¬ ((IsResidueClassZero D p ∨ IsSg D p) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n) :=
      fun h => (not_le.mpr hX) h.2
    rw [(Fm.ex x hx i).err.edef u j hj w]
    dsimp only [p, D, L] at h0 h1 h2 h3
    simp only [Eval, e, p, D, if_neg h0, if_neg h1, if_neg h2, if_neg h3, add_zero]
  have hsg : L.sg u w = -(D.R.m : ℝ) * e := by
    unfold SizeData₂.sg
    calc
      _ = ∑ _j ∈ SizeData₂.lifts D, -e := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hgain : L.gain j w = 0 := by
          by_cases hs : w ∈ L.supp
          · by_cases hin : IsResidueClassZero D p ∨ IsSg D p
            · rw [((Fm.fills x hx i w).2.2.2.1 hs hin j hj)]
              unfold gainP
              rw [if_pos (Or.inr hX)]
            · exact (L.not_inert w (fun h => hin (Or.inr h)) (fun h => hin (Or.inl h))).1 j
          · exact L.gain_supp j w hs
        simp [SizeData₂.gainD, hgain, L.F_above j w hX hg hd, hv j hj]
      _ = _ := by simp [SizeData₂.lifts, nsmul_eq_mul]
  have he : ∃ z : ℕ, (z : ℝ) = (D.R.m : ℝ) * e := by
    dsimp only [e]
    split
    · exact level_correction_integral D u w
    · exact ⟨D.R.m * padicValNat p (D.mem u).C.DGam, by push_cast; rfl⟩
  obtain ⟨z, hz⟩ := he
  have hi : DV.ur D w (L.sg u w) = ((-((D.what₂.places.ramIdx w : ℤ) * z) : ℤ) : ℝ) := by
    unfold DV.ur
    push_cast
    rw [hsg, hz]
    ring
  change 2 * SizeData₂.lwP w * Int.fract (DV.ur D w (L.sg u w)) = 0
  rw [hi, Int.fract_intCast, mul_zero]

private theorem rounding_large_primes {ε : ℝ} (Fm : FamP ε) {x : ℝ} (hx : Fm.x1 < x)
    (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word) :
    let D := Fm.D x i
    let L := Fm.L x i
    ∑ w ∈ L.supp.filter (fun w => L.sc.X'' D.R.n < (D.what₂.places.resChar w : ℝ)), roundingAt L u w ≤
      6 * L.sc.X'' D.R.n := by
  let D := Fm.D x i
  let L := Fm.L x i
  let S := L.supp.filter (fun w => L.sc.X'' D.R.n < (D.what₂.places.resChar w : ℝ))
  let B := S.filter (fun w => roundingAt L u w ≠ 0)
  let P : Finset ℕ := {D.host.g 0} ∪ ({D.host.g 1} ∪ {D.host.d})
  have hm : ∀ w ∈ B, D.what₂.places.resChar w ∈ P := by
    intro w hw
    obtain ⟨hS, hn⟩ := Finset.mem_filter.mp hw
    by_contra h
    simp only [P, Finset.mem_union, Finset.mem_singleton, not_or] at h
    exact hn (rounding_eq_zero_above Fm hx i u w (Finset.mem_filter.mp hS).2 (by simpa using And.intro h.1 h.2.1) h.2.2)
  obtain ⟨_, _, _, _, _, _, hQD, _, _, _, _, _, _, _, _, _, _, _, _, _, hG, _⟩ := Fm.sizes x hx i
  have hsum : ∑ p ∈ P, Real.log (p : ℝ) ≤ 3 * L.sc.X'' D.R.n := by
    have h1 := J.sum_log_union_le {D.host.g 0} ({D.host.g 1} ∪ {D.host.d})
    have h2 := J.sum_log_union_le {D.host.g 1} {D.host.d}
    simp only [Finset.sum_singleton] at h1 h2
    change ∑ p ∈ ({D.host.g 0} ∪ ({D.host.g 1} ∪ {D.host.d}) : Finset ℕ), Real.log (p : ℝ) ≤ _
    linarith only [h1, h2, J.log_g_le (D := D) (L := L) hG 0, J.log_g_le (D := D) (L := L) hG 1,
      J.log_d_le (D := D) (L := L) hQD]
  have htotal := (J.sum_lwP_le_primes D B P hm).trans hsum
  change ∑ w ∈ S, roundingAt L u w ≤ _
  calc
    _ = ∑ w ∈ B, roundingAt L u w := (Finset.sum_filter_of_ne (fun w _ hn => hn)).symm
    _ ≤ ∑ w ∈ B, 2 * SizeData₂.lwP w := Finset.sum_le_sum fun w _ =>
      mul_le_of_le_one_right (mul_nonneg (by norm_num) (J.logWeight_nonneg w)) (Int.fract_lt_one _).le
    _ = 2 * ∑ w ∈ B, SizeData₂.lwP w := (Finset.mul_sum ..).symm
    _ ≤ _ := by linarith only [htotal]

/-- The slope comparison follows from positive division rank. The group-order
and level-prime sizes drop out of the rounding error on every comparison family. -/
theorem principal_family_linkMu {ε : ℝ} (Fm : FamP ε) (hr : J.MuRank Fm) : LinkMu Fm := by
  obtain ⟨a, ha⟩ := hr
  obtain ⟨b, hb⟩ := principal_family_nuFull Fm
  refine ⟨6 + 2 * Real.log 4, max (max a b) (Fm.x1 + 1), fun x hx i u => ?_⟩
  have hx' : Fm.x1 < x := by have := le_of_max_le_right hx; linarith
  let D := Fm.D x i
  let L := Fm.L x i
  rw [slope_error_eq_rounding L u (Fm.nprimeDef x hx' i) ((hb x (le_of_max_le_right (le_of_max_le_left hx)) i u).1)
    (ha x (le_of_max_le_left (le_of_max_le_left hx)) i u), add_mul]
  have hs := add_le_add (rounding_large_primes Fm hx' i u) (rounding_small_primes L u)
  exact (Finset.sum_filter_add_sum_filter_not L.supp
    (fun w => L.sc.X'' D.R.n < (D.what₂.places.resChar w : ℝ)) _).symm.le.trans hs

end RiemannGaussian.AlpogeWindow

open Lean Elab Command in
run_cmd do
  let decl := ``RiemannGaussian.AlpogeWindow.principal_family_linkMu
  let axs ← collectAxioms decl
  for ax in axs do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in {decl}"
  logInfo m!"{decl} depends on {axs}"
