import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LogDerivLocal
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LFunctionConj
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.CharFamilyLFunctionNeZeroOfOneLeRe
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.mellinGchiOfNeOne
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.mellinGchiModOne
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.measurableGchi
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.GchiGrowth
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.GchiConj

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem poleData_dslope {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    AnalyticAt ℂ (dslope f a) a := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨_, hp.has_fpower_series_dslope_fslope⟩

theorem poleData_abstract (g : ℂ → ℂ) (hg : Differentiable ℂ g) (h1 : g 1 ≠ 0) (k : ℂ) :
    ∃ Φ : ℂ → ℂ,
      (∀ s, s ≠ 1 → Φ s =
        -(deriv g s / g s - s * (deriv g 1 / g 1) + k * (1 - s)) / (s * (s - 1))) ∧
      (∀ ρ, ρ ≠ 0 → g ρ ≠ 0 → AnalyticAt ℂ Φ ρ) ∧
      (∀ ρ, ρ ≠ 0 → ∃ m : ℕ, (m = 0 ↔ g ρ ≠ 0) ∧ ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧
        ∀ᶠ s in 𝓝[≠] ρ, Φ s = (m : ℂ) * (-1 / (ρ * (ρ - 1))) / (s - ρ) + h s) ∧
      (∀ z, ∀ᶠ w in 𝓝[≠] z, g w ≠ 0) := by
  have hA : ∀ z, AnalyticAt ℂ g z := fun z => hg.analyticAt z
  have hnz : ∀ z, ¬ ∀ᶠ w in 𝓝 z, g w = 0 := by
    intro z hz
    have hon : AnalyticOnNhd ℂ g Set.univ := fun w _ => hA w
    have hzero := hon.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ z) hz
    exact h1 (hzero (Set.mem_univ 1))
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = deriv g 1 / g 1 := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℂ → ℂ, N = fun s => deriv g s / g s - s * c + k * (1 - s) := ⟨_, rfl⟩
  have hNs : ∀ s, N s = deriv g s / g s - s * c + k * (1 - s) := fun s => by rw [hN]
  have hN1 : N 1 = 0 := by rw [hNs, hc]; ring
  have hUo : IsOpen {s | g s ≠ 0} := isOpen_ne_fun hg.continuous continuous_const
  have hNd : DifferentiableOn ℂ N {s | g s ≠ 0} := by
    intro s hs
    have hd : DifferentiableAt ℂ (deriv g) s := (hA s).deriv.differentiableAt
    have hd2 : DifferentiableAt ℂ (fun s => deriv g s / g s - s * c + k * (1 - s)) s :=
      ((hd.div (hA s).differentiableAt hs).sub (differentiableAt_id.mul (differentiableAt_const c))).add
        ((differentiableAt_const k).mul ((differentiableAt_const 1).sub differentiableAt_id))
    rw [hN]
    exact hd2.differentiableWithinAt
  have hDd : DifferentiableOn ℂ (dslope N 1) {s | g s ≠ 0} :=
    (differentiableOn_dslope (hUo.mem_nhds h1)).mpr hNd
  have hPhi : ∀ s, s ≠ 1 → -(dslope N 1 s) / s =
      -(deriv g s / g s - s * (deriv g 1 / g 1) + k * (1 - s)) / (s * (s - 1)) := by
    intro s hs
    rw [dslope_of_ne _ hs, slope_def_field, hN1, hNs, ← hc]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hPan : ∀ ρ, ρ ≠ 0 → g ρ ≠ 0 → AnalyticAt ℂ (fun s => -(dslope N 1 s) / s) ρ := by
    intro ρ hρ hgρ
    exact (hDd.analyticAt (hUo.mem_nhds hgρ)).neg.div analyticAt_id hρ
  refine ⟨fun s => -(dslope N 1 s) / s, hPhi, hPan, ?_, ?_⟩
  · intro ρ hρ
    by_cases hgρ : g ρ = 0
    · have hρ1 : ρ ≠ 1 := fun h => h1 (h ▸ hgρ)
      obtain ⟨m, hm0, -, h0, hh0, hev⟩ := logDeriv_local (hA ρ) (hnz ρ)
      have hr : AnalyticAt ℂ (fun s : ℂ => 1 / (s * (s - 1))) ρ :=
        analyticAt_const.div (analyticAt_id.mul (analyticAt_id.sub analyticAt_const))
          (mul_ne_zero hρ (sub_ne_zero.mpr hρ1))
      have hq := poleData_dslope hr
      refine ⟨m, hm0, fun s => -((m : ℂ) * dslope (fun s : ℂ => 1 / (s * (s - 1))) ρ s)
          - (h0 s - s * c + k * (1 - s)) * (1 / (s * (s - 1))), ?_, ?_⟩
      · exact ((analyticAt_const.mul hq).neg).sub
          (((hh0.sub (analyticAt_id.mul analyticAt_const)).add
            (analyticAt_const.mul (analyticAt_const.sub analyticAt_id))).mul hr)
      · have hne0 : ∀ᶠ s in 𝓝[≠] ρ, s ≠ 0 :=
          nhdsWithin_le_nhds (isOpen_ne.mem_nhds hρ)
        have hne1 : ∀ᶠ s in 𝓝[≠] ρ, s ≠ 1 :=
          nhdsWithin_le_nhds (isOpen_ne.mem_nhds hρ1)
        have hneρ : ∀ᶠ s in 𝓝[≠] ρ, s ≠ ρ := self_mem_nhdsWithin
        filter_upwards [hev, hne0, hne1, hneρ] with s hs hs0 hs1 hsρ
        rw [hPhi s hs1, hs, dslope_of_ne _ hsρ, slope_def_field, ← hc]
        simp only [div_eq_mul_inv, mul_inv]
        ring
    · refine ⟨0, by simp [hgρ], fun s => -(dslope N 1 s) / s, hPan ρ hρ hgρ, ?_⟩
      exact Filter.Eventually.of_forall (fun s => by simp)
  · intro z
    rcases (hA z).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd h (hnz z)
    · exact h

theorem poleData_integrable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) (hs : 2 < s.re) :
    IntegrableOn (fun u : ℝ => Gchi χ (Real.exp u) * cexp (-s * u)) (Ioi 0) := by
  obtain ⟨C, hC⟩ := Gchi_growth χ
  have hb : 0 < s.re - 2 := by linarith
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hb).const_mul (max C 0)) ?_ ?_
  · exact (((measurable_Gchi χ).comp Real.measurable_exp).mul
      (by fun_prop : Measurable fun u : ℝ => cexp (-s * u))).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    have hu0 : (0:ℝ) < u := hu
    have he : ‖cexp (-s * u)‖ = Real.exp (-s.re * u) := by
      rw [Complex.norm_exp]
      simp
    rw [norm_mul, he]
    have hg := hC (Real.exp u) (Real.one_le_exp hu0.le)
    calc ‖Gchi χ (Real.exp u)‖ * Real.exp (-s.re * u)
        ≤ (max C 0 * Real.exp u ^ 2) * Real.exp (-s.re * u) := by
          gcongr
          exact hg.trans (by gcongr; exact le_max_left _ _)
      _ = max C 0 * Real.exp (-(s.re - 2) * u) := by
          rw [mul_assoc, sq, ← Real.exp_add, ← Real.exp_add]
          congr 2
          ring

theorem poleData_change (G : ℝ → ℂ) (s : ℂ) :
    ∫ u in Ioi (0 : ℝ), G (Real.exp u) * cexp (-s * u) =
      ∫ y in Ioi (1 : ℝ), G y * (y : ℂ) ^ (-s - 1) := by
  have himg : Real.exp '' Ioi 0 = Ioi 1 := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      show (1:ℝ) < Real.exp u
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.2 hu
    · intro hy
      have hy1 : (1:ℝ) < y := hy
      exact ⟨Real.log y, Real.log_pos hy1, Real.exp_log (by linarith)⟩
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
  rw [abs_of_pos (Real.exp_pos u), Complex.real_smul,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos u).ne'),
    ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp, Complex.ofReal_exp,
    mul_left_comm, ← Complex.exp_add]
  congr 2
  ring

theorem poleData_char {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (adm : N = 1 ∨ χ ≠ 1) :
    ∃ Φ : ℂ → ℂ,
      (∀ s : ℂ, 2 < s.re → Φ s = ∫ u in Ioi (0 : ℝ), Gchi χ (Real.exp u) * cexp (-s * u)) ∧
      (∀ ρ, ρ ≠ 0 → DirichletCharacter.LFunction χ ρ ≠ 0 → AnalyticAt ℂ Φ ρ) ∧
      (∀ ρ, ρ ≠ 0 → ∃ m : ℕ, (m = 0 ↔ DirichletCharacter.LFunction χ ρ ≠ 0) ∧
        ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧
        ∀ᶠ s in 𝓝[≠] ρ, Φ s = (m : ℂ) * (-1 / (ρ * (ρ - 1))) / (s - ρ) + h s) ∧
      (∀ z, ∀ᶠ w in 𝓝[≠] z, DirichletCharacter.LFunction χ w ≠ 0) := by
  by_cases hχ : χ = 1
  · have hN : N = 1 := adm.resolve_right (fun h => h hχ)
    subst hN
    simp only [DirichletCharacter.LFunction_modOne_eq]
    set g : ℂ → ℂ := Function.update (fun s => (s - 1) * riemannZeta s) 1 1 with hg_def
    have hg_ne : ∀ w : ℂ, w ≠ 1 → g w = (w - 1) * riemannZeta w := by
      intro w hw
      simp [g, Function.update_apply, hw]
    have hg1 : g 1 = 1 := by simp [g]
    have hg : Differentiable ℂ g := by
      rw [← differentiableOn_univ,
        ← differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem]
      refine ⟨?_, ?_⟩
      · intro z hz
        have hz1 : z ≠ 1 := by simpa using hz
        apply DifferentiableAt.differentiableWithinAt
        have hev : g =ᶠ[𝓝 z] fun s => (s - 1) * riemannZeta s := by
          filter_upwards [isOpen_compl_singleton.mem_nhds hz1] with w hw
          exact hg_ne w hw
        have hd : DifferentiableAt ℂ (fun s => (s - 1) * riemannZeta s) z :=
          DifferentiableAt.mul (by fun_prop) (differentiableAt_riemannZeta hz1)
        exact hd.congr_of_eventuallyEq hev
      · simpa only [g, continuousAt_update_same] using riemannZeta_residue_one
    have hderiv1 : deriv g 1 = Real.eulerMascheroniConstant := by
      have hd : HasDerivAt g (deriv g 1) 1 := (hg 1).hasDerivAt
      rw [hasDerivAt_iff_tendsto_slope] at hd
      refine tendsto_nhds_unique hd (tendsto_riemannZeta_sub_one_div.congr' ?_)
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs1 : s ≠ 1 := hs
      have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      rw [slope_def_field, hg_ne s hs1, hg1]
      field_simp
    have hderiv : ∀ s : ℂ, s ≠ 1 →
        deriv g s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
      intro s hs1
      have hev : g =ᶠ[𝓝 s] fun s => (s - 1) * riemannZeta s := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with w hw
        exact hg_ne w hw
      rw [hev.deriv_eq]
      have h1 : HasDerivAt (fun s : ℂ => s - 1) 1 s := (hasDerivAt_id s).sub_const 1
      have h2 : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
        (differentiableAt_riemannZeta hs1).hasDerivAt
      have h3 : HasDerivAt (fun s : ℂ => (s - 1) * riemannZeta s)
          (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s := h1.mul h2
      rw [h3.deriv]
      ring
    have hgz : ∀ w : ℂ, g w ≠ 0 ↔ riemannZeta w ≠ 0 := by
      intro w
      by_cases hw : w = 1
      · subst hw
        rw [hg1]
        exact ⟨fun _ => riemannZeta_one_ne_zero, fun _ => one_ne_zero⟩
      · rw [hg_ne w hw]
        have hw' : w - 1 ≠ 0 := sub_ne_zero.mpr hw
        constructor
        · intro h hz
          exact h (by rw [hz, mul_zero])
        · intro h
          exact mul_ne_zero hw' h
    obtain ⟨Φ, h1, h2, h3, h4⟩ := poleData_abstract g hg (by rw [hg1]; exact one_ne_zero) 1
    refine ⟨Φ, ?_, ?_, ?_, ?_⟩
    · intro s hs
      have hs1 : s ≠ 1 := by
        intro h
        rw [h] at hs
        norm_num at hs
      have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      have hs0 : s ≠ 0 := by
        intro h
        rw [h] at hs
        norm_num at hs
      have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by linarith)
      rw [h1 s hs1, poleData_change, mellin_Gchi_modOne χ s (by linarith), hderiv s hs1,
        hg_ne s hs1, hderiv1, hg1]
      congr 1
      field_simp
      ring
    · intro ρ hρ hL
      exact h2 ρ hρ ((hgz ρ).mpr hL)
    · intro ρ hρ
      obtain ⟨m, hm, rest⟩ := h3 ρ hρ
      exact ⟨m, hm.trans (hgz ρ), rest⟩
    · intro z
      filter_upwards [h4 z] with w hw
      exact (hgz w).mp hw
  · obtain ⟨Φ, h1, h2, h3, h4⟩ := poleData_abstract (DirichletCharacter.LFunction χ)
      (DirichletCharacter.differentiable_LFunction hχ)
      (DirichletCharacter.LFunction_apply_one_ne_zero hχ) 0
    refine ⟨Φ, ?_, h2, h3, h4⟩
    intro s hs
    have hs1 : s ≠ 1 := by
      intro h
      rw [h] at hs
      norm_num at hs
    rw [h1 s hs1, poleData_change, mellin_Gchi_of_ne_one χ hχ s (by linarith), zero_mul, add_zero]

theorem poleData_inv_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (ρ : ℂ) :
    DirichletCharacter.LFunction χ⁻¹ ρ = 0 ↔
      DirichletCharacter.LFunction χ ((starRingEnd ℂ) ρ) = 0 := by
  have := LFunction_conj χ ((starRingEnd ℂ) ρ)
  rw [Complex.conj_conj] at this
  rw [this, map_eq_zero]

theorem poleData (F : CharFamily) : ∃ Φ : ℂ → ℂ, PoleData (gm F) Φ (zeroSet F) := by
  classical
  have adm' : ∀ i, F.N i = 1 ∨ (F.χ i)⁻¹ ≠ 1 := fun i => (F.adm i).imp id (fun h => inv_ne_one.mpr h)
  choose Φ1 hΦ1int hΦ1an hΦ1pol hΦ1iso using fun i => poleData_char (F.χ i) (F.adm i)
  choose Φ2 hΦ2int hΦ2an hΦ2pol hΦ2iso using fun i => poleData_char (F.χ i)⁻¹ (adm' i)
  choose C hC using fun i => Gchi_growth (F.χ i)
  have hZ : ∀ ρ, ρ ∈ zeroSet F ↔ 0 < ρ.re ∧ ∃ i, DirichletCharacter.LFunction (F.χ i) ρ = 0 ∨
      DirichletCharacter.LFunction (F.χ i) ((starRingEnd ℂ) ρ) = 0 := by
    intro ρ
    rw [zeroSet.eq_1]
    rfl
  have hconj : ∀ i (w : ℂ), DirichletCharacter.LFunction (F.χ i) ((starRingEnd ℂ) w) = 0 ↔
      DirichletCharacter.LFunction (F.χ i)⁻¹ w = 0 := fun i w => (poleData_inv_zero (F.χ i) w).symm
  refine ⟨fun s => ∑ i, (F.a i : ℂ) / 2 * (Φ1 i s + Φ2 i s), ?_⟩
  refine PoleData.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have hg : gm F = fun u => ∑ i, F.a i * (Gchi (F.χ i) (Real.exp u)).re := by
      funext u
      rw [gm.eq_1, Gm.eq_1]
    rw [hg]
    exact Finset.measurable_sum _ fun i _ => measurable_const.mul
      (Complex.measurable_re.comp ((measurable_Gchi (F.χ i)).comp Real.measurable_exp))
  · refine ⟨∑ i, F.a i * C i, fun u hu => ?_⟩
    rw [gm.eq_1, Gm.eq_1]
    have hy : 1 ≤ Real.exp u := Real.one_le_exp hu
    have he : Real.exp u ^ 2 = Real.exp (2 * u) := by
      rw [sq, ← Real.exp_add, two_mul]
    calc |∑ i, F.a i * (Gchi (F.χ i) (Real.exp u)).re|
        ≤ ∑ i, |F.a i * (Gchi (F.χ i) (Real.exp u)).re| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, F.a i * (C i * Real.exp (2 * u)) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_pos (F.a_pos i)]
        apply mul_le_mul_of_nonneg_left _ (F.a_pos i).le
        calc |(Gchi (F.χ i) (Real.exp u)).re| ≤ ‖Gchi (F.χ i) (Real.exp u)‖ := Complex.abs_re_le_norm _
          _ ≤ C i * Real.exp u ^ 2 := hC i _ hy
          _ = C i * Real.exp (2 * u) := by rw [he]
      _ = (∑ i, F.a i * C i) * Real.exp (2 * u) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
  · intro s hs
    have hpt : ∀ u : ℝ, ((gm F u : ℝ) : ℂ) * cexp (-s * u) = ∑ i, (F.a i : ℂ) / 2 *
        (Gchi (F.χ i) (Real.exp u) * cexp (-s * u) + Gchi (F.χ i)⁻¹ (Real.exp u) * cexp (-s * u)) := by
      intro u
      rw [gm.eq_1, Gm.eq_1]
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.re_eq_add_conj, Gchi_conj]
      ring
    simp_rw [hpt]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul, integral_add (poleData_integrable _ s hs) (poleData_integrable _ s hs),
        hΦ1int i s hs, hΦ2int i s hs]
    · intro i _
      exact ((poleData_integrable _ s hs).add (poleData_integrable _ s hs)).const_mul _
  · intro ρ hρ
    exact ((hZ ρ).1 hρ).1
  · intro s hs
    obtain ⟨hsre, hsZ⟩ := hs
    have hsre' : 0 < s.re := hsre
    have hs0 : s ≠ 0 := fun h => by rw [h] at hsre'; simp at hsre'
    have hL : ∀ i, DirichletCharacter.LFunction (F.χ i) s ≠ 0 ∧
        DirichletCharacter.LFunction (F.χ i)⁻¹ s ≠ 0 := by
      intro i
      constructor
      · intro h
        exact hsZ ((hZ s).2 ⟨hsre', i, Or.inl h⟩)
      · intro h
        exact hsZ ((hZ s).2 ⟨hsre', i, Or.inr ((hconj i s).2 h)⟩)
    apply DifferentiableAt.differentiableWithinAt
    have han : AnalyticAt ℂ (fun s => ∑ i, (F.a i : ℂ) / 2 * (Φ1 i s + Φ2 i s)) s := by
      apply Finset.analyticAt_fun_sum
      intro i _
      exact analyticAt_const.mul ((hΦ1an i s hs0 (hL i).1).add (hΦ2an i s hs0 (hL i).2))
    exact han.differentiableAt
  · intro z _
    have hall : ∀ᶠ w in 𝓝[≠] z, ∀ i, DirichletCharacter.LFunction (F.χ i) w ≠ 0 ∧
        DirichletCharacter.LFunction (F.χ i)⁻¹ w ≠ 0 := by
      rw [Filter.eventually_all]
      intro i
      exact (hΦ1iso i z).and (hΦ2iso i z)
    filter_upwards [hall] with w hw hwZ
    obtain ⟨_, i, hi⟩ := (hZ w).1 hwZ
    rcases hi with hi | hi
    · exact (hw i).1 hi
    · exact (hw i).2 ((hconj i w).1 hi)
  · intro ρ hρ
    obtain ⟨hρre, i0, hi0⟩ := (hZ ρ).1 hρ
    have hρ0 : ρ ≠ 0 := fun h => by rw [h] at hρre; simp at hρre
    have hρ1 : ρ ≠ 1 := by
      intro h
      rcases hi0 with h' | h'
      · exact charFamily_LFunction_ne_zero_of_one_le_re F i0 ρ (by rw [h]; simp) h'
      · exact charFamily_LFunction_ne_zero_of_one_le_re F i0 _ (by rw [h]; simp) h'
    choose m1 hm1 h1 hh1an hh1ev using fun i => hΦ1pol i ρ hρ0
    choose m2 hm2 h2 hh2an hh2ev using fun i => hΦ2pol i ρ hρ0
    obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ i, F.a i / 2 * ((m1 i : ℝ) + m2 i) := ⟨_, rfl⟩
    have hS0 : 0 < S := by
      have hpos : 0 < F.a i0 / 2 * ((m1 i0 : ℝ) + m2 i0) := by
        apply mul_pos (by linarith [F.a_pos i0])
        have hm1n : (0:ℝ) ≤ m1 i0 := Nat.cast_nonneg _
        have hm2n : (0:ℝ) ≤ m2 i0 := Nat.cast_nonneg _
        rcases hi0 with h | h
        · have hne : m1 i0 ≠ 0 := fun hm => ((hm1 i0).1 hm) h
          have : (1:ℝ) ≤ m1 i0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
          linarith
        · have hne : m2 i0 ≠ 0 := fun hm => ((hm2 i0).1 hm) ((hconj i0 ρ).1 h)
          have : (1:ℝ) ≤ m2 i0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
          linarith
      rw [hS]
      calc 0 < F.a i0 / 2 * ((m1 i0 : ℝ) + m2 i0) := hpos
        _ ≤ ∑ i, F.a i / 2 * ((m1 i : ℝ) + m2 i) :=
          Finset.single_le_sum (f := fun i => F.a i / 2 * ((m1 i : ℝ) + m2 i))
            (fun i _ => by have := F.a_pos i; positivity) (Finset.mem_univ i0)
    refine ⟨(S : ℂ) * (-1 / (ρ * (ρ - 1))), ?_, ?_, ?_⟩
    · have hr0 : (-1 / (ρ * (ρ - 1)) : ℂ) ≠ 0 :=
        div_ne_zero (by norm_num) (mul_ne_zero hρ0 (sub_ne_zero.mpr hρ1))
      exact mul_ne_zero (by exact_mod_cast hS0.ne') hr0
    · intro him
      have hρx : ρ = (ρ.re : ℂ) := by
        apply Complex.ext <;> simp [him]
      have hlt : ρ.re < 1 := by
        by_contra hge
        push_neg at hge
        rcases hi0 with h' | h'
        · exact charFamily_LFunction_ne_zero_of_one_le_re F i0 ρ hge h'
        · exact charFamily_LFunction_ne_zero_of_one_le_re F i0 _ (by simpa using hge) h'
      have hc : (S : ℂ) * (-1 / (ρ * (ρ - 1))) = ((S * (-1 / (ρ.re * (ρ.re - 1))) : ℝ) : ℂ) := by
        push_cast
        rw [← hρx]
      rw [hc, Complex.ofReal_re, Complex.ofReal_im]
      refine ⟨?_, rfl⟩
      have hneg : ρ.re * (ρ.re - 1) < 0 := mul_neg_of_pos_of_neg hρre (by linarith)
      exact mul_pos hS0 (div_pos_of_neg_of_neg (by norm_num) hneg)
    · refine ⟨fun s => ∑ i, (F.a i : ℂ) / 2 * (h1 i s + h2 i s), ?_, ?_⟩
      · apply Finset.analyticAt_fun_sum
        intro i _
        exact analyticAt_const.mul ((hh1an i).add (hh2an i))
      · have hev : ∀ᶠ s in 𝓝[≠] ρ, ∀ i,
            Φ1 i s = (m1 i : ℂ) * (-1 / (ρ * (ρ - 1))) / (s - ρ) + h1 i s ∧
            Φ2 i s = (m2 i : ℂ) * (-1 / (ρ * (ρ - 1))) / (s - ρ) + h2 i s := by
          rw [Filter.eventually_all]
          intro i
          exact (hh1ev i).and (hh2ev i)
        filter_upwards [hev] with s hs
        rw [hS]
        push_cast
        rw [Finset.sum_mul, Finset.sum_div, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [(hs i).1, (hs i).2]
        ring

end Deduction

end
