import Formalism.ZetaNonvanishing.MeasurableGchi

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

lemma riemannZetaOne_eq_mul_of_ne_one {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [riemannZeta_eq_inv_sub_mul hs]
  field_simp

lemma riemannZetaOne_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta₁ s ≠ 0 := by
  by_cases h1 : s = 1
  · subst h1; simp
  · rw [riemannZetaOne_eq_mul_of_ne_one h1]
    exact mul_ne_zero (sub_ne_zero.mpr h1) (riemannZeta_ne_zero_of_one_le_re hs)

lemma ofReal_ne_one_of_lt {σ : ℝ} (h : σ < 1) : (σ : ℂ) ≠ 1 := by
  intro h'
  have := congrArg Complex.re h'
  simp at this
  linarith

lemma riemannZetaOne_ne_zero_of_real_mem_Ioo (h8 : ZetaRealNonvanish) {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta₁ σ ≠ 0 := by
  rw [riemannZetaOne_eq_mul_of_ne_one (ofReal_ne_one_of_lt h1)]
  exact mul_ne_zero (sub_ne_zero.mpr (ofReal_ne_one_of_lt h1)) (h8 σ h0 h1)

lemma deriv_riemannZetaOne_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    deriv riemannZeta₁ s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
  have heq : riemannZeta₁ =ᶠ[𝓝 s] fun z => (z - 1) * riemannZeta z := by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz
    exact riemannZetaOne_eq_mul_of_ne_one hz
  rw [heq.deriv_eq]
  have h : HasDerivAt (fun z => (z - 1) * riemannZeta z)
      (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s :=
    ((hasDerivAt_id s).sub_const 1).mul (differentiableAt_riemannZeta hs).hasDerivAt
  rw [h.deriv]
  ring

lemma logderiv_zeta_eq {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    -deriv riemannZeta s / riemannZeta s =
      -(deriv riemannZeta₁ s / riemannZeta₁ s) + 1 / (s - 1) := by
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [deriv_riemannZetaOne_of_ne_one hs, riemannZetaOne_eq_mul_of_ne_one hs]
  field_simp
  ring

section Fam

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
  (χ : (i : ι) → DirichletCharacter ℂ (N i)) (w : ι → ℝ)

def ccOC (i : ι) : ℂ :=
  deriv (DirichletCharacter.LFunction (χ i)) 1 / DirichletCharacter.LFunction (χ i) 1

def linOC (i : ι) (s : ℂ) : ℂ := -1 + (1 + (Real.eulerMascheroniConstant : ℂ) - ccOC χ i) * s

def EOC (s : ℂ) : ℂ := riemannZeta₁ s * ∏ j, DirichletCharacter.LFunction (χ j) s

def nOC (i : ι) (s : ℂ) : ℂ :=
  -(deriv riemannZeta₁ s / riemannZeta₁ s)
    + deriv (DirichletCharacter.LFunction (χ i)) s / DirichletCharacter.LFunction (χ i) s
    + linOC χ i s

def aOC (i : ι) (s : ℂ) : ℂ :=
  -deriv riemannZeta₁ s * ∏ j, DirichletCharacter.LFunction (χ j) s
    + riemannZeta₁ s * deriv (DirichletCharacter.LFunction (χ i)) s
        * ∏ j ∈ Finset.univ.erase i, DirichletCharacter.LFunction (χ j) s
    + linOC χ i s * EOC χ s

def AOC (s : ℂ) : ℂ := ∑ i, (w i : ℂ) * aOC χ i s

def HOC (ε C θ : ℝ) (x : ℝ) : ℝ := ε * ∑ i, w i * (Gz x - Gchi (χ i) x) + C * x ^ θ

def IOC (ε C θ : ℝ) (s : ℂ) : ℂ :=
  ∫ x in Ioi (1:ℝ), ((HOC χ w ε C θ x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)

def PhiOC (ε C θ : ℝ) (s : ℂ) : ℂ :=
  ε * dslope (AOC χ w) 1 s / (s * EOC χ s) + C / (s - θ)

lemma differentiable_deriv_of {f : ℂ → ℂ} (hf : Differentiable ℂ f) : Differentiable ℂ (deriv f) :=
  fun z => ((analyticOnNhd_univ_iff_differentiable.mpr hf).deriv z trivial).differentiableAt

end Fam

end Formalism
