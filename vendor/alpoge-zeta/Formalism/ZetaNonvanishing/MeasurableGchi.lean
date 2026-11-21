import Formalism.DefsOC
import Formalism.ZetaNonvanishing.Assembly

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

open ArithmeticFunction

lemma Sz_eq_Sa : Sz = Sa (fun n => Λ n) := rfl

lemma Schi_eq_Sa {N : ℕ} (χ : DirichletCharacter ℂ N) :
    Schi χ = Sa (fun n => Λ n * (χ n).re) := rfl

lemma vM_bound : ∀ n : ℕ, |(Λ n : ℝ)| ≤ 1 * Λ n := fun n => by
  rw [one_mul, abs_of_nonneg vonMangoldt_nonneg]

lemma twist_bound {N : ℕ} (χ : DirichletCharacter ℂ N) :
    ∀ n : ℕ, |Λ n * (χ n).re| ≤ 1 * Λ n := fun n => by
  rw [one_mul, abs_mul, abs_of_nonneg vonMangoldt_nonneg]
  have h1 : |(χ n).re| ≤ 1 := (Complex.abs_re_le_norm _).trans (DirichletCharacter.norm_le_one χ _)
  exact mul_le_of_le_one_right vonMangoldt_nonneg h1

lemma measurable_Gz (h3 : MellinSgen) : Measurable Gz := by
  have := (h3 _ 1 vM_bound).1
  unfold Gz
  rw [Sz_eq_Sa]
  fun_prop

lemma measurable_Gchi (h3 : MellinSgen) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    Measurable (Gchi χ) := by
  have := (h3 _ 1 (twist_bound χ)).1
  unfold Gchi
  rw [Schi_eq_Sa]
  fun_prop

lemma rint_Gz (h3 : MellinSgen) (h5 : MellinElem) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun x : ℝ => Gz x * x ^ (-σ - 1)) (Ioi 1) := by
  have hS := h3 _ 1 vM_bound
  have a1 := rint_of_abs _ hS.1 σ (hS.2.1 σ hσ)
  have a2 := rint_of_abs (fun x => x * Real.log x) (by fun_prop) σ (h5.2.1 σ hσ)
  have a3 := h5.1 1 σ hσ
  have hfun : (fun x : ℝ => Gz x * x ^ (-σ - 1)) = fun x =>
      (Sa (fun n => Λ n) x * x ^ (-σ - 1) - (x * Real.log x) * x ^ (-σ - 1))
        + (1 + Real.eulerMascheroniConstant) * (x ^ (1:ℝ) * x ^ (-σ - 1)) := by
    funext x
    simp only [Gz, Sz_eq_Sa, Real.rpow_one]
    ring
  rw [hfun]
  exact Integrable.add (Integrable.sub a1 a2) (Integrable.const_mul a3 _)

lemma rint_Gchi (h3 : MellinSgen) (h5 : MellinElem) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun x : ℝ => Gchi χ x * x ^ (-σ - 1)) (Ioi 1) := by
  have hS := h3 _ 1 (twist_bound χ)
  have a1 := rint_of_abs _ hS.1 σ (hS.2.1 σ hσ)
  have a3 := h5.1 1 σ hσ
  have hfun : (fun x : ℝ => Gchi χ x * x ^ (-σ - 1)) = fun x =>
      Sa (fun n => Λ n * (χ n).re) x * x ^ (-σ - 1)
        + (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re
          * (x ^ (1:ℝ) * x ^ (-σ - 1)) := by
    funext x
    simp only [Gchi, Schi_eq_Sa, Real.rpow_one]
    ring
  rw [hfun]
  exact Integrable.add a1 (Integrable.const_mul a3 _)

lemma mellin_Gz (h3 : MellinSgen) (h5 : MellinElem) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (Gz x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) ∧
    ∫ x in Ioi (1:ℝ), (Gz x : ℂ) * (x : ℂ) ^ (-s - 1) =
      (-deriv riemannZeta s / riemannZeta s) / (s * (s - 1)) - 1 / (s - 1) ^ 2
        + (1 + (Real.eulerMascheroniConstant : ℂ)) * (1 / (s - 1)) := by
  have hS := h3 _ 1 vM_bound
  have i1 : IntegrableOn (fun x : ℝ => (Sa (fun n => Λ n) x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ hS.1 s (hS.2.1 _ hs)
  have i2 := cint_of_abs (fun x => x * Real.log x) (by fun_prop) s (h5.2.1 _ hs)
  have i3 : IntegrableOn (fun x : ℝ => ((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ (by fun_prop) s (int_abs_rpow h5 (by linarith))
  have hfun : (fun x : ℝ => (Gz x : ℂ) * (x : ℂ) ^ (-s - 1)) = fun x =>
      ((Sa (fun n => Λ n) x : ℂ) * (x : ℂ) ^ (-s - 1)
        - ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
        + ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ) *
          (((x ^ (1:ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) := by
    funext x
    simp only [Gz, Sz_eq_Sa, Real.rpow_one]
    push_cast
    ring
  have j12 : IntegrableOn (fun x : ℝ => (Sa (fun n => Λ n) x : ℂ) * (x : ℂ) ^ (-s - 1)
        - ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) := Integrable.sub i1 i2
  have j3 := Integrable.const_mul i3 ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ)
  refine ⟨by rw [hfun]; exact j12.add j3, ?_⟩
  rw [hfun, integral_add j12 j3, integral_sub i1 i2, integral_const_mul, hS.2.2 s hs,
    h5.2.2.2 s hs, h5.2.2.1 1 s (by simpa using hs)]
  have hL : LSeries (fun n => ((Λ n : ℝ) : ℂ)) s = -deriv riemannZeta s / riemannZeta s :=
    LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  rw [hL]
  push_cast
  ring

end Formalism
