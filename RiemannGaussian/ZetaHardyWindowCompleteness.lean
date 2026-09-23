/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaHardyPhase
import RiemannGaussian.ZetaZeroCountCompleteness

/-!
# Complete finite RH verification from ordered Hardy sign windows

Each disjoint positive sign-change interval supplies a distinct actual
critical-line zero. Its conjugate supplies the negative ordinate. Matching
these zeros with an independently proved total multiplicity count excludes
every unseen zero, without any simplicity assumption on unseen roots.
-/

namespace RiemannGaussian.ZetaHardyWindowCompleteness
noncomputable section
open ZetaHardyPhase

/-- Opposite actual Hardy signs give a critical-line zero inside the open
interval, with either orientation of the sign change. -/
theorem exists_zero_of_mul_neg {a b : ℝ} (hab : a ≤ b) (hs : hardy a * hardy b < 0) :
    ∃ t ∈ Set.Ioo a b, riemannZeta (point t) = 0 := by
  rcases mul_neg_iff.mp hs with hs | hs
  · obtain ⟨t, ht, hz⟩ := intermediate_value_Ioo' hab continuous_hardy.continuousOn hs.symm
    exact ⟨t, ht, (hardy_eq_zero_iff t).mp hz⟩
  · obtain ⟨t, ht, hz⟩ := intermediate_value_Ioo hab continuous_hardy.continuousOn hs
    exact ⟨t, ht, (hardy_eq_zero_iff t).mp hz⟩

/-- Verified ordered positive sign windows and a matching complete upper
count prove RH through the stated height. The signs and the total count
are separate obligations; no numerical zero list is presumed. -/
theorem critical_line_of_sign_windows {H : ℝ} (hH : 0 ≤ H) {n : ℕ}
    (a b : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i ≤ b i)
    (hb : ∀ i, b i ≤ H) (hsep : ∀ i j, i < j → b i ≤ a j)
    (hs : ∀ i, hardy (a i) * hardy (b i) < 0)
    (hc : ZetaFiniteZeroCount.count H ≤ 2 * n)
    (ρ : NontrivialZetaZero) (hρ : |ρ.1.im| ≤ H) : ρ.1.re = 1 / 2 := by
  classical
  choose t ht hz using fun i => exists_zero_of_mul_neg (hab i) (hs i)
  have htpos (i) : 0 < t i := (ha i).trans (ht i).1
  have htmono : StrictMono t := fun i j hij =>
    ((ht i).2.trans_le (hsep i j hij)).trans (ht j).1
  have hn (i) : IsNontrivialZetaZero (point (t i)) := by
    refine ⟨hz i, ?_, ?_⟩
    · rintro ⟨k, he⟩
      have hh := congrArg Complex.im he
      norm_num [point] at hh
      linarith [htpos i]
    · intro he
      have hh := congrArg Complex.im he
      norm_num [point] at hh
      linarith [htpos i]
  let z (i : Fin n) : NontrivialZetaZero := ⟨point (t i), hn i⟩
  let f (i : Fin n × Bool) : NontrivialZetaZero :=
    if i.2 then z i.1 else NontrivialZetaZero.conjugate (z i.1)
  have him (i : Fin n × Bool) : (f i).1.im = if i.2 then t i.1 else -t i.1 := by
    cases i with | mk i c => cases c <;> simp [f, z, point]
  have hre (i : Fin n × Bool) : (f i).1.re = 1 / 2 := by
    cases i with | mk i c => cases c <;> simp [f, z, point]
  have hf : Function.Injective f := by
    rintro ⟨i, c⟩ ⟨j, d⟩ he
    have hh := congrArg (fun τ : NontrivialZetaZero => τ.1.im) he
    rw [him, him] at hh
    cases c <;> cases d <;> simp only [Bool.false_eq_true, ↓reduceIte] at hh
    · exact Prod.ext (htmono.injective (by linarith)) rfl
    · linarith [htpos i, htpos j]
    · linarith [htpos i, htpos j]
    · exact Prod.ext (htmono.injective hh) rfl
  apply ZetaZeroCountCompleteness.critical_line_of_count_le_card hH
    (Finset.univ.image f) ?_ ?_ ?_ ρ hρ
  · intro τ hτ
    obtain ⟨⟨i, c⟩, _, rfl⟩ := Finset.mem_image.mp hτ
    rw [him]
    cases c <;> simp only [Bool.false_eq_true, ↓reduceIte, abs_neg]
    all_goals rw [abs_of_pos (htpos i)]; exact (ht i).2.le.trans (hb i)
  · simpa only [Finset.card_image_of_injective _ hf, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.mul_comm n 2] using hc
  · intro τ hτ
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hτ
    exact hre i

end
end RiemannGaussian.ZetaHardyWindowCompleteness
