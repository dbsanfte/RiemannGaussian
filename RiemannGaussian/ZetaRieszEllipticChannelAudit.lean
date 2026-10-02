/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic

/-!
# The principal channel left open by direct elliptic trace projection

The complete Legendre-family cubic character sum includes the two
degenerate fibers. Every translated trace has zero mean. Its correlations
are unchanged by adding a constant to the original residue population.
Consequently, no bound on these correlations alone implies a one-sided
bound on the original signed sum.

This is a go/no-go audit of DIRECT trace projection, not a no-go for
algebraic-geometric correlation estimates derived from another exact
arithmetic identity. It neither changes the Riesz carrier nor estimates its
actual principal channel. No Hasse bound or prime-count theorem is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszEllipticChannelAudit

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Cubic character-sum continuation of the Legendre elliptic family.
Both singular parameters zero and one remain in the complete field sum. -/
def familyTrace (v : F) : ℂ :=
  -(∑ x : F, (quadraticChar F (x*(x-1)*(x-v)) : ℂ))

private theorem character_sub_sum_zero (hF : ringChar F ≠ 2) (x : F) :
    (∑ v : F, (quadraticChar F (x-v) : ℂ))=0 := by
  have hb : Function.Bijective (fun v : F => x-v) := by
    constructor
    · intro v w h
      have he := congrArg (fun z : F => x-z) h
      simpa only [sub_sub_cancel] using he
    · intro v
      exact ⟨x-v,by ring⟩
  calc
    _ = ∑ v : F, (quadraticChar F v : ℂ) :=
      hb.sum_comp (fun v : F => (quadraticChar F v : ℂ))
    _ = 0 := by exact_mod_cast quadraticChar_sum_zero hF

/-- Exact zero mean, before any estimate or normalization. -/
theorem familyTrace_sum_zero (hF : ringChar F ≠ 2) :
    (∑ v : F, familyTrace v)=0 := by
  calc
    _ = -(∑ x : F, (quadraticChar F (x*(x-1)) : ℂ)*
        (∑ v : F, (quadraticChar F (x-v) : ℂ))) := by
      unfold familyTrace
      rw [Finset.sum_neg_distrib,Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      simp only [map_mul,Int.cast_mul,Finset.mul_sum]
    _ = 0 := by simp only [character_sub_sum_zero hF,mul_zero,Finset.sum_const_zero,neg_zero]

/-- An arbitrary translation of the trace has the same exact zero mean. -/
theorem familyTrace_shift_sum_zero (hF : ringChar F ≠ 2) (h : F) :
    (∑ v : F, familyTrace (v-h))=0 := by
  have hb : Function.Bijective (fun v : F => v-h) := by
    constructor
    · intro v w he
      have hh := congrArg (fun z : F => z+h) he
      simpa only [sub_add_cancel] using hh
    · intro v
      exact ⟨v+h,by ring⟩
  rw [hb.sum_comp]
  exact familyTrace_sum_zero hF

/-- A literal residue population can contain arbitrary correlated complex
weights and masks; no separation of those weights is imposed here. -/
def twist (g : F → ℂ) (h : F) : ℂ :=
  ∑ v : F, g v*familyTrace (v-h)

/-- The entire constant population is invisible to every elliptic twist. -/
theorem constant_twist_zero (hF : ringChar F ≠ 2) (c : ℂ) (h : F) :
    twist (fun _ : F => c) h=0 := by
  rw [twist,← Finset.mul_sum,familyTrace_shift_sum_zero hF,mul_zero]

/-- Retaining all trace translations still loses the principal channel. -/
theorem twist_add_constant (hF : ringChar F ≠ 2) (g : F → ℂ) (c : ℂ) (h : F) :
    twist (fun v => g v+c) h=twist g h := by
  simp only [twist,add_mul,Finset.sum_add_distrib]
  rw [← Finset.mul_sum,familyTrace_shift_sum_zero hF,mul_zero,add_zero]

/-- Mean subtraction preserves every trace twist but removes exactly the
original joined signed sum. No bound for that sum follows from this identity. -/
theorem twist_sub_mean (hF : ringChar F ≠ 2) (g : F → ℂ) (h : F) :
    twist (fun v => g v-(∑ x : F,g x)/(Fintype.card F : ℂ)) h=twist g h := by
  exact twist_add_constant hF g (-((∑ x : F,g x)/(Fintype.card F : ℂ))) h

/-- A precise failure of a proposed floor from trace-twist norms alone.
The constant negative witness has zero twists and strictly negative total.
This concerns arbitrary populations, not an asserted native Riesz witness. -/
theorem no_floor_from_twist_norms (hF : ringChar F ≠ 2) :
    ¬∃ B : ℝ, ∀ g : F → ℂ,
      -B*(∑ h : F, ‖twist g h‖) ≤ (∑ v : F,g v).re := by
  rintro ⟨B,hB⟩
  have hh : (0 : ℝ) ≤ -(Fintype.card F : ℝ) := by
    simpa [constant_twist_zero hF] using hB (fun _ : F => (-1 : ℂ))
  have hc : (0 : ℝ)<(Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  linarith only [hh,hc]

end RiemannGaussian.ZetaRieszEllipticChannelAudit
