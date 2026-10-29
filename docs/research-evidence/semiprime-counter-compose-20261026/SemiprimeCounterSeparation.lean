/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSharedSummary
import RiemannGaussian.SemiprimeStreamingTensor

/-!
# Row certificates imply exact shared-summary contraction

The hypotheses are local row-span certificates and exact measurement readouts.
They imply the pointwise invariance required by the fibre theorem for the actual
streamed tensor expressions, with arbitrary polynomial corrections independent
of the original assignment. No contraction value or invariance is assumed.
-/

namespace RiemannGaussian.SemiprimeCounterSeparation
open scoped BigOperators
open RiemannGaussian.SemiprimeStreamingTensor
noncomputable section
attribute [local instance] Classical.propDecidable
variable {G E : Type*} [Fintype G] [DecidableEq G]
variable {V W Y : G → Type*} [∀ g, Fintype (V g)] [∀ g, Fintype (W g)]

/-- The rational dot product of a row with a local Boolean assignment. -/
def rowValue {A : Type*} [Fintype A] (row : A → ℚ) (x : A → Bool) : ℚ :=
  ∑ v, row v * bit (x v)

theorem rowValue_of_span {A B : Type*} [Fintype A] [Fintype B]
    (row : A → ℚ) (rows : B → A → ℚ) (c : B → ℚ)
    (hspan : ∀ v, row v = ∑ a, c a * rows a v) (x : A → Bool) :
    rowValue row x = ∑ a, c a * rowValue (rows a) x := by
  simp only [rowValue, hspan, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem rowValue_eq_of_measurements {A B : Type*} [Fintype A] [Fintype B]
    (row : A → ℚ) (rows : B → A → ℚ)
    (hspan : ∃ c : B → ℚ, ∀ v, row v = ∑ a, c a * rows a v)
    (x z : A → Bool) (hmeas : ∀ a, rowValue (rows a) x = rowValue (rows a) z) :
    rowValue row x = rowValue row z := by
  obtain ⟨c,hc⟩ := hspan
  rw [rowValue_of_span row rows c hc x, rowValue_of_span row rows c hc z]
  simp only [hmeas]

/-- Constant part of one native input port, decomposed over variable groups. -/
def basePort (arity : E → ℕ)
    (rows : (e : E) → Fin (arity e) → (g : G) → V g → ℚ)
    (e : E) (i : Fin (arity e)) (x : (g : G) → V g → Bool) : ℚ :=
  ∑ g, rowValue (rows e i g) (x g)

theorem basePort_invariant (arity : E → ℕ) (assigned : E → G)
    (rows : (e : E) → Fin (arity e) → (g : G) → V g → ℚ)
    (measureRows : (g : G) → W g → V g → ℚ)
    (measurement : (g : G) → (V g → Bool) → Y g)
    (readout : (g : G) → Y g → W g → ℚ)
    (hread : ∀ g x a, readout g (measurement g x) a = rowValue (measureRows g a) x)
    (hspan : ∀ e i g, g ≠ assigned e →
      ∃ c : W g → ℚ, ∀ v, rows e i g v = ∑ a, c a * measureRows g a v)
    (e : E) (i : Fin (arity e)) (x z : (g : G) → V g → Bool)
    (hown : x (assigned e) = z (assigned e))
    (hother : ∀ g, g ≠ assigned e → measurement g (x g) = measurement g (z g)) :
    basePort arity rows e i x = basePort arity rows e i z := by
  classical
  apply Finset.sum_congr rfl
  intro g hg
  by_cases he : g = assigned e
  · subst g
    rw [hown]
  · apply rowValue_eq_of_measurements _ (measureRows g) (hspan e i g he)
    intro a
    rw [← hread g (x g) a, ← hread g (z g) a, hother g he]

/-- Actual streamed factor polynomial, on a scalar base plus a fixed correction. -/
def factorValue (arity : E → ℕ) (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (rows : (e : E) → Fin (arity e) → (g : G) → V g → ℚ)
    (correction : (e : E) → Fin (arity e) → Polynomial ℚ)
    (e : E) (x : (g : G) → V g → Bool) : Polynomial ℚ :=
  evaluate (arity e) (fun a => Polynomial.C (T e a))
    (fun i => Polynomial.C (basePort arity rows e i x) + correction e i)

variable [Fintype E]

/-- Product of exactly the factors assigned to one group. -/
def groupValue (arity : E → ℕ) (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (assigned : E → G)
    (rows : (e : E) → Fin (arity e) → (g : G) → V g → ℚ)
    (correction : (e : E) → Fin (arity e) → Polynomial ℚ)
    (g : G) (x : (g : G) → V g → Bool) : Polynomial ℚ :=
  ∏ e : {e // assigned e = g}, factorValue arity T rows correction e.val x

theorem product_groupValue (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℚ) (assigned : E → G)
    (rows : (e : E) → Fin (arity e) → (g : G) → V g → ℚ)
    (correction : (e : E) → Fin (arity e) → Polynomial ℚ)
    (x : (g : G) → V g → Bool) :
    ∏ g, groupValue arity T assigned rows correction g x =
      ∏ e, factorValue arity T rows correction e x :=
  Fintype.prod_fiberwise assigned (fun e => factorValue arity T rows correction e x)

theorem groupValue_invariant (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℚ) (assigned : E → G)
    (rows : (e : E) → Fin (arity e) → (g : G) → V g → ℚ)
    (correction : (e : E) → Fin (arity e) → Polynomial ℚ)
    (measureRows : (g : G) → W g → V g → ℚ)
    (measurement : (g : G) → (V g → Bool) → Y g)
    (readout : (g : G) → Y g → W g → ℚ)
    (hread : ∀ g x a, readout g (measurement g x) a = rowValue (measureRows g a) x)
    (hspan : ∀ e i g, g ≠ assigned e →
      ∃ c : W g → ℚ, ∀ v, rows e i g v = ∑ a, c a * measureRows g a v)
    (g : G) (x z : (g : G) → V g → Bool) (hown : x g = z g)
    (hother : ∀ h, h ≠ g → measurement h (x h) = measurement h (z h)) :
    groupValue arity T assigned rows correction g x =
      groupValue arity T assigned rows correction g z := by
  apply Finset.prod_congr rfl
  intro e he
  rcases e with ⟨e, heq⟩
  have ho : x (assigned e) = z (assigned e) := by rw [heq]; exact hown
  have ht : ∀ h, h ≠ assigned e → measurement h (x h) = measurement h (z h) := by
    rw [heq]
    exact hother
  have hb (i : Fin (arity e)) :=
    basePort_invariant arity assigned rows measureRows measurement readout hread hspan e i x z ho ht
  simp only [factorValue, hb]

variable [∀ g, Fintype (Y g)]

/-- Separation of the actual streamed factor product follows from row-span
certificates; no pointwise invariance or contraction identity is a premise. -/
theorem separated_tensor_contraction (arity : E → ℕ)
    (T : (e : E) → (Fin (arity e) → Bool) → ℚ) (assigned : E → G)
    (rows : (e : E) → Fin (arity e) → (g : G) → V g → ℚ)
    (correction : (e : E) → Fin (arity e) → Polynomial ℚ)
    (measureRows : (g : G) → W g → V g → ℚ)
    (measurement : (g : G) → (V g → Bool) → Y g)
    (readout : (g : G) → Y g → W g → ℚ)
    (hread : ∀ g x a, readout g (measurement g x) a = rowValue (measureRows g a) x)
    (hspan : ∀ e i g, g ≠ assigned e →
      ∃ c : W g → ℚ, ∀ v, rows e i g v = ∑ a, c a * measureRows g a v)
    (forced : (g : G) → (V g → Bool) → Prop)
    (representative : ((g : G) → Y g) → (g : G) → V g → Bool)
    (hrep : ∀ y g, (∃ a, measurement g a = y g) →
      measurement g (representative y g) = y g) :
    (∑ x : (g : G) → V g → Bool, if ∀ g, forced g (x g) then
      ∏ e, factorValue arity T rows correction e x else 0) =
      ∑ y : (g : G) → Y g, ∏ g, ∑ a : V g → Bool,
        if measurement g a = y g ∧ forced g a then
          groupValue arity T assigned rows correction g (Function.update (representative y) g a)
        else 0 := by
  classical
  simp_rw [← product_groupValue arity T assigned rows correction]
  exact SemiprimeSharedSummary.shared_summary_contraction measurement forced
    (groupValue arity T assigned rows correction) representative hrep
    (groupValue_invariant arity T assigned rows correction measureRows measurement readout hread hspan)

#print axioms separated_tensor_contraction
#print axioms groupValue_invariant
#print axioms basePort_invariant
end
end RiemannGaussian.SemiprimeCounterSeparation
