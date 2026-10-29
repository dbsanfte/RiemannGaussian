import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SubexpAnnihilation
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.LayoutExactBuckets

namespace OAI.Algorithms

/-!
# Cleared integer matrices and exact ring-valued source rows

The rational spectral argument will supply integer numerators `N` and a
power-of-two denominator `d`. Over the target coefficient ring only the
unit representing `d` is inverted. Exact integer equations `d I - N`
therefore imply the fixed-vector equations needed by the original
multicolor row construction, without a map from `ℚ` to the target ring.
-/

namespace SubexponentialSAT.SqrtLog.LayoutScaledMatrices

open scoped BigOperators
open Matrix

section Cleared

variable {J O : Type*} [Fintype J] [DecidableEq J] [CommRing O]

def clearedDefect (d : ℤ) (N : Matrix J J ℤ) : Matrix J J ℤ :=
  fun i j => (if i = j then d else 0) - N i j

def unitScaled (u : Oˣ) (N : Matrix J J ℤ) : Matrix J J O :=
  fun i j => (↑(u⁻¹) : O) * (N i j : O)

theorem fixed_of_clearedDefect (d : ℤ) (u : Oˣ) (hu : (u : O) = (d : O))
    (N : Matrix J J ℤ) (z : J → ℤ)
    (hz : clearedDefect d N *ᵥ z = 0) :
    unitScaled u N *ᵥ (fun j => (z j : O)) = fun j => (z j : O) := by
  funext i
  have hzi := congrFun hz i
  have hN : ∑ j, N i j * z j = d * z i := by
    have hzero : d * z i - ∑ j, N i j * z j = 0 := by
      simpa [clearedDefect, Matrix.mulVec, dotProduct, sub_mul,
        Finset.sum_sub_distrib] using hzi
    exact (sub_eq_zero.mp hzero).symm
  change (∑ j, (↑(u⁻¹) : O) * (N i j : O) * (z j : O)) = (z i : O)
  calc
    _ = (↑(u⁻¹) : O) * ((∑ j, N i j * z j : ℤ) : O) := by
      simp [Finset.mul_sum, mul_assoc]
    _ = (↑(u⁻¹) : O) * ((d * z i : ℤ) : O) := by rw [hN]
    _ = (z i : O) := by
      push_cast
      rw [← hu, ← mul_assoc]
      simp

end Cleared

section SourceRows

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpRowInterpolation

variable {O : Type*} [CommRing O] {r Q Δ : ℕ}
variable {node : Fin Q → O}

abbrev Numerators (r Q Δ : ℕ) :=
  (t : Fin Q) → (g : Fin r) → (i : Fin Δ) →
    Matrix (Joint t g i) (Joint t g i) ℤ

noncomputable def sourceRow (N : Numerators r Q Δ) (denom : Oˣ)
    (a : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ)
    (units : NodeUnits node) : UniversalType r Q Δ → Polynomial O :=
  SubexponentialSAT.SubexpAnnihilation.rowForMatrices (RingHom.id O)
    (fun t g j => unitScaled denom (N t g j)) a i R units

theorem sourceRow_origin (N : Numerators r Q Δ) (denom : Oˣ)
    (a : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ) (units : NodeUnits node) :
    (fun y => (sourceRow N denom a i R units y).eval 0) = Pi.single a 1 :=
  SubexponentialSAT.SubexpAnnihilation.rowForMatrices_origin _ _ _ _ _ _

theorem sourceRow_degree (N : Numerators r Q Δ) (denom : Oˣ)
    (a : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ) (units : NodeUnits node)
    (y : UniversalType r Q Δ) :
    (sourceRow N denom a i R units y).natDegree ≤ R :=
  SubexponentialSAT.SubexpAnnihilation.rowForMatrices_degree _ _ _ _ _ _ _

/-- This is the actual multicolor path from the immutable library, with
cleared integer source constraints and a unit denominator. -/
theorem sourceRow_annihilates
    (N : Numerators r Q Δ) (d : ℤ) (denom : Oˣ)
    (hdenom : (denom : O) = (d : O))
    (a : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ) (units : NodeUnits node)
    (hsupport : ∀ t g j (a b : Joint t g j), N t g j a b ≠ 0 →
      (mismatchPositions (fun y : UniversalType r Q Δ => y.head)
        (a.val.slot j) b.val).card ≤ R)
    (t : Fin Q) (g : Fin r) (hg : g ≠ a.slot i t)
    (z : UniversalType r Q Δ → ℤ)
    (hz : ∀ y, y.head t ≠ g → z y = 0)
    (hconstraint : clearedDefect d (N t g i) *ᵥ
        (fun y : Joint t g i => z y) = 0) :
    (∑ y, (sourceRow N denom a i R units y).eval (node t) * (z y : O)) = 0 := by
  have hs : ∀ t g j (a b : Joint t g j), unitScaled denom (N t g j) a b ≠ 0 →
      (mismatchPositions (fun y : UniversalType r Q Δ => y.head)
        (a.val.slot j) b.val).card ≤ R := by
    intro t g j a b hab
    apply hsupport t g j a b
    intro heq
    apply hab
    simp [unitScaled, heq]
  have hf := fixed_of_clearedDefect d denom hdenom (N t g i)
    (fun y : Joint t g i => z y) hconstraint
  have h := SubexponentialSAT.SubexpAnnihilation.rowForMatrices_annihilates_of_fixed
    (RingHom.id O) (fun t g j => unitScaled denom (N t g j))
    a i R units hs t g hg (fun y => (z y : O))
    (by intro y hy; simp [hz y hy]) hf
  simpa only [sourceRow, RingHom.id_apply, dotProduct] using h

end SourceRows

end SubexponentialSAT.SqrtLog.LayoutScaledMatrices

end OAI.Algorithms
