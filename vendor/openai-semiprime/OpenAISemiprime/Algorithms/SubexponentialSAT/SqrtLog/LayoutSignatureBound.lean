import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.LayoutExactBuckets

namespace OAI.Algorithms

/-! Exact integer signature ranges for Boolean assignments. -/
namespace SubexponentialSAT.SqrtLog.LayoutSignatureBound

open scoped BigOperators
open LayoutExactBuckets

variable {J V : Type*} [Fintype J] [Fintype V]

/-- Boolean assignments are embedded in the integers before signatures are
computed. No precision-dependent modulus enters this definition. -/
def boolSignature (A : J → V → ℤ) (x : V → Bool) : J → ℤ :=
  signature A (fun v => if x v then 1 else 0)

omit [Fintype J] in
theorem abs_boolSignature_le (A : J → V → ℤ) (W : ℕ)
    (hA : ∀ j v, |A j v| ≤ (W : ℤ)) (x : V → Bool) (j : J) :
    |boolSignature A x j| ≤ (Fintype.card V * W : ℕ) := by
  unfold boolSignature signature
  calc
    _ ≤ ∑ v, |A j v * (if x v then 1 else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v : V, (W : ℤ) := by
      apply Finset.sum_le_sum
      intro v _
      cases h : x v <;> simp [ hA j v]
    _ = (Fintype.card V * W : ℕ) := by simp

/-- The number of attained integer labels has the usual height/rank bound,
independently of the characteristic and prime-power precision used later. -/
theorem card_range_boolSignature_le (A : J → V → ℤ) (W : ℕ)
    (hA : ∀ j v, |A j v| ≤ (W : ℤ)) :
    Nat.card (Set.range (boolSignature A)) ≤
      (2 * Fintype.card V * W + 1) ^ Fintype.card J := by
  classical
  let B := Fintype.card V * W
  let enc : Set.range (boolSignature A) → (J → Fin (2 * B + 1)) := fun y j =>
    ⟨(y.val j + (B : ℤ)).toNat, by
      obtain ⟨x, hx⟩ := y.property
      have hb := abs_boolSignature_le A W hA x j
      have hbounds := abs_le.mp hb
      have hy : y.val j = boolSignature A x j := congrFun hx.symm j
      rw [hy]
      dsimp [B]
      omega⟩
  have hinj : Function.Injective enc := by
    intro y z he
    apply Subtype.ext
    funext j
    have heq := congrArg Fin.val (congrFun he j)
    change (y.val j + (B : ℤ)).toNat = (z.val j + (B : ℤ)).toNat at heq
    obtain ⟨x, hx⟩ := y.property
    obtain ⟨w, hw⟩ := z.property
    have hy := abs_le.mp (abs_boolSignature_le A W hA x j)
    have hz := abs_le.mp (abs_boolSignature_le A W hA w j)
    have ey : y.val j = boolSignature A x j := congrFun hx.symm j
    have ez : z.val j = boolSignature A w j := congrFun hw.symm j
    dsimp [B] at heq
    rw [ey, ez] at heq ⊢
    omega
  have hc := Nat.card_le_card_of_injective enc hinj
  simpa [Nat.card_eq_fintype_card, Fintype.card_fun, B, Nat.mul_assoc] using hc

end SubexponentialSAT.SqrtLog.LayoutSignatureBound

end OAI.Algorithms
