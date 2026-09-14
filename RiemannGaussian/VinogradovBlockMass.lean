/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovResidueEnergy
import Mathlib.Data.Fintype.CardEmbedding
/-!
# Quantitative mass of the original nonsingular block family

Every injective choice of next digits, together with arbitrary quotient
choices in complete blocks of length p^(a+1), determines one original
positive conditioned block. Exact reconstruction makes this map injective.
Its cardinality gives p.descFactorial(k)*floor(X/p^(a+1))^k actual blocks.
A paid floor inequality also gives an explicit lower bound proportional
to X^k. These are counts of the actual family, not assumed normalizations.
-/

namespace RiemannGaussian.VinogradovBlockMass
noncomputable section
open scoped Classical
open VinogradovResidueEnergy

/-- Construct an original positive block from all distinct next digits and all complete higher-quotient choices. -/
def blockFromDigits {p k a M X : ℕ} [NeZero p]
    (hX : p ^ (a + 1) * M ≤ X)
    (d : (Fin k ↪ Fin p) × (Fin k → Fin M)) : ConditionedWindow p k a 0 X := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hpa : 0 < p ^ a := pow_pos hp a
  let t (j : Fin k) := p * (d.2 j).val + (d.1 j).val + 1
  have ht (j : Fin k) : 0 < t j := by dsimp [t]; omega
  have hu (j : Fin k) : p ^ a * t j ≤ X := by
    have hj : t j ≤ p * M := by
      have h := Nat.mul_le_mul_left p (show (d.2 j).val + 1 ≤ M by omega)
      dsimp [t]
      nlinarith [(d.1 j).isLt]
    calc
      _ ≤ p ^ a * (p * M) := Nat.mul_le_mul_left _ hj
      _ = p ^ (a + 1) * M := by rw [pow_succ]; ring
      _ ≤ X := hX
  let x : Fin k → Fin X := fun j => ⟨p ^ a * t j - 1, by
    have hpj := Nat.mul_pos hpa (ht j)
    have huj := hu j
    omega⟩
  have hx (j : Fin k) : (x j).val + 1 = p ^ a * t j := by
    have hpj := Nat.mul_pos hpa (ht j)
    dsimp [x]
    omega
  refine ⟨x, ?_, ?_⟩
  · intro j
    rw [hx]
    exact Nat.mul_mod_right _ _
  · intro i j hij
    simp only [hx, Nat.mul_div_cancel_left _ hpa] at hij
    simp only [t, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add,
      Nat.cast_one, add_left_inj] at hij
    have he := congrArg ZMod.val hij
    rw [ZMod.val_natCast_of_lt (d.1 i).isLt, ZMod.val_natCast_of_lt (d.1 j).isLt] at he
    exact d.1.injective (Fin.ext he)

/-- Each constructed coordinate recovers its exact digit and quotient without a boundary error. -/
theorem blockFromDigits_val {p k a M X : ℕ} [NeZero p]
    (hX : p ^ (a + 1) * M ≤ X)
    (d : (Fin k ↪ Fin p) × (Fin k → Fin M)) (j : Fin k) :
    ((blockFromDigits hX d).val j).val + 1 =
      p ^ a * (p * (d.2 j).val + (d.1 j).val + 1) := by
  have hpa : 0 < p ^ a := pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) a
  have hpj : 0 < p ^ a * (p * (d.2 j).val + (d.1 j).val + 1) := Nat.mul_pos hpa (by omega)
  change p ^ a * (p * (d.2 j).val + (d.1 j).val + 1) - 1 + 1 = _
  omega

/-- The original positive integers uniquely determine every digit and quotient choice. -/
theorem blockFromDigits_injective {p k a M X : ℕ} [NeZero p]
    (hX : p ^ (a + 1) * M ≤ X) : Function.Injective (blockFromDigits (k := k) hX) := by
  intro d e hde
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hpa : 0 < p ^ a := pow_pos hp a
  have hv (j : Fin k) : p * (d.2 j).val + (d.1 j).val = p * (e.2 j).val + (e.1 j).val := by
    have he := congrArg (fun z : ConditionedWindow p k a 0 X => (z.val j).val + 1) hde
    rw [blockFromDigits_val, blockFromDigits_val] at he
    exact Nat.add_right_cancel (Nat.eq_of_mul_eq_mul_left hpa he)
  have hd (j : Fin k) : (d.1 j).val = (e.1 j).val := by
    have he := congrArg (fun t => t % p) (hv j)
    simpa only [Nat.add_mod, Nat.mul_mod_right, zero_add,
      Nat.mod_eq_of_lt (d.1 j).isLt, Nat.mod_eq_of_lt (e.1 j).isLt] using he
  apply Prod.ext
  · exact Function.Embedding.ext (fun j => Fin.ext (hd j))
  · funext j
    apply Fin.ext
    have he := hv j
    rw [hd j] at he
    exact Nat.eq_of_mul_eq_mul_left hp (Nat.add_right_cancel he)

/-- Count every injective next-digit choice and every complete higher block inside the original window. -/
theorem conditionedWindow_card_ge {p k a M X : ℕ} [NeZero p]
    (hX : p ^ (a + 1) * M ≤ X) :
    p.descFactorial k * M ^ k ≤ Fintype.card (ConditionedWindow p k a 0 X) := by
  have h := Fintype.card_le_of_injective (blockFromDigits (k := k) hX) (blockFromDigits_injective hX)
  simpa only [Fintype.card_prod, Fintype.card_embedding_eq, Fintype.card_fun,
    Fintype.card_fin] using h

/-- The actual nonsingular block count has a completely explicit falling-factorial and floor lower bound. -/
theorem conditionedWindow_floor_card_ge {p k a X : ℕ} [NeZero p] :
    p.descFactorial k * (X / p ^ (a + 1)) ^ k ≤ Fintype.card (ConditionedWindow p k a 0 X) :=
  conditionedWindow_card_ge (Nat.mul_div_le X (p ^ (a + 1)))

/-- Once one full block fits, its quotient floor loses at most a factor of two. -/
theorem half_quotient_le {q X : ℕ} (hq : 0 < q) (hX : q ≤ X) :
    (X : ℝ) / (2 * (q : ℝ)) ≤ ((X / q : ℕ) : ℝ) := by
  have hd : 1 ≤ X / q := (Nat.le_div_iff_mul_le hq).mpr (by simpa)
  have he := Nat.mod_add_div X q
  have hm := Nat.mod_lt X hq
  have hc := Nat.mul_le_mul_left q hd
  have hn : X ≤ X / q * (2 * q) := by nlinarith
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (q : ℝ))).mpr
  exact_mod_cast hn

/-- The actual original block count is bounded below by an explicit positive multiple of X^k. -/
theorem conditionedWindow_real_mass_ge {p k a X : ℕ} [NeZero p]
    (hX : p ^ (a + 1) ≤ X) :
    (p.descFactorial k : ℝ) * ((X : ℝ) / (2 * (p ^ (a + 1) : ℕ))) ^ k ≤
      (Fintype.card (ConditionedWindow p k a 0 X) : ℝ) := by
  have hq : 0 < p ^ (a + 1) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) _
  have hpow := pow_le_pow_left₀ (by positivity) (half_quotient_le hq hX) k
  calc
    _ ≤ (p.descFactorial k : ℝ) * ((X / p ^ (a + 1) : ℕ) : ℝ) ^ k :=
      mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
    _ ≤ _ := by exact_mod_cast (conditionedWindow_floor_card_ge (p := p) (k := k) (a := a) (X := X))

end
end RiemannGaussian.VinogradovBlockMass
