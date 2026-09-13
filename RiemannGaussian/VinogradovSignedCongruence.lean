/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovWeightedLifting
import RiemannGaussian.VinogradovSignedRigidity
import RiemannGaussian.VinogradovAnisotropicCongruence

/-!
# Signed translated congruences with unequal degree precisions

The full sign pattern survives Newton reconstruction and every nonsingular
prime-power lift. Each correlated complete target costs at most r₊! * r₋!
ordered tuples. Refining degree-specific moduli gives a uniform count for
the actual signed and translated integer congruences.

The result covers tuples distinct modulo p > k. Conditioning singular
classes and the high-moment iteration remain separate obligations.
-/

namespace RiemannGaussian.VinogradovSignedCongruence
noncomputable section
open scoped BigOperators
open VinogradovSignedRigidity VinogradovWeightedLifting

/-- The integer coefficient of a retained positive/negative colour. -/
def sign (colour : Bool) : ℤ := if colour then 1 else -1

/-- Changing coefficient rings keeps the original sign. -/
theorem cast_sign {R : Type*} [Ring R] (colour : Bool) :
    ((sign colour : ℤ) : R) = if colour then 1 else -1 := by
  cases colour <;> simp [sign]

/-- Both sign coefficients are units in every prime field. -/
theorem sign_mod_ne_zero {p : ℕ} [Fact p.Prime] (colour : Bool) :
    (sign colour : ZMod p) ≠ 0 := by
  cases colour <;> simp [sign]

/-- The signed prime-field moment vector determines the tuple and its
colours up to a colour-preserving permutation. -/
theorem prime_signed_permutation {p k : ℕ} [Fact p.Prime] (hkp : k < p)
    (colour : Fin k → Bool) (v u : Fin k → ZMod p) (hv : Function.Injective v)
    (h : ∀ i : Fin k, (∑ j, (sign (colour j) : ZMod p) * v j ^ (i.val + 1)) =
      ∑ j, (sign (colour j) : ZMod p) * u j ^ (i.val + 1)) :
    ∃ σ : Equiv.Perm (Fin k), ∀ j, u j = v (σ j) ∧ colour j = colour (σ j) := by
  apply signed_power_permutation colour v u hv
  · intro n hn hnk hz
    have hd := (ZMod.natCast_eq_zero_iff n p).mp hz
    have hp := Nat.le_of_dvd (by omega : 0 < n) hd
    omega
  · intro n hn hnk
    have he := h ⟨n - 1, by omega⟩
    simpa only [Nat.sub_add_cancel hn, cast_sign] using he

/-- The full signed power-sum system retains a colour-preserving
permutation at every prime-power precision. -/
theorem prime_power_permutation {p k : ℕ} [Fact p.Prime] (hkp : k < p)
    (colour : Fin k → Bool) (v u : Fin k → ℤ)
    (hv : Function.Injective (fun i => (v i : ZMod p))) (n : ℕ)
    (hpowers : ∀ i : Fin k, (p : ℤ) ^ n ∣
      (∑ j, sign (colour j) * u j ^ (i.val + 1)) -
        ∑ j, sign (colour j) * v j ^ (i.val + 1)) :
    ∃ σ : Equiv.Perm (Fin k),
      (∀ j, colour j = colour (σ j)) ∧ ∀ j, (p : ℤ) ^ n ∣ u j - v (σ j) := by
  by_cases hn : n = 0
  · subst n
    exact ⟨Equiv.refl _, by simp⟩
  have he := prime_signed_permutation hkp colour
    (fun j => (v j : ZMod p)) (fun j => (u j : ZMod p)) hv (by
      intro i
      have hd := dvd_trans (dvd_pow_self (p : ℤ) hn) (hpowers i)
      have hz := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ p).mpr hd
      simpa only [Int.cast_sum, Int.cast_pow, Int.cast_mul] using hz)
  obtain ⟨σ, hσ⟩ := he
  refine ⟨σ, fun j => (hσ j).2, ?_⟩
  apply weighted_prime_power_rigidity hkp (fun j => sign (colour j))
    (fun j => v (σ j)) u (fun j => sign_mod_ne_zero (colour j)) (hv.comp σ.injective)
    (fun j => (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ p).mp (hσ j).1.symm) n
  intro i
  have heq : (∑ j, sign (colour j) * v (σ j) ^ (i.val + 1)) =
      ∑ j, sign (colour j) * v j ^ (i.val + 1) := by
    calc
      _ = ∑ j, sign (colour (σ j)) * v (σ j) ^ (i.val + 1) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [(hσ j).2]
      _ = _ := Equiv.sum_comp σ (fun j => sign (colour j) * v j ^ (i.val + 1))
  rw [heq]
  exact hpowers i

/-- Signed translated canonical representatives are literally equal after
a permutation preserving both sign classes. -/
theorem residue_tuple_permutation {p k n : ℕ} [Fact p.Prime] (hkp : k < p)
    (colour : Fin k → Bool) (eta : ℤ) (v u : Fin k → Fin (p ^ n))
    (hv : Function.Injective (fun i => ((v i).val : ZMod p)))
    (hpowers : ∀ i : Fin k, (p : ℤ) ^ n ∣
      (∑ j, sign (colour j) * (((u j).val : ℤ) - eta) ^ (i.val + 1)) -
        ∑ j, sign (colour j) * (((v j).val : ℤ) - eta) ^ (i.val + 1)) :
    ∃ σ : PreservingPerm (fun j => colour j = true), u = fun j => v (σ.val j) := by
  obtain ⟨σ, hc, hσ⟩ := prime_power_permutation hkp colour
    (fun j => ((v j).val : ℤ) - eta) (fun j => ((u j).val : ℤ) - eta)
    (by
      intro i j hij
      apply hv
      simpa only [Int.cast_sub, Int.cast_natCast, sub_left_inj] using hij) n hpowers
  refine ⟨⟨σ, fun j => by change colour (σ j) = true ↔ colour j = true; rw [hc j]⟩, ?_⟩
  funext j
  apply Fin.ext
  have hd : ((p ^ n : ℕ) : ℤ) ∣ ((u j).val : ℤ) - ((v (σ j)).val : ℤ) := by
    simpa only [Nat.cast_pow, sub_sub_sub_cancel_right] using hσ j
  have hz := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ (p ^ n)).mpr hd
  have he := congrArg ZMod.val hz
  simpa only [Int.cast_natCast, ZMod.val_natCast_of_lt (v (σ j)).isLt,
    ZMod.val_natCast_of_lt (u j).isLt] using he.symm

/-- The factorial allowance when the full sign partition is retained. -/
abbrev colourFactorial {k : ℕ} (colour : Fin k → Bool) : ℕ :=
  (Fintype.card {i // colour i = true}).factorial *
    (Fintype.card {i // colour i ≠ true}).factorial

/-- The canonical signed fibre has at most the product of the two sign
factorials, uniformly over every prime-power precision. -/
theorem residue_fibre_le {p k n : ℕ} [Fact p.Prime] (hkp : k < p)
    (colour : Fin k → Bool) (eta : ℤ) (v : Fin k → Fin (p ^ n))
    (hv : Function.Injective (fun i => ((v i).val : ZMod p))) :
    (Finset.univ.filter (fun u : Fin k → Fin (p ^ n) => ∀ i : Fin k,
      (p : ℤ) ^ n ∣ (∑ j, sign (colour j) * (((u j).val : ℤ) - eta) ^ (i.val + 1)) -
        ∑ j, sign (colour j) * (((v j).val : ℤ) - eta) ^ (i.val + 1))).card ≤
      colourFactorial colour := by
  classical
  have hsub : (Finset.univ.filter (fun u : Fin k → Fin (p ^ n) => ∀ i : Fin k,
      (p : ℤ) ^ n ∣ (∑ j, sign (colour j) * (((u j).val : ℤ) - eta) ^ (i.val + 1)) -
        ∑ j, sign (colour j) * (((v j).val : ℤ) - eta) ^ (i.val + 1))) ⊆
      Finset.univ.image (fun σ : PreservingPerm (fun j => colour j = true) =>
        fun j => v (σ.val j)) := by
    intro u hu
    obtain ⟨σ, hσ⟩ := residue_tuple_permutation hkp colour eta v u hv (Finset.mem_filter.mp hu).2
    exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, hσ.symm⟩
  have hc : Fintype.card (PreservingPerm (fun j => colour j = true)) =
      colourFactorial colour := by
    rw [← Nat.card_eq_fintype_card, card_preservingPerm]
  exact (Finset.card_le_card hsub).trans (by simpa only [Finset.card_univ, hc] using
    (Finset.card_image_le (s := Finset.univ)
      (f := fun σ : PreservingPerm (fun j => colour j = true) => fun j => v (σ.val j))))

/-- The complete signed modular power vector after the common integer translation. -/
def residueSignedPowers {k N : ℕ} (colour : Fin k → Bool) (eta : ℤ)
    (u : Fin k → Fin N) : Fin k → ZMod N :=
  fun i => ∑ j, (sign (colour j) : ZMod N) * (((u j).val : ZMod N) - (eta : ZMod N)) ^ (i.val + 1)

/-- Every complete target admits at most the sign-factorial allowance of
nonsingular tuples, including targets with no realizations. -/
theorem nonsingular_fibre_le {p k n : ℕ} [Fact p.Prime] (hkp : k < p)
    (colour : Fin k → Bool) (eta : ℤ) (target : Fin k → ZMod (p ^ n)) :
    (Finset.univ.filter (fun u : Fin k → Fin (p ^ n) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧
      residueSignedPowers colour eta u = target)).card ≤ colourFactorial colour := by
  classical
  let S := Finset.univ.filter (fun u : Fin k → Fin (p ^ n) =>
    Function.Injective (fun j => ((u j).val : ZMod p)) ∧
      residueSignedPowers colour eta u = target)
  change S.card ≤ _
  by_cases hS : S.Nonempty
  · obtain ⟨v, hv⟩ := hS
    obtain ⟨hvprime, hvpower⟩ := (Finset.mem_filter.mp hv).2
    apply le_trans (Finset.card_le_card ?_) (residue_fibre_le hkp colour eta v hvprime)
    intro u hu
    obtain ⟨_, hupower⟩ := (Finset.mem_filter.mp hu).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro i
    have he := congrFun (hvpower.trans hupower.symm) i
    have hz : ((∑ j, sign (colour j) * (((v j).val : ℤ) - eta) ^ (i.val + 1) : ℤ) :
        ZMod (p ^ n)) =
        ((∑ j, sign (colour j) * (((u j).val : ℤ) - eta) ^ (i.val + 1) : ℤ) :
        ZMod (p ^ n)) := by
      simpa only [residueSignedPowers, Int.cast_sum, Int.cast_mul,
        Int.cast_pow, Int.cast_sub, Int.cast_natCast] using he
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ (p ^ n)).mp hz
    simpa only [Nat.cast_pow] using hd
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp

/-- Arbitrary correlated complete target families retain their actual
cardinality and pay only the sign-factorial allowance per target. -/
theorem nonsingular_preimage_le {p k n : ℕ} [Fact p.Prime] (hkp : k < p)
    (colour : Fin k → Bool) (eta : ℤ) (T : Finset (Fin k → ZMod (p ^ n))) :
    (Finset.univ.filter (fun u : Fin k → Fin (p ^ n) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧
      residueSignedPowers colour eta u ∈ T)).card ≤ T.card * colourFactorial colour := by
  classical
  let S := Finset.univ.filter (fun u : Fin k → Fin (p ^ n) =>
    Function.Injective (fun j => ((u j).val : ZMod p)))
  have he : (Finset.univ.filter (fun u : Fin k → Fin (p ^ n) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧
      residueSignedPowers colour eta u ∈ T)) = S.filter (fun u => residueSignedPowers colour eta u ∈ T) := by
    ext u
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [he, ← Finset.sum_card_fiberwise_eq_card_filter]
  calc
    _ ≤ ∑ _ ∈ T, colourFactorial colour := by
      apply Finset.sum_le_sum
      intro target htarget
      simpa only [S, Finset.filter_filter] using nonsingular_fibre_le hkp colour eta target
    _ = _ := by simp

/-- Independent coordinate target sets are a downstream product bound;
the original correlated-target estimate remains available. -/
theorem nonsingular_coordinate_preimage_le {p k n : ℕ} [Fact p.Prime]
    (hkp : k < p) (colour : Fin k → Bool) (eta : ℤ) (T : Fin k → Finset (ZMod (p ^ n))) :
    (Finset.univ.filter (fun u : Fin k → Fin (p ^ n) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧
      ∀ i, residueSignedPowers colour eta u i ∈ T i)).card ≤
      (∏ i, (T i).card) * colourFactorial colour := by
  simpa only [Fintype.mem_piFinset, Fintype.card_piFinset] using
    nonsingular_preimage_le hkp colour eta (Fintype.piFinset T)

/-- The signed and translated complete system permits separate precisions
for every degree, with each refinement digit counted once. -/
theorem nonsingular_anisotropic_card_le {p k n : ℕ} [Fact p.Prime]
    (hkp : k < p) (colour : Fin k → Bool) (eta : ℤ)
    (e : Fin k → ℕ) (he : ∀ i, e i ≤ n) (a : Fin k → ℕ) :
    (Finset.univ.filter (fun u : Fin k → Fin (p ^ n) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧
      ∀ i, (residueSignedPowers colour eta u i).val % p ^ e i = a i)).card ≤
      p ^ (∑ i, (n - e i)) * colourFactorial colour := by
  classical
  let T (i : Fin k) := Finset.univ.filter (fun x : ZMod (p ^ n) => x.val % p ^ e i = a i)
  have hb := nonsingular_coordinate_preimage_le hkp colour eta T
  simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  apply hb.trans
  apply Nat.mul_le_mul_right
  calc
    (∏ i, (T i).card) ≤ ∏ i, p ^ (n - e i) := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro i hi
      exact VinogradovAnisotropicCongruence.prime_power_class_card_le (p := p) (he i) (a i)
    _ = p ^ (∑ i, (n - e i)) := Finset.prod_pow_eq_pow_sum _ _ _

/-- Reducing the complete modular vector to a smaller modulus agrees
with the literal signed and translated integer power sum. -/
theorem reduction_val {k N d : ℕ} [NeZero N] (hd : d ∣ N)
    (colour : Fin k → Bool) (eta : ℤ) (u : Fin k → Fin N) (i : Fin k) :
    (residueSignedPowers colour eta u i).val % d =
      ((∑ j, sign (colour j) * (((u j).val : ℤ) - eta) ^ (i.val + 1) : ℤ) : ZMod d).val := by
  have hcast : ((residueSignedPowers colour eta u i).val : ZMod d) =
      ((∑ j, sign (colour j) * (((u j).val : ℤ) - eta) ^ (i.val + 1) : ℤ) : ZMod d) := by
    rw [ZMod.natCast_val, ← ZMod.castHom_apply (h := hd)]
    simp only [residueSignedPowers, map_sum, map_mul, map_pow, map_sub, map_natCast,
      map_intCast, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_sub, Int.cast_natCast]
  simpa only [ZMod.val_natCast] using congrArg ZMod.val hcast

/-- The bound applies to the actual signed integer congruences, with an
arbitrary common translation and all degree precisions preserved. -/
theorem actual_anisotropic_card_le {p k n : ℕ} [Fact p.Prime]
    (hkp : k < p) (colour : Fin k → Bool) (eta : ℤ)
    (e : Fin k → ℕ) (he : ∀ i, e i ≤ n) (a : Fin k → ℤ) :
    (Finset.univ.filter (fun u : Fin k → Fin (p ^ n) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧ ∀ i : Fin k,
      (p : ℤ) ^ e i ∣ (∑ j, sign (colour j) * (((u j).val : ℤ) - eta) ^ (i.val + 1)) -
        a i)).card ≤ p ^ (∑ i, (n - e i)) * colourFactorial colour := by
  classical
  have hp := (Fact.out : p.Prime).pos
  have : NeZero (p ^ n) := ⟨ne_of_gt (pow_pos hp n)⟩
  apply le_trans (Finset.card_le_card ?_)
    (nonsingular_anisotropic_card_le hkp colour eta e he
      (fun i => (a i : ZMod (p ^ e i)).val))
  intro u hu
  obtain ⟨huprime, hupower⟩ := (Finset.mem_filter.mp hu).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, huprime, ?_⟩
  intro i
  rw [reduction_val (pow_dvd_pow p (he i))]
  apply congrArg ZMod.val
  symm
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ (p ^ e i)).mpr
  simpa only [Nat.cast_pow] using hupower i

/-- At moduli p^b,...,p^(kb), signed translated nonsingular tuples cost
p^(b*k*(k-1)/2) times the factorials of the two retained sign classes. -/
theorem degree_moduli_card_le {p k b : ℕ} [Fact p.Prime] (hkp : k < p)
    (colour : Fin k → Bool) (eta : ℤ) (a : Fin k → ℤ) :
    (Finset.univ.filter (fun u : Fin k → Fin (p ^ (k * b)) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧ ∀ i : Fin k,
      (p : ℤ) ^ ((i.val + 1) * b) ∣
        (∑ j, sign (colour j) * (((u j).val : ℤ) - eta) ^ (i.val + 1)) - a i)).card ≤
      p ^ (b * (k * (k - 1) / 2)) * colourFactorial colour := by
  simpa only [VinogradovAnisotropicCongruence.degree_precision_cost] using
    actual_anisotropic_card_le hkp colour eta (fun i => (i.val + 1) * b)
      (fun i => Nat.mul_le_mul_right b (by omega : i.val + 1 ≤ k)) a

end
end RiemannGaussian.VinogradovSignedCongruence
