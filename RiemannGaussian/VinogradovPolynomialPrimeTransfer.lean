/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovPolynomialExceptional
import RiemannGaussian.VinogradovTwoBlockPacket

/-!
# The unrestricted mixed count reaches an eligible nonsingular count

The maximum-over-types argument pays both repeated blocks. One common
prime packet then covers all retained solutions, and its largest eligible
nonsingular count carries the original count with factor `2*R`. The same
tail, positive endpoints and all integer equations are retained.
-/

namespace RiemannGaussian.VinogradovPolynomialPrimeTransfer
noncomputable section
open scoped BigOperators Classical
open Polynomial VinogradovPolynomialSystems VinogradovPolynomialDifferencing
open VinogradovMixedMoments VinogradovMixedExceptional VinogradovTypeMaximum
open VinogradovTwoBlockPacket VinogradovPolynomialExceptional
open VinogradovPolynomialNonsingular (Window nonsingularCount)

/-- Use the same finite enumeration as the existing nonsingular count. -/
local instance windowFintype (p m P : ℕ) : Fintype (Window p m P) := Fintype.ofFinite _

/-- The literal full collisions with both original blocks separated modulo p. -/
def separatedCount {κ a : Type*} [Fintype κ] {P : ℕ}
    (p m s : ℕ) (v : Fin P → a → ℤ) (u : κ → a → ℤ) : ℕ :=
  (Finset.univ.filter (fun xy : ((Fin m → Fin P) × (Fin s → κ)) ×
      ((Fin m → Fin P) × (Fin s → κ)) =>
    (Function.Injective (fun i => (((xy.1.1 i).val + 1 : ℕ) : ZMod p)) ∧
      Function.Injective (fun i => (((xy.2.1 i).val + 1 : ℕ) : ZMod p))) ∧
    configurationFrequency m s v u xy.1 = configurationFrequency m s v u xy.2)).card

/-- A common packet covers both full blocks of every original retained collision. -/
theorem distinct_le_separated_sum {κ a : Type*} [Fintype κ] {P : ℕ}
    (m s : ℕ) (v : Fin P → a → ℤ) (u : κ → a → ℤ) (π : Finset ℕ)
    (hcover : ∀ x y : Fin m → Fin P, Function.Injective x → Function.Injective y →
      ∃ p ∈ π, Function.Injective (fun i => (((x i).val + 1 : ℕ) : ZMod p)) ∧
        Function.Injective (fun i => (((y i).val + 1 : ℕ) : ZMod p))) :
    distinctCount m s v u ≤ ∑ p ∈ π, separatedCount p m s v u := by
  let S (p : ℕ) := Finset.univ.filter (fun xy : ((Fin m → Fin P) × (Fin s → κ)) ×
      ((Fin m → Fin P) × (Fin s → κ)) =>
    (Function.Injective (fun i => (((xy.1.1 i).val + 1 : ℕ) : ZMod p)) ∧
      Function.Injective (fun i => (((xy.2.1 i).val + 1 : ℕ) : ZMod p))) ∧
    configurationFrequency m s v u xy.1 = configurationFrequency m s v u xy.2)
  have hs : Finset.univ.filter (fun xy : ((Fin m → Fin P) × (Fin s → κ)) ×
      ((Fin m → Fin P) × (Fin s → κ)) =>
    (Function.Injective xy.1.1 ∧ Function.Injective xy.2.1) ∧
      configurationFrequency m s v u xy.1 = configurationFrequency m s v u xy.2) ⊆
      π.biUnion S := by
    intro xy hxy
    have hx := (Finset.mem_filter.mp hxy).2
    obtain ⟨p, hp, hl, hr⟩ := hcover xy.1.1 xy.2.1 hx.1.1 hx.1.2
    exact Finset.mem_biUnion.mpr
      ⟨p, hp, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hl, hr⟩, hx.2⟩⟩
  convert (Finset.card_le_card hs).trans Finset.card_biUnion_le using 1 <;> try rfl
  unfold distinctCount
  congr 1
  ext xy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Passing to the two nonsingular subtypes preserves the complete
original configuration, so no frequency equation or endpoint is paid away. -/
theorem separated_le_nonsingular {κ : Type*} [Fintype κ]
    (p m d P s : ℕ) (F : Fin m → ℤ[X]) (u : κ → (Fin d ⊕ Fin m) → ℤ) :
    separatedCount p m s (fun x : Fin P => fullFrequency d F (x.val + 1)) u ≤
      nonsingularCount p m d P s F u := by
  let S := Finset.univ.filter (fun xy : ((Fin m → Fin P) × (Fin s → κ)) ×
      ((Fin m → Fin P) × (Fin s → κ)) =>
    (Function.Injective (fun i => (((xy.1.1 i).val + 1 : ℕ) : ZMod p)) ∧
      Function.Injective (fun i => (((xy.2.1 i).val + 1 : ℕ) : ZMod p))) ∧
    configurationFrequency m s (fun x : Fin P => fullFrequency d F (x.val + 1)) u xy.1 =
      configurationFrequency m s (fun x : Fin P => fullFrequency d F (x.val + 1)) u xy.2)
  let V := VinogradovPolynomialNonsingular.configurationFrequency (p := p) (P := P) d s F u
  let C := Finset.univ.filter (fun z : (Window p m P × (Fin s → κ)) ×
      (Window p m P × (Fin s → κ)) => V z.1 = V z.2 + 0)
  let f (xy : S) : C := by
    have hx := (Finset.mem_filter.mp xy.property).2
    refine ⟨((⟨xy.val.1.1, hx.1.1⟩, xy.val.1.2),
      (⟨xy.val.2.1, hx.1.2⟩, xy.val.2.2)), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simpa only [V, VinogradovPolynomialNonsingular.configurationFrequency,
      VinogradovPolynomialNonsingular.windowFrequency, VinogradovPolynomialConditioning.blockFrequency,
      configurationFrequency, VinogradovShiftedMoment.tupleFrequency, add_zero] using hx.2
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    exact congrArg (fun z : C =>
      ((z.val.1.1.val, z.val.1.2), (z.val.2.1.val, z.val.2.2))) he
  have h : S.card ≤ C.card := Finset.card_le_card_of_injective hf
  convert h using 1 <;> try rfl
  unfold separatedCount
  dsimp only [S]
  congr 1
  ext xy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Any proved finite packet with enough prime product carries the full
original type count, with its actual cardinality and upper endpoint. -/
theorem exists_prime_carrying_count_of_packet {κ : Type*} [Fintype κ]
    {m d T e P s M U : ℕ} {F : Fin m → ℤ[X]} (hF : HasType F d T e)
    (hm : 2 ≤ m) (hP : 4 * m ^ 4 ≤ P)
    (hT0 : 0 < T) (hT : T ≤ P ^ d) (π : Finset ℕ)
    (hπ : ∀ p ∈ π, p.Prime ∧ M < p ∧ p ≤ U)
    (hbudget : P ^ (d + 2 * m.choose 2) < ∏ p ∈ π, p)
    (u : κ → (Fin d ⊕ Fin m) → ℤ) :
    ∃ (e' p : ℕ) (G : Fin m → ℤ[X]), HasType G d T e' ∧
      p.Prime ∧ M < p ∧ p ≤ U ∧ ¬p ∣ T ∧
      typeCount d P s F u ≤ 2 * π.card * nonsingularCount p m d P s G u := by
  obtain ⟨e', G, hG, hgood⟩ := exists_count_reduction hF hm hP u
  have hsep := packet_separates_blocks (fun p hp => (hπ p hp).1) hbudget
  let E := π.filter (fun p => ¬p ∣ T)
  have hP0 : 0 < P := by
    have hm0 : 0 < m := by omega
    have hpow : 0 < 4 * m ^ 4 := by positivity
    omega
  have hTprod : T < ∏ p ∈ π, p :=
    hT.trans_lt ((Nat.pow_le_pow_right (by omega : 0 < P)
      (Nat.le_add_right d (2 * m.choose 2))).trans_lt hbudget)
  obtain ⟨p₀, hp₀, hp₀T⟩ := VinogradovPrimePacket.exists_prime_not_dvd
    (fun p hp => (hπ p hp).1) hT0 hTprod
  have hE : E.Nonempty := ⟨p₀, Finset.mem_filter.mpr ⟨hp₀, hp₀T⟩⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image E
    (fun p => nonsingularCount p m d P s G u) hE
  have hsum := distinct_le_separated_sum m s
    (fun x : Fin P => fullFrequency d G (x.val + 1)) u E (by
      intro x y hx hy
      obtain ⟨q, hq, hqT, hqx, hqy⟩ := hsep T hT0 hT x y hx hy
      exact ⟨q, Finset.mem_filter.mpr ⟨hq, hqT⟩, hqx, hqy⟩)
  have hsum' : (∑ q ∈ E,
      separatedCount q m s (fun x : Fin P => fullFrequency d G (x.val + 1)) u) ≤
      π.card * nonsingularCount p m d P s G u := by
    calc
      _ ≤ ∑ _q ∈ E, nonsingularCount p m d P s G u := by
        apply Finset.sum_le_sum
        intro q hq
        exact (separated_le_nonsingular q m d P s G u).trans (hmax q hq)
      _ = E.card * nonsingularCount p m d P s G u := by simp
      _ ≤ π.card * nonsingularCount p m d P s G u := by
        apply Nat.mul_le_mul_right
        exact Finset.card_filter_le _ _
  have hpπ := (Finset.mem_filter.mp hp).1
  refine ⟨e', p, G, hG, (hπ p hpπ).1, (hπ p hpπ).2.1, (hπ p hpπ).2.2,
    (Finset.mem_filter.mp hp).2, ?_⟩
  exact hgood.trans (by
    rw [mul_assoc]
    exact Nat.mul_le_mul_left 2 (hsum.trans hsum'))


/-- One eligible prime carries the full original type count after the
proved repeated-tuple absorption. The packet width is the explicit
Bertrand width, and its separation budget is a displayed size condition. -/
theorem exists_prime_carrying_count {κ : Type*} [Fintype κ]
    {m d T e P s M R : ℕ} {F : Fin m → ℤ[X]} (hF : HasType F d T e)
    (hm : 2 ≤ m) (hP : 4 * m ^ 4 ≤ P) (hM : 0 < M)
    (hT0 : 0 < T) (hT : T ≤ P ^ d)
    (hbudget : P ^ (d + 2 * m.choose 2) < M ^ R)
    (u : κ → (Fin d ⊕ Fin m) → ℤ) :
    ∃ (e' p : ℕ) (G : Fin m → ℤ[X]), HasType G d T e' ∧
      p.Prime ∧ M < p ∧ p ≤ 2 ^ R * M ∧ ¬p ∣ T ∧
      typeCount d P s F u ≤ 2 * R * nonsingularCount p m d P s G u := by
  obtain ⟨π, hcard, hπ, hprod, _⟩ := exists_uniform_two_block_packet M R m d P hM hbudget
  simpa only [hcard] using exists_prime_carrying_count_of_packet hF hm hP hT0 hT π hπ hprod u

end
end RiemannGaussian.VinogradovPolynomialPrimeTransfer
