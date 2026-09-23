/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovPrimePacket

/-!
# One eligible prime separates both original blocks

The product over unordered position pairs retains the classical
discriminant exponent. A single prime avoids the type multiplier and both
separation products. Iterated Bertrand supplies a uniform finite packet;
its upper endpoint is explicitly `2^R*M`, not the sharper `2*M`.
-/

namespace RiemannGaussian.VinogradovTwoBlockPacket
noncomputable section
open scoped Classical BigOperators
open VinogradovPrimePacket

/-- Count each off-diagonal position pair once. -/
def pairProduct {m : ℕ} (x : Fin m → ℕ) : ℕ :=
  ∏ ij ∈ (Finset.univ : Finset (Fin m × Fin m)).filter (fun ij => ij.1 < ij.2),
    Nat.dist (x ij.1) (x ij.2)

/-- Distinct integer entries give a positive unordered separation product. -/
theorem pairProduct_pos {m : ℕ} {x : Fin m → ℕ} (hx : Function.Injective x) :
    0 < pairProduct x := by
  apply Finset.prod_pos
  intro ij hij
  exact Nat.dist_pos_of_ne (hx.ne (ne_of_lt (Finset.mem_filter.mp hij).2))

/-- One block costs exactly the number of unordered pairs. -/
theorem pairProduct_le {m P : ℕ} (x : Fin m → ℕ) (hx : ∀ i, x i ≤ P) :
    pairProduct x ≤ P ^ (m.choose 2) := by
  have hc : ((Finset.univ : Finset (Fin m × Fin m)).filter (fun ij => ij.1 < ij.2)).card =
      m.choose 2 := by
    simpa only [Finset.univ_product_univ, Finset.card_univ, Fintype.card_fin] using
      Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin m)))
  unfold pairProduct
  rw [← hc, ← Finset.prod_const]
  apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
  intro ij hij
  have hi := hx ij.1
  have hj := hx ij.2
  unfold Nat.dist
  omega

/-- Every distinct pair's distance divides the unordered product. -/
theorem dist_dvd_pairProduct {m : ℕ} (x : Fin m → ℕ) {i j : Fin m} (hij : i ≠ j) :
    Nat.dist (x i) (x j) ∣ pairProduct x := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact Finset.dvd_prod_of_mem (fun ij : Fin m × Fin m => Nat.dist (x ij.1) (x ij.2))
      (Finset.mem_filter.mpr ⟨Finset.mem_univ (i, j), h⟩)
  · rw [Nat.dist_comm]
    exact Finset.dvd_prod_of_mem (fun ij : Fin m × Fin m => Nat.dist (x ij.1) (x ij.2))
      (Finset.mem_filter.mpr ⟨Finset.mem_univ (j, i), h⟩)

/-- Avoiding the unordered product preserves every pairwise distinction modulo p. -/
theorem mod_injective_of_not_dvd {m p : ℕ} (x : Fin m → ℕ)
    (hp : ¬p ∣ pairProduct x) : Function.Injective (fun i => x i % p) := by
  intro i j hij
  by_contra hne
  apply hp
  have hm : Nat.ModEq p (x i) (x j) := hij
  have hd : p ∣ Nat.dist (x i) (x j) := by
    unfold Nat.dist
    exact dvd_add hm.symm.dvd' hm.dvd'
  exact hd.trans (dist_dvd_pairProduct x hne)

/-- The type multiplier and both blocks share one exact discriminant budget. -/
theorem two_block_budget {m d P T : ℕ} (hT : T ≤ P ^ d)
    (x y : Fin m → ℕ) (hx : ∀ i, x i ≤ P) (hy : ∀ i, y i ≤ P) :
    T * pairProduct x * pairProduct y ≤ P ^ (d + 2 * m.choose 2) := by
  calc
    _ ≤ P ^ d * P ^ (m.choose 2) * P ^ (m.choose 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul hT (pairProduct_le x hx)) (pairProduct_le y hy)
    _ = _ := by rw [← pow_add, ← pow_add]; congr 1; omega

/-- A packet whose prime product exceeds the joint budget has one prime
which avoids T and separates both original distinct blocks simultaneously. -/
theorem exists_eligible_separating_prime {m d P T : ℕ} {π : Finset ℕ}
    (hπ : ∀ p ∈ π, p.Prime) (hT0 : 0 < T) (hT : T ≤ P ^ d)
    (hbudget : P ^ (d + 2 * m.choose 2) < ∏ p ∈ π, p)
    (x y : Fin m → ℕ) (hx : Function.Injective x) (hy : Function.Injective y)
    (hxP : ∀ i, x i ≤ P) (hyP : ∀ i, y i ≤ P) :
    ∃ p ∈ π, ¬p ∣ T ∧ Function.Injective (fun i => x i % p) ∧
      Function.Injective (fun i => y i % p) := by
  obtain ⟨p, hp, hnot⟩ := exists_prime_not_dvd hπ
    (mul_pos (mul_pos hT0 (pairProduct_pos hx)) (pairProduct_pos hy))
    ((two_block_budget hT x y hxP hyP).trans_lt hbudget)
  refine ⟨p, hp, ?_, mod_injective_of_not_dvd x ?_, mod_injective_of_not_dvd y ?_⟩
  · exact fun h => hnot (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _)
  · exact fun h => hnot (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _)
  · exact fun h => hnot (dvd_mul_of_dvd_right h _)

/-- The original positive-index block enters ZMod with the same distinctions. -/
theorem positive_mod_injective {m P p : ℕ} (x : Fin m → Fin P)
    (hx : Function.Injective (fun i => ((x i).val + 1) % p)) :
    Function.Injective (fun i => (((x i).val + 1 : ℕ) : ZMod p)) := by
  intro i j hij
  exact hx ((ZMod.natCast_eq_natCast_iff' _ _ _).mp hij)

/-- Any actual prime packet exceeding the joint discriminant budget
separates both original blocks while avoiding the type multiplier. -/
theorem packet_separates_blocks {m d P : ℕ} {π : Finset ℕ}
    (hπ : ∀ p ∈ π, p.Prime)
    (hbudget : P ^ (d + 2 * m.choose 2) < ∏ p ∈ π, p) :
    ∀ T : ℕ, 0 < T → T ≤ P ^ d →
      ∀ x y : Fin m → Fin P, Function.Injective x → Function.Injective y →
        ∃ p ∈ π, ¬p ∣ T ∧
          Function.Injective (fun i => (((x i).val + 1 : ℕ) : ZMod p)) ∧
          Function.Injective (fun i => (((y i).val + 1 : ℕ) : ZMod p)) := by
  intro T hT0 hT x y hx hy
  have hinj (z : Fin m → Fin P) (hz : Function.Injective z) :
      Function.Injective (fun i => (z i).val + 1) := by
    intro i j hij
    exact hz (Fin.ext (Nat.add_right_cancel hij))
  have hbound (z : Fin m → Fin P) (i : Fin m) : (z i).val + 1 ≤ P := (z i).isLt
  obtain ⟨p, hp, hpT, hpx, hpy⟩ := exists_eligible_separating_prime
    hπ hT0 hT hbudget
    (fun i => (x i).val + 1) (fun i => (y i).val + 1)
    (hinj x hx) (hinj y hy) (hbound x) (hbound y)
  exact ⟨p, hp, hpT, positive_mod_injective x hpx, positive_mod_injective y hpy⟩


/-- A single explicitly constructed packet works for every original
pair of distinct blocks and every admissible type multiplier. -/
theorem exists_uniform_two_block_packet (M R m d P : ℕ) (hM : 0 < M)
    (hbudget : P ^ (d + 2 * m.choose 2) < M ^ R) :
    ∃ π : Finset ℕ, π.card = R ∧
      (∀ p ∈ π, p.Prime ∧ M < p ∧ p ≤ 2 ^ R * M) ∧
      (P ^ (d + 2 * m.choose 2) < ∏ p ∈ π, p) ∧
      ∀ T : ℕ, 0 < T → T ≤ P ^ d →
        ∀ x y : Fin m → Fin P, Function.Injective x → Function.Injective y →
          ∃ p ∈ π, ¬p ∣ T ∧
            Function.Injective (fun i => (((x i).val + 1 : ℕ) : ZMod p)) ∧
            Function.Injective (fun i => (((y i).val + 1 : ℕ) : ZMod p)) := by
  obtain ⟨π, hcard, hπ⟩ := exists_prime_packet M R hM
  have hprod : M ^ R ≤ ∏ p ∈ π, p := by
    rw [← hcard, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun p hp => (hπ p hp).2.1.le)
  have hb := hbudget.trans_le hprod
  refine ⟨π, hcard, hπ, hb, ?_⟩
  exact packet_separates_blocks (fun p hp => (hπ p hp).1) hb

end
end RiemannGaussian.VinogradovTwoBlockPacket
