/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovInitialExceptional
import RiemannGaussian.VinogradovPrimePacket

/-!
# A prime carrying a fixed share of the original mean value

The uniform prime packet covers all retained original solutions. A finite
pigeonhole argument finds one actual prime with J_r<=2R*D_p. Every tuple,
selected position and complete frequency constraint is unchanged; there is
no supplied mean-value budget or independent choice of prime per solution.
-/

namespace RiemannGaussian.VinogradovInitialPrimeTransfer
noncomputable section
open scoped Classical BigOperators
open VinogradovMeanValue VinogradovShiftedMoment VinogradovInitialExceptional
open VinogradovPrimePacket
/-- Original full collisions whose selected left entries stay distinct modulo the chosen prime. -/
def separatedCount {ι d : Type*} [Fintype ι] {k : ℕ} (n : ι → ℕ) (s : ℕ) (v : ι → d → ℤ)
    (e : Fin k ↪ Fin (s + 2)) (p : ℕ) : ℕ :=
  (Finset.univ.filter (fun xy : (Fin (s + 2) → ι) × (Fin (s + 2) → ι) =>
    Function.Injective (fun j => n (xy.1 (e j)) % p) ∧
    tupleFrequency (s + 2) v xy.1 = tupleFrequency (s + 2) v xy.2)).card
/-- A single packet covering every distinct original block covers every full distinct-block collision. -/
theorem distinctCount_le_separated_sum {ι d : Type*} [Fintype ι] {k : ℕ} (n : ι → ℕ) (s : ℕ)
    (v : ι → d → ℤ) (e : Fin k ↪ Fin (s + 2)) (P : Finset ℕ)
    (hcover : ∀ x : Fin k → ι, Function.Injective x →
      ∃ p ∈ P, Function.Injective (fun j => n (x j) % p)) :
    distinctCount s v e ≤ ∑ p ∈ P, separatedCount n s v e p := by
  let S (p : ℕ) := Finset.univ.filter
    (fun xy : (Fin (s + 2) → ι) × (Fin (s + 2) → ι) =>
      Function.Injective (fun j => n (xy.1 (e j)) % p) ∧
      tupleFrequency (s + 2) v xy.1 = tupleFrequency (s + 2) v xy.2)
  have hs : Finset.univ.filter
      (fun xy : (Fin (s + 2) → ι) × (Fin (s + 2) → ι) =>
        Function.Injective (xy.1 ∘ e) ∧
        tupleFrequency (s + 2) v xy.1 = tupleFrequency (s + 2) v xy.2) ⊆ P.biUnion S := by
    intro xy hxy
    have hx := (Finset.mem_filter.mp hxy).2
    obtain ⟨p, hp, hmod⟩ := hcover (xy.1 ∘ e) hx.1
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmod, hx.2⟩⟩
  exact (Finset.card_le_card hs).trans Finset.card_biUnion_le
/-- The separated count on the literal positive interval 1 through X. -/
def intervalSeparatedCount {d : Type*} {X k : ℕ} (s : ℕ) (v : Fin X → d → ℤ)
    (e : Fin k ↪ Fin (s + 2)) (p : ℕ) : ℕ :=
  separatedCount (fun x : Fin X => x.val + 1) s v e p
/-- One explicit finite prime packet carries the full moment up to the proved factor two, uniformly over every original frequency family and selected block. -/
theorem exists_uniform_prime_moment_transfer {d : Type*} [Fintype d]
    (M R k X : ℕ) (hM : 0 < M) (hbudget : X ^ (k * (k - 1)) < M ^ R)
    (hsize : 4 * k ^ 4 ≤ X) :
    ∃ P : Finset ℕ, P.card = R ∧
      (∀ p ∈ P, p.Prime ∧ M < p ∧ p ≤ 2 ^ R * M) ∧
      ∀ s (v : Fin X → d → ℤ) (e : Fin k ↪ Fin (s + 2)),
        moment (s + 2) v ≤ 2 * ∑ p ∈ P, (intervalSeparatedCount s v e p : ℝ) := by
  obtain ⟨P, hcard, hP, hsep⟩ := exists_uniform_separating_packet M R k X hM hbudget
  have hcover (x : Fin k → Fin X) (hx : Function.Injective x) :
      ∃ p ∈ P, Function.Injective (fun j => ((x j).val + 1) % p) := by
    apply hsep (fun j => (x j).val + 1)
    · intro i j hij
      apply hx
      apply Fin.ext
      exact Nat.add_right_cancel hij
    · intro j
      have hj := (x j).isLt
      omega
  refine ⟨P, hcard, hP, ?_⟩
  intro s v e
  have hJ := moment_le_twice_distinctCount s v e (by simpa using hsize)
  have hcount : (distinctCount s v e : ℝ) ≤ ∑ p ∈ P, (intervalSeparatedCount s v e p : ℝ) := by
    exact_mod_cast distinctCount_le_separated_sum (fun x : Fin X => x.val + 1) s v e P hcover
  exact hJ.trans (mul_le_mul_of_nonneg_left hcount (by norm_num))
/-- At least one prime in an explicit interval carries a fixed share of the actual full moment; neither an upper moment estimate nor a prime-counting estimate is assumed. -/
theorem exists_prime_carrying_moment {d : Type*} [Fintype d]
    (M R k X s : ℕ) (v : Fin X → d → ℤ) (e : Fin k ↪ Fin (s + 2))
    (hM : 0 < M) (hR : 0 < R) (hbudget : X ^ (k * (k - 1)) < M ^ R)
    (hsize : 4 * k ^ 4 ≤ X) :
    ∃ p : ℕ, p.Prime ∧ M < p ∧ p ≤ 2 ^ R * M ∧
      moment (s + 2) v ≤ 2 * (R : ℝ) * (intervalSeparatedCount s v e p : ℝ) := by
  obtain ⟨P, hcard, hP, htransfer⟩ := exists_uniform_prime_moment_transfer
    (d := d) M R k X hM hbudget hsize
  have hn : P.Nonempty := Finset.card_pos.mp (hcard ▸ hR)
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image P (intervalSeparatedCount s v e) hn
  have hsum : (∑ q ∈ P, intervalSeparatedCount s v e q) ≤ R * intervalSeparatedCount s v e p := by
    calc
      _ ≤ ∑ _q ∈ P, intervalSeparatedCount s v e p := Finset.sum_le_sum (fun q hq => hmax q hq)
      _ = _ := by simp [hcard]
  have hsumR : (∑ q ∈ P, (intervalSeparatedCount s v e q : ℝ)) ≤
      (R : ℝ) * (intervalSeparatedCount s v e p : ℝ) := by exact_mod_cast hsum
  refine ⟨p, (hP p hp).1, (hP p hp).2.1, (hP p hp).2.2, ?_⟩
  have hbound := (htransfer s v e).trans (mul_le_mul_of_nonneg_left hsumR (by norm_num))
  simpa only [mul_assoc] using hbound
end
end RiemannGaussian.VinogradovInitialPrimeTransfer
