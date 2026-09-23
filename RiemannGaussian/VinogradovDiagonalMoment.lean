/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovUnrestrictedConditioning

/-!
# A direct moment-order step from the exact diagonal branch

The original monomial mixed count is exactly J_{s+k,k}. An eligible
prime above the k-th root of the original endpoint makes the conditioned
residue moment exactly diagonal. The unrestricted conditioning theorem
therefore gives a numerical recurrence for actual homogeneous moments,
with all repeated-tuple, prime-packet and tail-endpoint costs paid.
-/

namespace RiemannGaussian.VinogradovDiagonalMoment
noncomputable section
open scoped BigOperators Classical
open Polynomial MeasureTheory UnitAddTorus VinogradovMeanValue VinogradovPartitionEnergy
open VinogradovPolynomialSystems VinogradovPolynomialDifferencing
open VinogradovTypeMaximum VinogradovPolynomialNonsingular
open VinogradovMixedMoments VinogradovMixedDifferencing VinogradovNonsingularDescent

/-- The original normalized Haar measure. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The circle Haar measure has total mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The original monomials form the initial polynomial system. -/
def monomialSystem (k : ℕ) (j : Fin k) : ℤ[X] := X ^ (j.val + 1)

/-- The initial system has exact type (0,1) and binary exponent zero. -/
theorem monomialSystem_hasType (k : ℕ) : HasType (monomialSystem k) 0 1 0 := by
  intro j
  simp [monomialSystem]

/-- Equal original frequency maps add their tuple orders in the actual integral. -/
theorem mixedMoment_self {ι a : Type*} [Fintype ι] [Fintype a]
    (m s : ℕ) (v : ι → a → ℤ) : mixedMoment m s v v = moment (m + s) v := by
  unfold mixedMoment moment
  simp only [polynomial, one_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [← pow_add]
  congr 1
  omega

/-- The initial block and the original undilated monomial tail agree coordinatewise. -/
theorem initial_frequency (k P : ℕ) :
    (fun x : Fin P => fullFrequency 0 (monomialSystem k) (x.val + 1)) =
      monomialTail k 0 1 1 P := by
  funext x j
  rcases j with j | j
  · exact Fin.elim0 j
  · simp [fullFrequency, monomialSystem, monomialTail]

/-- No auxiliary model is introduced: the initial type count is exactly the next homogeneous moment. -/
theorem initial_count_eq (k s P : ℕ) :
    (typeCount 0 P s (monomialSystem k) (monomialTail k 0 1 1 P) : ℝ) =
      meanValue (s + k) k P := by
  rw [typeCount_eq_mixedMoment, initial_frequency, mixedMoment_self,
    monomialTail_moment _ _ _ _ _ _ (by norm_num) (by norm_num)]
  simp only [Nat.zero_add, Nat.add_comm k s]

/-- An arbitrary proved prime packet feeds the exact diagonal
homogeneous moment step, retaining its cardinality and actual width. -/
theorem exists_diagonal_moment_step_of_packet {k s P M U : ℕ}
    (hk : 2 ≤ k) (hP : 4 * k ^ 4 ≤ P) (hM : k ≤ M)
    (π : Finset ℕ) (hπ : ∀ p ∈ π, p.Prime ∧ M < p ∧ p ≤ U)
    (hbudget : P ^ (2 * k.choose 2) < ∏ p ∈ π, p)
    (hroot : P < (M + 1) ^ k) (hs : 1 ≤ s)
    (hQ : 16 * s ^ 2 * U ≤ P) :
    ∃ p : ℕ, p.Prime ∧ M < p ∧ p ≤ U ∧
      meanValue (s + k) k P ≤
        ((4 * π.card * k.factorial : ℕ) : ℝ) *
          (p : ℝ) ^ (2 * s + k * (k - 1) / 2) * (P : ℝ) ^ k *
            meanValue s k (P / p) := by
  obtain ⟨e', p, xi, hp, G, hG, hpM, hpU, hpT, hxi, hcount⟩ :=
    VinogradovUnrestrictedConditioning.exists_conditioning_of_packet (monomialSystem_hasType k)
      hk hP (by simpa only [Nat.zero_add] using hM) (by norm_num) (by simp) π hπ
      (by simpa only [Nat.zero_add] using hbudget) (by omega : 1 ≤ k)
      (by omega : k ≤ 0 + k) (by omega : 0 ≤ s) hs (by norm_num : 0 < 1) hQ
  have hpk : P < p ^ k :=
    hroot.trans_le (Nat.pow_le_pow_left (by omega : M + 1 ≤ p) k)
  rw [initial_count_eq,
    residueMixedMoment_eq_diagonal k s P (p ^ k) (pow_pos hp.pos k) hpk,
    monomialTail_moment _ _ _ _ _ _ hp.pos (by norm_num)] at hcount
  refine ⟨p, hp, hpM, hpU, ?_⟩
  convert hcount using 1
  simp only [Nat.zero_add, Nat.sub_zero, Nat.factorial_zero, mul_one,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
  ring


/-- One original prime and its literal quotient endpoint give the direct
J_{s,k} to J_{s+k,k} step. The conditioned block is exactly diagonal;
no lower-degree count or moment estimate is assumed. -/
theorem exists_diagonal_moment_step {k s P M R : ℕ}
    (hk : 2 ≤ k) (hP : 4 * k ^ 4 ≤ P) (hM : k ≤ M)
    (hbudget : P ^ (2 * k.choose 2) < M ^ R)
    (hroot : P < (M + 1) ^ k) (hs : 1 ≤ s)
    (hQ : 16 * s ^ 2 * (2 ^ R * M) ≤ P) :
    ∃ p : ℕ, p.Prime ∧ M < p ∧ p ≤ 2 ^ R * M ∧
      meanValue (s + k) k P ≤
        ((4 * R * k.factorial : ℕ) : ℝ) *
          (p : ℝ) ^ (2 * s + k * (k - 1) / 2) * (P : ℝ) ^ k *
            meanValue s k (P / p) := by
  obtain ⟨π, hcard, hπ, hprod, _⟩ :=
    VinogradovTwoBlockPacket.exists_uniform_two_block_packet M R k 0 P
      (by omega : 0 < M) (by simpa only [Nat.zero_add] using hbudget)
  simpa only [hcard] using exists_diagonal_moment_step_of_packet hk hP hM π hπ
    (by simpa only [Nat.zero_add] using hprod) hroot hs hQ

end
end RiemannGaussian.VinogradovDiagonalMoment
