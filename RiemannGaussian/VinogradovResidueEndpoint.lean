/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovEndpointDeletion

/-!
# The original residue tail reaches the required quotient endpoint

The existing quotient injection reconstructs every original residue entry.
Its explicit extra endpoint is paid using the proved mixed-count endpoint
bound. The remaining interval has length `floor(Q/p)` and a literal common
integer shift, ready for polynomial-row transport.
-/

namespace RiemannGaussian.VinogradovResidueEndpoint
noncomputable section
open scoped BigOperators Classical
open Polynomial MeasureTheory UnitAddTorus VinogradovMeanValue VinogradovShiftedMoment
open VinogradovPartitionEnergy VinogradovMomentPartition VinogradovLowDegreeTail
open VinogradovPolynomialNonsingular VinogradovResidueMoment VinogradovEndpointDeletion

/-- Use the original finite enumeration of the nonsingular block window. -/
local instance windowFintype (p m P : ℕ) : Fintype (Window p m P) := Fintype.ofFinite _
/-- The normalized Haar measure used by the actual count. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- Circle Haar measure has mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Every monomial-tail coordinate, including the inactive block rows. -/
def integerTail (m d : ℕ) (x : ℤ) : (Fin d ⊕ Fin m) → ℤ :=
  Sum.elim (fun i => x ^ (i.val + 1)) (fun i => x ^ (d + i.val + 1))

/-- The earlier finite tail is the full integer monomial vector. -/
theorem monomialTail_eq_integerTail (m d p q Q : ℕ) (x : Fin Q) :
    monomialTail m d p q Q x =
      integerTail m d (((p * q : ℕ) : ℤ) * ((x.val + 1 : ℕ) : ℤ)) := by
  funext i
  rcases i with i | i <;>
    simp only [monomialTail, integerTail, Sum.elim_inl, Sum.elim_inr, Nat.cast_add, Nat.cast_one]

/-- The exact affine tail at positive quotient entries. The shift
is retained even when the residue is zero. -/
def shiftedTail (m d p q xi : ℕ) (x : ℕ) : (Fin d ⊕ Fin m) → ℤ :=
  integerTail m d ((q : ℤ) * ((p : ℤ) * x + ((xi : ℤ) - p)))

/-- The quotient injection reconstructs the full original tail vector. -/
theorem residue_tail_reconstruction (m d p q xi Q : ℕ) (x : ResidueWindow p xi Q) :
    monomialTail m d 1 q Q x.val =
      shiftedTail m d p q xi ((residueQuotient x).val + 1) := by
  rw [monomialTail_eq_integerTail]
  simp only [shiftedTail, residue_reconstruction, Nat.one_mul]

/-- A field residue mask is exactly the original positive natural
residue window, with no extra endpoint yet introduced. -/
theorem class_polynomial {p : ℕ} [NeZero p] (m d Q q : ℕ) (c : ZMod p)
    (theta : UnitAddTorus (Fin d ⊕ Fin m)) :
    polynomial (monomialTail m d 1 q Q) (targetWeight tailResidue (fun _ => 1) c) theta =
      polynomial (fun x : ResidueWindow p c.val Q => monomialTail m d 1 q Q x.val)
        (fun _ => 1) theta := by
  have hc (x : Fin Q) : tailResidue (p := p) x = c ↔ (x.val + 1) % p = c.val := by
    constructor
    · intro he
      simpa only [tailResidue, ZMod.val_natCast] using congrArg ZMod.val he
    · intro he
      apply ZMod.val_injective p
      simpa only [tailResidue, ZMod.val_natCast] using he
  unfold polynomial
  simp only [targetWeight, ite_mul, one_mul, zero_mul, hc]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun x : Fin Q => (x.val + 1) % p = c.val))
    (by simp) (fun x : Fin Q => mFourier (monomialTail m d 1 q Q x) theta)]
  simp only [Finset.sum_filter]

/-- The original tail-class moment is its exact mixed residue-window
count, while the whole original block stays coupled to it. -/
theorem tailClassMoment_eq {p : ℕ} [NeZero p] (m d P Q q s : ℕ)
    (F : Fin m → ℤ[X]) (c : ZMod p) :
    tailClassMoment p m d P Q q s F c =
      VinogradovMixedMoments.mixedMoment 1 s (windowFrequency (p := p) (P := P) d F)
        (fun x : ResidueWindow p c.val Q => monomialTail m d 1 q Q x.val) := by
  unfold tailClassMoment VinogradovMixedMoments.mixedMoment
  simp only [mul_one, class_polynomial]

/-- Completing the quotient window costs no estimate yet; the
full mixed count pays the literal extra endpoint `floor(Q/p)+1`. -/
theorem tailClassMoment_le_quotient {p : ℕ} [NeZero p] (m d P Q q s : ℕ)
    (F : Fin m → ℤ[X]) (c : ZMod p) :
    tailClassMoment p m d P Q q s F c ≤
      VinogradovMixedMoments.mixedMoment 1 s (windowFrequency (p := p) (P := P) d F)
        (fun x : Fin (Q / p + 1) => shiftedTail m d p q c.val (x.val + 1)) := by
  rw [tailClassMoment_eq]
  have he := mixedMoment_map_le 1 s (windowFrequency (p := p) (P := P) d F)
    (fun x : Fin (Q / p + 1) => shiftedTail m d p q c.val (x.val + 1))
    (residueQuotient (q := p) (xi := c.val) (X := Q)) residueQuotient_injective
  simpa only [residue_tail_reconstruction] using he

/-- The possible extra endpoint is paid with the explicit factor two.
The resulting tail has precisely the required `floor(Q/p)` entries. -/
theorem tailClassMoment_le_floor {p s : ℕ} [NeZero p]
    (hs : 1 ≤ s) (m d P Q q : ℕ) (hQ : 16 * s ^ 2 ≤ Q / p)
    (F : Fin m → ℤ[X]) (c : ZMod p) :
    tailClassMoment p m d P Q q s F c ≤
      2 * VinogradovMixedMoments.mixedMoment 1 s (windowFrequency (p := p) (P := P) d F)
        (fun x : Fin (Q / p) => shiftedTail m d p q c.val (x.val + 1)) :=
  (tailClassMoment_le_quotient m d P Q q s F c).trans
    (mixedMoment_succ_le hs hQ 1 (windowFrequency (p := p) (P := P) d F)
      (shiftedTail m d p q c.val))

/-- The actual original nonsingular count reaches a shifted dilated
tail at the required endpoint, with every conditioning and boundary
factor proved. No analytic estimate is a premise. -/
theorem exists_floor_tail_bound {p d s : ℕ} [Fact p.Prime]
    (hdp : d < p) (hds : d ≤ s) (hs : 1 ≤ s)
    (m P Q q : ℕ) (hq : 0 < q) (hQ : 16 * s ^ 2 ≤ Q / p) (F : Fin m → ℤ[X]) :
    ∃ xi : ℕ, xi < p ∧
      (nonsingularCount p m d P s F (monomialTail m d 1 q Q) : ℝ) ≤
        ((2 * d.factorial * p ^ (2 * s - d) : ℕ) : ℝ) *
          VinogradovMixedMoments.mixedMoment 1 s (windowFrequency (p := p) (P := P) d F)
            (fun x : Fin (Q / p) => shiftedTail m d p q xi (x.val + 1)) := by
  obtain ⟨c, hc⟩ := exists_tail_class_bound hdp hds hs m P Q q hq F
  refine ⟨c.val, ZMod.val_lt c, ?_⟩
  have he := hc.trans (mul_le_mul_of_nonneg_left (tailClassMoment_le_floor hs m d P Q q hQ F c)
    (Nat.cast_nonneg _))
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc, mul_left_comm] using he

/-- The usual prime-packet size conditions pay the integer endpoint
threshold with no extra rounding allowance. -/
theorem floor_condition_of_packet {p M Q s : ℕ} (hp : 0 < p)
    (hpM : p ≤ 2 * M) (hQ : 32 * s ^ 2 * M ≤ Q) : 16 * s ^ 2 ≤ Q / p := by
  apply (Nat.le_div_iff_mul_le hp).mpr
  calc
    16 * s ^ 2 * p ≤ 16 * s ^ 2 * (2 * M) := Nat.mul_le_mul_left _ hpM
    _ = 32 * s ^ 2 * M := by ring
    _ ≤ Q := hQ

end
end RiemannGaussian.VinogradovResidueEndpoint
