/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovAffineMoment

/-!
# Actual residue-window tail moments

Integer quotient reconstruction preserves the entire finite positive residue
window. Its exact moment and complex weighted Gram coefficient retain that
support before embedding into the normalized interval with its explicit extra
endpoint. All shifted target counts and bounded complex coefficients then
receive the literal normalized Vinogradov mean value. This bounds the actual
tail completions of each fixed pair of weighted moment blocks.
-/

namespace RiemannGaussian.VinogradovResidueMoment
noncomputable section
open scoped BigOperators

/-- Restricting the frequency index family along an injection cannot
increase any fixed difference count. The full frequency shift is unchanged. -/
theorem differenceCount_map_le {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]
    (f : ι → κ) (hf : Function.Injective f) (v : κ → d → ℤ) (h : d → ℤ) :
    VinogradovShiftedMoment.differenceCount (fun i => v (f i)) h ≤
      VinogradovShiftedMoment.differenceCount v h := by
  classical
  unfold VinogradovShiftedMoment.differenceCount
  apply Finset.card_le_card_of_injOn (fun xy => (f xy.1, f xy.2))
  · intro xy hxy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hxy).2⟩
  · intro xy hxy uv huv he
    exact Prod.ext (hf (congrArg Prod.fst he)) (hf (congrArg Prod.snd he))

/-- Positive integer entries up to X in a fixed natural residue class. -/
abbrev ResidueWindow (q xi X : ℕ) := {n : Fin X // (n.val + 1) % q = xi}

/-- Every actual residue-window quotient lies in the explicit normalized
range 0,...,floor(X/q), including endpoint rounding. -/
def residueQuotient {q xi X : ℕ} (x : ResidueWindow q xi X) : Fin (X / q + 1) :=
  ⟨(x.val.val + 1) / q, by
    have h := Nat.div_le_div_right (show x.val.val + 1 ≤ X by omega) (c := q)
    omega⟩

/-- The quotient map is injective on the original residue window. -/
theorem residueQuotient_injective {q xi X : ℕ} :
    Function.Injective (residueQuotient (q := q) (xi := xi) (X := X)) := by
  intro x y hxy
  apply Subtype.ext
  apply Fin.ext
  have hq := congrArg Fin.val hxy
  change (x.val.val + 1) / q = (y.val.val + 1) / q at hq
  have hx := Nat.mod_add_div (x.val.val + 1) q
  have hy := Nat.mod_add_div (y.val.val + 1) q
  rw [x.property, hq] at hx
  rw [y.property] at hy
  omega

/-- The affine progression reconstructs the exact original positive
integer, including both the residue offset and the initial-index shift. -/
theorem residue_reconstruction {q xi X : ℕ} (x : ResidueWindow q xi X) :
    (q : ℤ) * (((residueQuotient x).val + 1 : ℕ) : ℤ) + ((xi : ℤ) - q) =
      ((x.val.val + 1 : ℕ) : ℤ) := by
  have hn := Nat.mod_add_div (x.val.val + 1) q
  rw [x.property] at hn
  have hz : (xi : ℤ) + (q : ℤ) * (residueQuotient x).val =
      ((x.val.val + 1 : ℕ) : ℤ) := by exact_mod_cast hn
  push_cast
  push_cast at hz
  linarith

/-- The literal power vector of every residue-window entry is exactly
its affine progression vector at the normalized quotient. -/
theorem residue_frequency {q xi X : ℕ} (k : ℕ) (x : ResidueWindow q xi X) :
    VinogradovMeanValue.monomialFrequency k (x.val.val + 1) =
      VinogradovPowerSumRigidity.integerFrequency k
        ((q : ℤ) * (((residueQuotient x).val + 1 : ℕ) : ℤ) + ((xi : ℤ) - q)) := by
  rw [residue_reconstruction]
  rfl

/-- Before enlarging the normalized support to an interval, the exact
moment retains every original residue-window index and its quotient. -/
theorem residue_moment_eq_quotient {q xi X : ℕ} (hq : q ≠ 0) (r k : ℕ) :
    VinogradovMeanValue.moment r
      (fun n : ResidueWindow q xi X => VinogradovMeanValue.monomialFrequency k (n.val.val + 1)) =
    VinogradovMeanValue.moment r
      (fun n : ResidueWindow q xi X => VinogradovPowerSumRigidity.integerFrequency k
        (((residueQuotient n).val + 1 : ℕ) : ℤ)) := by
  have hqz : (q : ℤ) ≠ 0 := by exact_mod_cast hq
  simp only [residue_frequency]
  exact VinogradovAffineMoment.moment_affine r k _ hqz ((xi : ℤ) - q)

/-- Every complete shifted tail system in the actual positive residue
window is bounded by the literal normalized mean value. The extra endpoint
in floor(X/q)+1 is explicit, and the full shift vector is retained. -/
theorem residue_window_shift_le_meanValue {q xi X : ℕ} (hq : q ≠ 0)
    (r k : ℕ) (h : Fin k → ℤ) :
    (VinogradovShiftedMoment.differenceCount
      (VinogradovShiftedMoment.tupleFrequency r
        (fun n : ResidueWindow q xi X =>
          VinogradovMeanValue.monomialFrequency k (n.val.val + 1))) h : ℝ) ≤
      VinogradovMeanValue.meanValue r k (X / q + 1) := by
  classical
  let v (i : Fin (X / q + 1)) := VinogradovPowerSumRigidity.integerFrequency k
    ((q : ℤ) * ((i.val + 1 : ℕ) : ℤ) + ((xi : ℤ) - q))
  let f (x : Fin r → ResidueWindow q xi X) := fun j => residueQuotient (x j)
  have hf : Function.Injective f := by
    intro x y hxy
    funext j
    exact residueQuotient_injective (congrFun hxy j)
  have hb := differenceCount_map_le f hf (VinogradovShiftedMoment.tupleFrequency r v) h
  have hsource : (fun x : Fin r → ResidueWindow q xi X =>
      VinogradovShiftedMoment.tupleFrequency r v (f x)) =
      VinogradovShiftedMoment.tupleFrequency r
        (fun n : ResidueWindow q xi X =>
          VinogradovMeanValue.monomialFrequency k (n.val.val + 1)) := by
    funext x
    simp only [VinogradovShiftedMoment.tupleFrequency, f, v, ← residue_frequency]
  rw [hsource] at hb
  have hreal : (VinogradovShiftedMoment.differenceCount
      (VinogradovShiftedMoment.tupleFrequency r
        (fun n : ResidueWindow q xi X =>
          VinogradovMeanValue.monomialFrequency k (n.val.val + 1))) h : ℝ) ≤
      VinogradovShiftedMoment.differenceCount (VinogradovShiftedMoment.tupleFrequency r v) h := by
    exact_mod_cast hb
  exact hreal.trans (VinogradovAffineMoment.affine_shift_le_meanValue r k (X / q + 1)
    (by exact_mod_cast hq) ((xi : ℤ) - q) h)

/-- The residue-window support retains all complex tuple products in
its exact normalized homogeneous Gram coefficient. -/
theorem residue_weighted_gram_eq_quotient {q xi X : ℕ} (hq : q ≠ 0) (r k : ℕ)
    (w : ResidueWindow q xi X → ℂ) :
    VinogradovShiftedMoment.weightedShift
      (VinogradovShiftedMoment.tupleFrequency r
        (fun n : ResidueWindow q xi X => VinogradovMeanValue.monomialFrequency k (n.val.val + 1)))
      (VinogradovShiftedMoment.tupleWeight r w) 0 =
    VinogradovShiftedMoment.weightedShift
      (VinogradovShiftedMoment.tupleFrequency r
        (fun n : ResidueWindow q xi X => VinogradovPowerSumRigidity.integerFrequency k
          (((residueQuotient n).val + 1 : ℕ) : ℤ)))
      (VinogradovShiftedMoment.tupleWeight r w) 0 := by
  simp only [residue_frequency]
  exact VinogradovAffineMoment.weighted_gram_affine r k _ w
    (by exact_mod_cast hq) ((xi : ℤ) - q)

/-- All bounded complex weight families on the actual residue window
satisfy the normalized shifted coefficient bound, uniformly in the target. -/
theorem residue_weighted_shift_le_meanValue {q xi X : ℕ} (hq : q ≠ 0) (r k : ℕ)
    (w : ResidueWindow q xi X → ℂ) (hw : ∀ i, ‖w i‖ ≤ 1) (h : Fin k → ℤ) :
    ‖VinogradovShiftedMoment.weightedShift
      (VinogradovShiftedMoment.tupleFrequency r
        (fun n : ResidueWindow q xi X => VinogradovMeanValue.monomialFrequency k (n.val.val + 1)))
      (VinogradovShiftedMoment.tupleWeight r w) h‖ ≤
      VinogradovMeanValue.meanValue r k (X / q + 1) :=
  (VinogradovShiftedMoment.weightedShift_norm_le_count _ _
    (VinogradovShiftedMoment.tupleWeight_norm_le_one r w hw) h).trans
      (residue_window_shift_le_meanValue hq r k h)

/-- Canonical natural residues agree with the literal integer
coarse-class divisibility, including negative residue representatives. -/
theorem residue_mod_iff_dvd_sub {q : ℕ} [NeZero q] (eta : ℤ) (n : ℕ) :
    n % q = (eta : ZMod q).val ↔ (q : ℤ) ∣ (n : ℤ) - eta := by
  constructor
  · intro h
    have he : (n : ZMod q) = (eta : ZMod q) :=
      ZMod.val_injective q (by simpa only [ZMod.val_natCast] using h)
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ q).mp
    simpa only [Int.cast_natCast] using he.symm
  · intro h
    have he := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ q).mpr h
    simpa only [Int.cast_natCast, ZMod.val_natCast] using (congrArg ZMod.val he).symm

/-- For every fixed pair of weighted blocks, the original complete
moment equations have at most the normalized mean value of tail completions
inside the actual finite positive residue window. -/
theorem tail_completions_le_meanValue {q xi X : ℕ} (hq : q ≠ 0) (r k : ℕ)
    (c x y : Fin k → ℤ) :
    ((Finset.univ.filter (fun vw :
        (Fin r → ResidueWindow q xi X) × (Fin r → ResidueWindow q xi X) =>
      ∀ i : Fin k,
        (∑ j, c j * x j ^ (i.val + 1)) +
          (∑ j, ((vw.1 j).val.val + 1 : ℤ) ^ (i.val + 1)) =
        (∑ j, c j * y j ^ (i.val + 1)) +
          ∑ j, ((vw.2 j).val.val + 1 : ℤ) ^ (i.val + 1))).card : ℝ) ≤
      VinogradovMeanValue.meanValue r k (X / q + 1) := by
  classical
  let h (i : Fin k) := (∑ j, c j * y j ^ (i.val + 1)) - ∑ j, c j * x j ^ (i.val + 1)
  have he (vw : (Fin r → ResidueWindow q xi X) × (Fin r → ResidueWindow q xi X)) :
      (∀ i : Fin k,
        (∑ j, c j * x j ^ (i.val + 1)) +
          (∑ j, ((vw.1 j).val.val + 1 : ℤ) ^ (i.val + 1)) =
        (∑ j, c j * y j ^ (i.val + 1)) +
          ∑ j, ((vw.2 j).val.val + 1 : ℤ) ^ (i.val + 1)) ↔
      VinogradovShiftedMoment.tupleFrequency r
        (fun n : ResidueWindow q xi X => VinogradovMeanValue.monomialFrequency k (n.val.val + 1)) vw.1 =
      VinogradovShiftedMoment.tupleFrequency r
        (fun n : ResidueWindow q xi X => VinogradovMeanValue.monomialFrequency k (n.val.val + 1)) vw.2 + h := by
    constructor
    · intro hvw
      funext i
      simp only [VinogradovShiftedMoment.tupleFrequency, Finset.sum_apply, Pi.add_apply,
        VinogradovMeanValue.monomialFrequency, Nat.cast_add, Nat.cast_one, h]
      linarith [hvw i]
    · intro hvw i
      have hi := congrFun hvw i
      simp only [VinogradovShiftedMoment.tupleFrequency, Finset.sum_apply, Pi.add_apply,
        VinogradovMeanValue.monomialFrequency, Nat.cast_add, Nat.cast_one, h] at hi
      linarith
  have hb := residue_window_shift_le_meanValue (xi := xi) (X := X) hq r k h
  simpa only [VinogradovShiftedMoment.differenceCount, ← he] using hb

end
end RiemannGaussian.VinogradovResidueMoment
