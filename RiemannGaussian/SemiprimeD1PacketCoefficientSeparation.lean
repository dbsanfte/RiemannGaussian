/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1GlobalModeFamilies
import RiemannGaussian.SemiprimeD1PartialCoefficient
import RiemannGaussian.SemiprimeD1PacketPolynomialAcquired

/-! # Actual global requested coefficient factors into executed packet queries
Unique ownership is derived from original acquired slot/route data. The right
side executes the concrete coefficient recurrence on actual recipe lists with
the actual computed restricted beta. No full polynomial or coefficient oracle
is a runtime input. Global original-row and child-assignment transport are
separate from this exact coefficient identity.
-/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace RiemannGaussian.SemiprimeD1PacketCoefficientSeparation
open scoped BigOperators
open SemiprimeD1GlobalModeOwners SemiprimeD1GlobalModeFibres SemiprimeD1GlobalModeFamilies
open SemiprimeD1SeparatedCoefficient SemiprimeD1PacketEntryInputs SemiprimeD1JetAxes
open SemiprimeD1JetInterpretation
noncomputable section

/-- Original acquired queries have the FULL actual global catalogue length,
including empty inventories; no selected packet is needed to prove the length. -/
theorem original_query_length (n F r a u p : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a) (beta : List ℕ)
    (hb : beta ∈ (node n F r a u p arity owner i).modes.values) :
    beta.length = (modes n F r a (cutoff n F r a u p arity owner i) arity owner i).length := by
  have h := ((SemiprimeD1OriginalModeAcquisition.modes_correct n F r a u i.val p arity owner beta).1.mp hb).1
  simp only [SemiprimeD1ModeCatalog.weights, List.length_map] at h
  have hc : cutoff n F r a u p arity owner i =
      SemiprimeD1ModeRate.modeBudget (SemiprimeD1CollisionOriginal.ports n F a arity).length u a i.val p := by
    unfold cutoff
    rw [SemiprimeD1OriginalModeAcquisition.precision_original]
    rfl
  rw [← hc] at h
  exact h

/-- The coefficient of the product of ACTUAL packet/group recipe polynomials is
the product of the ACTUALLY EXECUTED restricted-query recurrence outputs. -/
theorem coefficient_separation (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (n F r a u p : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (columns rows : (Fin (original n F r a arity owner).state.packets.length × Fin r) → List (Wire a))
    (beta : List ℕ) (hpos : ctx.Positive)
    (hlen : beta.length ≤ (modes n F r a (cutoff n F r a u p arity owner i) arity owner i).length) :
    let cache := fun fg : Fin (original n F r a arity owner).state.packets.length × Fin r =>
      SemiprimeD1PacketModeMask.fromModes (node n F r a u p arity owner i) fg.1 i fg.2
    (∏ fg, SemiprimeD1PacketPolynomialAcquired.polynomial ctx z a i t (columns fg) (rows fg) (cache fg)).coeff
      beta.toFinsupp =
      ∏ fg, interpret ctx (SemiprimeD1JetAffineCoefficient.evaluate ctx (cache fg).items.length
        (SemiprimeD1PacketEntryBits.recipes ctx z a i t (columns fg) (cache fg).items (rows fg)).value
        (SemiprimeD1PacketModeMask.restrict (cache fg) beta).value).words := by
  let G := Fin (original n F r a arity owner).state.packets.length × Fin r
  let cache := fun fg : G =>
    SemiprimeD1PacketModeMask.fromModes (node n F r a u p arity owner i) fg.1 i fg.2
  let Q := fun fg : G => SemiprimeD1PacketPolynomialAcquired.polynomial ctx z a i t
    (columns fg) (rows fg) (cache fg)
  let family := targetFamily n F r a u p arity owner i
  have hon : ∀ fg : G, On {j | family j = some fg} (Q fg) := by
    intro fg
    have hs : {j | family j = some fg} = SemiprimeD1PacketModeProjection.targetSet (cache fg) :=
      (target_set n F r a u p arity owner i fg.1 fg.2).symm
    rw [hs]
    exact SemiprimeD1PacketPolynomialSupport.packet_polynomial_on ctx z a i t (columns fg) (rows fg) (cache fg)
  have hzero : ∀ j, family j = none → beta.toFinsupp j = 0 := by
    intro j hj
    by_cases hlt : j < (modes n F r a (cutoff n F r a u p arity owner i) arity owner i).length
    · simp only [family, targetFamily, hlt, dite_true, reduceCtorEq] at hj
    · exact List.toFinsupp_apply_le beta j (hlen.trans (Nat.le_of_not_gt hlt))
  have hc := SemiprimeD1PartialCoefficient.coefficient_optional family Q hon beta.toFinsupp hzero
  refine hc.trans ?_
  apply Finset.prod_congr rfl
  intro fg _
  have hs : {j | family j = some fg} = SemiprimeD1PacketModeProjection.targetSet (cache fg) :=
    (target_set n F r a u p arity owner i fg.1 fg.2).symm
  rw [hs]
  have he := SemiprimeD1JetAffineCoefficient.evaluate_coefficient ctx (cache fg).items.length
    (SemiprimeD1PacketEntryBits.recipes ctx z a i t (columns fg) (cache fg).items (rows fg)).value
    (SemiprimeD1PacketModeMask.restrict (cache fg) beta).value hpos
  rw [SemiprimeD1PacketModeProjection.restrict_toFinsupp] at he
  exact he.symm

/-- ACTUAL acquired-menu membership discharges all ambient absent-index conditions. -/
theorem original_coefficient_separation (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (n F r a u p : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (columns rows : (Fin (original n F r a arity owner).state.packets.length × Fin r) → List (Wire a))
    (beta : List ℕ) (hpos : ctx.Positive)
    (hb : beta ∈ (node n F r a u p arity owner i).modes.values) :
    let cache := fun fg : Fin (original n F r a arity owner).state.packets.length × Fin r =>
      SemiprimeD1PacketModeMask.fromModes (node n F r a u p arity owner i) fg.1 i fg.2
    (∏ fg, SemiprimeD1PacketPolynomialAcquired.polynomial ctx z a i t (columns fg) (rows fg) (cache fg)).coeff
      beta.toFinsupp =
      ∏ fg, interpret ctx (SemiprimeD1JetAffineCoefficient.evaluate ctx (cache fg).items.length
        (SemiprimeD1PacketEntryBits.recipes ctx z a i t (columns fg) (cache fg).items (rows fg)).value
        (SemiprimeD1PacketModeMask.restrict (cache fg) beta).value).words :=
  coefficient_separation ctx z n F r a u p arity owner i t columns rows beta hpos
    (original_query_length n F r a u p arity owner i beta hb).le

end
end RiemannGaussian.SemiprimeD1PacketCoefficientSeparation
