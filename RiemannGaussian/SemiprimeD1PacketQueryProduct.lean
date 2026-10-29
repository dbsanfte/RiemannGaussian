/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketCoefficientSeparation
import RiemannGaussian.SemiprimeD1PacketRowProducts
import RiemannGaussian.SemiprimeD1PacketSourceProductValues
import RiemannGaussian.SemiprimeD1PacketEntryPolynomial

/-! # The complete actual packet product uses the original acquired query menu
This joins coefficient cancellation, actual target ownership and actual source
ownership for the same acquired packet family. Polynomials and finite sums are
erased specifications of the actual coefficient queries, never runtime inputs.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1PacketQueryProduct
open scoped BigOperators
open SemiprimeD1JetAxes SemiprimeD1JetInterpretation
open SemiprimeD1GlobalModeOwners SemiprimeD1GlobalModeFibres SemiprimeD1GlobalModeFamilies
open SemiprimeD1PacketRowProducts SemiprimeD1PacketPolynomialAcquired
open SemiprimeD1PacketPolynomialWeight SemiprimeD1PacketModeProjection
open SemiprimeD1SeparatedCoefficient SemiprimeD1WeightedPolynomial
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SemiprimeD1PacketReplayOriginal.acquire SemiprimeD1ChildGraph.acquire

/-- Unique optional ownership suffices even for an empty actual packet
inventory. No fictional owner is installed for absent catalogue indices. -/
theorem source_optional {G R : Type*} [Fintype G] [CommMonoid R]
    (family : ℕ → Option G) (e : ℕ →₀ ℕ) (values : ℕ → R)
    (hz : ∀ j, family j = none → e j = 0) :
    (∏ g, e.prod (fun j n => if family j = some g then values j ^ n else 1)) =
      e.prod (fun j n => values j ^ n) := by
  classical
  unfold Finsupp.prod
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j hj
  cases hf : family j with
  | none => exact False.elim ((Finsupp.mem_support_iff.mp hj) (hz j hf))
  | some g =>
    simpa only [hf,Option.some.injEq] using
      Fintype.prod_ite_eq g (fun _ : G => values j ^ e j)

/-- A literal family of masks may be substituted by its proved owner fibres;
the finite algebra does not unfold any acquired cache to compare predicates. -/
theorem source_optional_sets {G R : Type*} [Fintype G] [CommMonoid R]
    (family : ℕ → Option G) (sets : G → Set ℕ)
    (hs : ∀ g, sets g = {j | family j = some g})
    (e : ℕ →₀ ℕ) (values : ℕ → R) (hz : ∀ j, family j = none → e j = 0) :
    (∏ g,e.prod (fun j n => if j ∈ sets g then values j ^ n else 1)) =
      e.prod (fun j n => values j ^ n) := by
  have he : (∏ g,e.prod (fun j n => if j ∈ sets g then values j ^ n else 1)) =
      ∏ g,e.prod (fun j n => if family j = some g then values j ^ n else 1) := by
    apply Finset.prod_congr rfl
    intro g _
    apply Finsupp.prod_congr
    intro j _
    rw [hs g]
    by_cases h : family j = some g
    · simp only [Set.mem_ofPred_eq,h,ite_true]
    · simp only [Set.mem_ofPred_eq,h,ite_false]
  exact he.trans (source_optional family e values hz)

/-- The original beta uses every source exponent exactly once across the
ACTUAL computed source masks, and none at absent catalogue indices. -/
theorem original_source_factors {R : Type*} [CommMonoid R]
    (n F r a u p : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a)
    (beta : List ℕ) (hb : beta ∈ (node n F r a u p arity owner i).modes.values)
    (values : ℕ → R) :
    (∏ fg : Fin (original n F r a arity owner).state.packets.length × Fin r,
      beta.toFinsupp.prod (fun j exponent =>
        if j ∈ sourceSet (SemiprimeD1PacketModeMask.fromModes
          (node n F r a u p arity owner i) fg.1 i fg.2)
        then values j ^ exponent else 1)) =
      beta.toFinsupp.prod (fun j exponent => values j ^ exponent) := by
  let G := Fin (original n F r a arity owner).state.packets.length × Fin r
  let sets : G → Set ℕ := fun fg => sourceSet
    (SemiprimeD1PacketModeMask.fromModes (node n F r a u p arity owner i) fg.1 i fg.2)
  have hs : ∀ fg : G,sets fg = {j | sourceFamily n F r a u p arity owner i j = some fg} := by
    intro fg
    exact source_set n F r a u p arity owner i fg.1 fg.2
  have hz : ∀ j, sourceFamily n F r a u p arity owner i j = none → beta.toFinsupp j = 0 := by
    intro j hj
    have hl := SemiprimeD1PacketCoefficientSeparation.original_query_length n F r a u p arity owner i beta hb
    have hn : (modes n F r a (cutoff n F r a u p arity owner i) arity owner i).length ≤ j := by
      by_contra h
      simp only [sourceFamily,show j <
        (modes n F r a (cutoff n F r a u p arity owner i) arity owner i).length by omega,
        dite_true,reduceCtorEq] at hj
    exact List.toFinsupp_apply_le beta j (hl.trans_le hn)
  exact source_optional_sets (sourceFamily n F r a u p arity owner i) sets hs beta.toFinsupp values hz

/-- The complete product of actual packet/group recipe polynomials is
covered by the SAME actual global menu enumerated by the original source. -/
theorem original_eval_menu (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (n F r a u p : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a)
    (assignment : SemiprimeD1ChildGraph.Endpoint (n+F) → Bool)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (hprecision : ctx.precision = (node n F r a u p arity owner i).precision)
    (hpos : ctx.Positive) (hp : 0 < ctx.precision)
    (ht : SemiprimeD1WireKernelOriginal.point a t.val ≠ 0)
    (hi : padicValInt 2 (SemiprimeD1WireKernelOriginal.point a t.val) = i.val)
    (values : ℕ → Carrier ctx) :
    MvPolynomial.eval values
      (∏ fg : Fin (original n F r a arity owner).state.packets.length × Fin r,
        packetPolynomial ctx z n F r a u p arity owner i fg.1 fg.2 assignment t) =
      ((node n F r a u p arity owner i).modes.values.map (fun beta =>
        (∏ fg : Fin (original n F r a arity owner).state.packets.length × Fin r,
          packetPolynomial ctx z n F r a u p arity owner i fg.1 fg.2 assignment t).coeff beta.toFinsupp *
            beta.toFinsupp.prod (fun j exponent => values j ^ exponent))).sum := by
  let source := node n F r a u p arity owner i
  let ws := SemiprimeD1ModeCatalog.weights (source.packets.state.packets.length*2^(i.val+1))
    (source.precision-1)
  let Q := fun fg : Fin (original n F r a arity owner).state.packets.length × Fin r =>
    packetPolynomial ctx z n F r a u p arity owner i fg.1 fg.2 assignment t
  have hw : ∀ w ∈ ws, 0 < w := by
    intro w hw
    obtain ⟨item,_,rfl⟩ := List.mem_map.mp hw
    omega
  have hweight : ∀ fg, Weighted (SemiprimeD1AcquiredModeSum.weight ws) (Q fg) := by
    intro fg
    have h := packet_polynomial_weighted ctx z a i t
      (SemiprimeD1PacketGlobalRowForm.columnsOf n F r a arity owner i fg.1 assignment fg.2)
      (rowsOf n F r a arity owner i fg.1 assignment fg.2)
      (SemiprimeD1PacketModeMask.fromModes source fg.1 i fg.2) hpos hp ht hi
    have he := original_weights source fg.1 i fg.2
    exact (congrArg (fun w => Weighted (SemiprimeD1AcquiredModeSum.weight w) (Q fg)) he).mp h
  have hfinite : ∀ fg, On {j | j < ws.length} (Q fg) := by
    intro fg
    have h := polynomial_finite ctx z a i t
      (SemiprimeD1PacketGlobalRowForm.columnsOf n F r a arity owner i fg.1 assignment fg.2)
      (rowsOf n F r a arity owner i fg.1 assignment fg.2)
      (SemiprimeD1PacketModeMask.fromModes source fg.1 i fg.2)
    have he := congrArg List.length (original_weights source fg.1 i fg.2)
    simp only [weights,List.length_map] at he
    exact (congrArg (fun K => On {j | j < K} (Q fg)) he).mp h
  have he := SemiprimeD1AcquiredModeSum.eval_acquired ws hw ctx.precision hp
    (∏ fg, Q fg) (weighted_prod _ _ _ (fun fg _ => hweight fg))
    (on_prod _ _ _ (fun fg _ => hfinite fg))
    (SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes)) values
  have hm : source.modes.values =
      (SemiprimeD1WeightedTuples.acquire ws (ctx.precision-1)).values := by
    change (SemiprimeD1OriginalModeAcquisition.acquire n F r a u i.val p arity owner).modes.values = _
    rw [SemiprimeD1OriginalModeAcquisition.modes_original,SemiprimeD1ModeCatalog.acquireModes_values,
      SemiprimeD1WeightedTuples.acquire_values]
    have hp' := SemiprimeD1OriginalModeAcquisition.precision_original n F r a u i.val p arity owner
    have hc : SemiprimeD1ModeRate.modeBudget
        (SemiprimeD1CollisionOriginal.ports n F a arity).length u a i.val p = ctx.precision-1 := by
      rw [hprecision,hp']
      rfl
    rw [hc]
    dsimp only [ws]
    rw [← hprecision]
    rfl
  rw [← hm] at he
  exact he

/-- Abstract mask substitution keeps the coefficient proof opaque before
the literal original caches are instantiated. -/
theorem coefficient_masks {G R : Type*} [Fintype G] [CommRing R]
    (family : ℕ → Option G) (sets : G → Set ℕ) (Q : G → MvPolynomial ℕ R)
    (hs : ∀ g,sets g = {j | family j = some g}) (hon : ∀ g,On (sets g) (Q g))
    (e : ℕ →₀ ℕ) (hz : ∀ j,family j = none → e j = 0) :
    (∏ g,Q g).coeff e = ∏ g,(Q g).coeff (restrict (sets g) e) := by
  have hon' : ∀ g,On {j | family j = some g} (Q g) := by
    intro g
    rw [← hs g]
    exact hon g
  have he := SemiprimeD1PartialCoefficient.coefficient_optional family Q hon' e hz
  refine he.trans ?_
  apply Finset.prod_congr rfl
  intro g _
  exact congrArg (fun S => (Q g).coeff (restrict S e)) (hs g).symm

/-- Every actual acquired global coefficient is the product of coefficients
requested from the actual target-masked packet/group polynomials. -/
theorem original_coefficient_factor (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (n F r a u p : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a)
    (assignment : SemiprimeD1ChildGraph.Endpoint (n+F) → Bool)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (beta : List ℕ) (hb : beta ∈ (node n F r a u p arity owner i).modes.values) :
    (∏ fg : Fin (original n F r a arity owner).state.packets.length × Fin r,
      packetPolynomial ctx z n F r a u p arity owner i fg.1 fg.2 assignment t).coeff beta.toFinsupp =
      ∏ fg : Fin (original n F r a arity owner).state.packets.length × Fin r,
        (packetPolynomial ctx z n F r a u p arity owner i fg.1 fg.2 assignment t).coeff
          (restrict (targetSet (SemiprimeD1PacketModeMask.fromModes
            (node n F r a u p arity owner i) fg.1 i fg.2)) beta.toFinsupp) := by
  let G := Fin (original n F r a arity owner).state.packets.length × Fin r
  let Q : G → MvPolynomial ℕ (Carrier ctx) := fun fg =>
    packetPolynomial ctx z n F r a u p arity owner i fg.1 fg.2 assignment t
  let sets : G → Set ℕ := fun fg => targetSet
    (SemiprimeD1PacketModeMask.fromModes (node n F r a u p arity owner i) fg.1 i fg.2)
  let family := targetFamily n F r a u p arity owner i
  have hs : ∀ fg : G,sets fg = {j | family j = some fg} := by
    intro fg
    exact target_set n F r a u p arity owner i fg.1 fg.2
  have hon : ∀ fg : G,On (sets fg) (Q fg) := by
    intro fg
    dsimp only [sets,Q,packetPolynomial,polynomial]
    exact SemiprimeD1PacketPolynomialSupport.packet_polynomial_on ctx z a i t _ _ _
  have hz : ∀ j,family j = none → beta.toFinsupp j = 0 := by
    intro j hj
    have hl := SemiprimeD1PacketCoefficientSeparation.original_query_length n F r a u p arity owner i beta hb
    by_cases hk : j < (modes n F r a (cutoff n F r a u p arity owner i) arity owner i).length
    · simp only [family,targetFamily,hk,dite_true,reduceCtorEq] at hj
    · exact List.toFinsupp_apply_le beta j (hl.trans_le (Nat.le_of_not_gt hk))
  exact coefficient_masks family sets Q hs hon beta.toFinsupp hz

/-- The actual physical packet entry under one common original endpoint
assignment. This proof-side abbreviation invokes the original evaluator; it
is never supplied as a table-entry callback to the recursive controller. -/
def queryEntry (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (n F r a u p : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a)
    (fg : Fin (original n F r a arity owner).state.packets.length × Fin r)
    (assignment : SemiprimeD1ChildGraph.Endpoint (n+F) → Bool)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ) : Carrier ctx :=
  let endpoints := ((SemiprimeD1ChildGraph.acquire n F r a arity owner i fg.2).factors[fg.1.val]?).getD []
  interpret ctx (SemiprimeD1PacketEntryBits.evaluate ctx z a i t
    (SemiprimeD1PacketModeMask.fromModes (node n F r a u p arity owner i) fg.1 i fg.2)
    endpoints beta (endpoints.map assignment)).words

/-- Each physical queried entry is the actual restricted coefficient times
its owned ORIGINAL-beta source powers from the same actual global vector. -/
theorem queryEntry_value (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (n F r a u p : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a)
    (fg : Fin (original n F r a arity owner).state.packets.length × Fin r)
    (assignment : SemiprimeD1ChildGraph.Endpoint (n+F) → Bool)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ)
    (hb : beta ∈ (node n F r a u p arity owner i).modes.values) (hpos : ctx.Positive) :
    queryEntry ctx z n F r a u p arity owner i fg assignment t beta =
      (packetPolynomial ctx z n F r a u p arity owner i fg.1 fg.2 assignment t).coeff
        (restrict (targetSet (SemiprimeD1PacketModeMask.fromModes
          (node n F r a u p arity owner i) fg.1 i fg.2)) beta.toFinsupp) *
      beta.toFinsupp.prod (fun j exponent => if j ∈ sourceSet
        (SemiprimeD1PacketModeMask.fromModes (node n F r a u p arity owner i) fg.1 i fg.2)
        then (SemiprimeD1PacketSourceVector.values ctx n F r a (cutoff n F r a u p arity owner i)
          arity owner i assignment j)^exponent else 1) := by
  unfold queryEntry
  rw [SemiprimeD1PacketEntryPolynomial.evaluate_polynomial ctx z a i t _ _ beta _ hpos]
  have he := SemiprimeD1PacketSourceProductValues.original_source_product_values ctx n F r a u p
    arity owner i fg.1 fg.2 assignment beta hb hpos
  dsimp only [packetPolynomial,rowsOf,SemiprimeD1PacketGlobalRowForm.columnsOf] at he ⊢
  apply congrArg₂ (·*·)
  · rfl
  · exact he

/-- A complete original acquired query term equals the product of the ACTUAL
physically executed packet/group queries, with no supplied coefficient or
source-value answer. This is the coefficient/source cancellation join. -/
theorem original_query_factor (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (n F r a u p : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a)
    (assignment : SemiprimeD1ChildGraph.Endpoint (n+F) → Bool)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ)
    (hb : beta ∈ (node n F r a u p arity owner i).modes.values) (hpos : ctx.Positive) :
    (∏ fg : Fin (original n F r a arity owner).state.packets.length × Fin r,
      packetPolynomial ctx z n F r a u p arity owner i fg.1 fg.2 assignment t).coeff beta.toFinsupp *
      beta.toFinsupp.prod (fun j exponent =>
        (SemiprimeD1PacketSourceVector.values ctx n F r a (cutoff n F r a u p arity owner i)
          arity owner i assignment j)^exponent) =
      ∏ fg : Fin (original n F r a arity owner).state.packets.length × Fin r,
        queryEntry ctx z n F r a u p arity owner i fg assignment t beta := by
  rw [original_coefficient_factor ctx z n F r a u p arity owner i assignment t beta hb,
    ← original_source_factors n F r a u p arity owner i beta hb
      (SemiprimeD1PacketSourceVector.values ctx n F r a (cutoff n F r a u p arity owner i)
        arity owner i assignment)]
  simp_rw [queryEntry_value ctx z n F r a u p arity owner i _ assignment t beta hb hpos]
  exact Finset.prod_mul_distrib.symm

/-- The whole actual original packet family evaluates by the original finite
acquired menu of actual physical entry queries. It constructs no full matrix
or full multivariate polynomial at runtime. -/
theorem original_eval_queries (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (n F r a u p : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a)
    (assignment : SemiprimeD1ChildGraph.Endpoint (n+F) → Bool)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (hprecision : ctx.precision = (node n F r a u p arity owner i).precision)
    (hpos : ctx.Positive) (hp : 0 < ctx.precision)
    (ht : SemiprimeD1WireKernelOriginal.point a t.val ≠ 0)
    (hi : padicValInt 2 (SemiprimeD1WireKernelOriginal.point a t.val) = i.val) :
    MvPolynomial.eval
      (SemiprimeD1PacketSourceVector.values ctx n F r a (ctx.precision-1) arity owner i assignment)
      (∏ fg : Fin (original n F r a arity owner).state.packets.length × Fin r,
        packetPolynomial ctx z n F r a u p arity owner i fg.1 fg.2 assignment t) =
      ((node n F r a u p arity owner i).modes.values.map (fun beta =>
        ∏ fg : Fin (original n F r a arity owner).state.packets.length × Fin r,
          queryEntry ctx z n F r a u p arity owner i fg assignment t beta)).sum := by
  rw [original_eval_menu ctx z n F r a u p arity owner i assignment t hprecision hpos hp ht hi]
  apply congrArg List.sum
  apply List.map_congr_left
  intro beta hb
  have hcut : ctx.precision-1 = cutoff n F r a u p arity owner i := congrArg (fun P => P-1) hprecision
  rw [hcut]
  exact original_query_factor ctx z n F r a u p arity owner i assignment t beta hb hpos

end
end RiemannGaussian.SemiprimeD1PacketQueryProduct
