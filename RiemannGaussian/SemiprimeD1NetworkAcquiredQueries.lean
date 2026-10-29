/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketQueryProduct
import RiemannGaussian.SemiprimeD1OriginalChildProduct
import RiemannGaussian.SemiprimeD1ChildContractionSum
import RiemannGaussian.SemiprimeD1NetworkPacketPolynomial

/-! # Acquired original queries join the actual network and actual child integrands
Every original table factor, packet entry and endpoint bit is read from its
actual constructor. The assignment sums here are erased algebraic identities;
the executed controller uses only its acquired menu and recursive child calls.
-/
set_option autoImplicit false
set_option maxHeartbeats 220000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1NetworkAcquiredQueries
open scoped BigOperators
open SemiprimeD1TensorNetwork SemiprimeD1JetAxes SemiprimeD1JetInterpretation
open SemiprimeD1OriginalChildProduct SemiprimeD1PacketQueryProduct
open SemiprimeD1ChildNetworkIntegrand SemiprimeD1ChildPacketEntrySemantics
open SemiprimeD1ChildOldEntryAssignment SemiprimeD1OriginalDoubleAssignments
open SemiprimeD1JetBoxIndex SemiprimeD1JetScalarMap SemiprimeD1DyadicInteger
noncomputable section
attribute [local irreducible] SemiprimeD1PacketReplayOriginal.acquire SemiprimeD1ChildGraph.acquire

/-- Actual original occurrence assignments of the literal network. -/
abbrev OriginalBits (net : Network) (r a : ℕ) :=
  Bits net.leftCount net.rows.length r a (arity net.rows) (owner net.rows)

/-- The original individual right-X/left-Y table factors at CHILD precision. -/
def oldFactor (net : Network) (old : Context) (q p r a : ℕ)
    (x y : OriginalBits net r a) : Carrier ⟨q::old.axes,p⟩ :=
  SemiprimeD1JetBlockPolynomial.actualEmbedding old q p
    ((net.right.toList.map (fun v => interpret ⟨old.axes,p⟩
      (SemiprimeD1TensorTables.valueAt v.table (SemiprimeD1LeafCounter.localAssignment x v)))).prod) *
  SemiprimeD1JetBlockPolynomial.actualEmbedding old q p
    ((net.left.toList.map (fun v => interpret ⟨old.axes,p⟩
      (SemiprimeD1TensorTables.valueAt v.table (SemiprimeD1LeafCounter.localAssignment y v)))).prod)

/-- The actually cached packet term is exactly the actual queried entry;
borrowing changes only reports, and the header supplies the original bucket. -/
theorem packetTerm_query (net : Network) (r a u p0 : ℕ) (i : Fin a) (g : Fin r)
    (ctx : Context) (z : SemiprimeD1JetRingBits.Run)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ)
    (bits : Incidence net.rows × Bool → Bool)
    (f : Fin (original net r a).state.packets.length) (hpos : ctx.Positive) :
    packetTerm net r a u p0 i g ctx z t beta bits f =
      queryEntry ctx z net.leftCount net.rows.length r a u p0 (arity net.rows) (owner net.rows)
        i (f,g) (endpointBits net r a bits) t beta := by
  let source := node net r a u p0 i
  let cache := SemiprimeD1PacketModeMask.fromModes source f i g
  let points := ((SemiprimeD1ChildGraph.fromReplay (owner net.rows) source.packets i g).factors[f.val]?).getD []
  have hp : source.packets = SemiprimeD1PacketReplayOriginal.acquire net.leftCount net.rows.length r a
      (arity net.rows) (owner net.rows) := rfl
  have he := congrArg (fun replay =>
    ((SemiprimeD1ChildGraph.fromReplay (owner net.rows) replay i g).factors[f.val]?).getD []) hp
  have hgraph : SemiprimeD1ChildGraph.acquire net.leftCount net.rows.length r a (arity net.rows)
      (owner net.rows) i g = SemiprimeD1ChildGraph.fromReplay (owner net.rows)
        (SemiprimeD1PacketReplayOriginal.acquire net.leftCount net.rows.length r a
          (arity net.rows) (owner net.rows)) i g := by
    unfold SemiprimeD1ChildGraph.acquire
    rfl
  change interpret ctx (SemiprimeD1PacketEntryBits.evaluate ctx (SemiprimeD1PacketEntryBits.borrow z)
    a i t cache points beta (points.map (endpointBits net r a bits))).words = _
  refine (SemiprimeD1PacketEntryPolynomial.evaluate_borrow ctx z a i t cache points beta _ hpos).trans ?_
  dsimp only [queryEntry]
  have he' := he.trans (congrArg (fun graph : SemiprimeD1ChildGraph.Graph (net.leftCount+net.rows.length) =>
    (graph.factors[f.val]?).getD []) hgraph.symm)
  exact congrArg (fun endpoints => interpret ctx (SemiprimeD1PacketEntryBits.evaluate ctx z a i t cache
    endpoints beta (endpoints.map (endpointBits net r a bits))).words) he'

/-- At each original X/Y assignment, the product of all EXECUTED child
integrands is exactly its original old factor times the actual queried
packet/group product. No local truth or source-vector answer is a premise. -/
theorem child_product_original (net : Network) (hw : WellFormed net) (old : Context)
    (hg : Good old net) (q p r a u : ℕ) [NeZero r] (hq : 0 < q) (i : Fin a)
    (z : SemiprimeD1JetRingBits.Run) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (beta : List ℕ) (x y : OriginalBits net r a) (hpos : (⟨q::old.axes,p⟩ : Context).Positive) :
    (∏ g : Fin r,interpret ⟨q::old.axes,p⟩
      (SemiprimeD1LeafCounter.evaluateAssignment ⟨q::old.axes,p⟩
        (vertices (child net old [q] p r a u i g z t beta))
        (List.ofFn (networkAssignment net r a i g
          (SemiprimeD1PacketAssignmentRows.tagBits net.leftCount net.rows.length r a
            (arity net.rows) (owner net.rows) x y)))).words) =
      oldFactor net old q p r a x y *
      ∏ fg : Fin (original net r a).state.packets.length × Fin r,
        queryEntry ⟨q::old.axes,p⟩ z net.leftCount net.rows.length r a u old.precision
          (arity net.rows) (owner net.rows) i fg
          (endpointBits net r a (SemiprimeD1PacketAssignmentRows.tagBits net.leftCount net.rows.length r a
            (arity net.rows) (owner net.rows) x y)) t beta := by
  have hc := all_child_integrands net hw old [q] p r a u i z t beta
    (SemiprimeD1PacketAssignmentRows.tagBits net.leftCount net.rows.length r a
      (arity net.rows) (owner net.rows) x y) hpos
  have hp := original_parent_product net hw old hg q p r a hq x y
  simp only [List.singleton_append] at hc
  refine hc.trans ?_
  apply congrArg₂ (·*·)
  · exact hp
  · rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro f _
    apply Finset.prod_congr rfl
    intro g _
    exact packetTerm_query net r a u old.precision i g ⟨q::old.axes,p⟩ z t beta _ f hpos

/-- A literal acquired list commutes with the two original finite assignment
sums, preserving its actual order and every zero contribution. -/
theorem sum_double_list {X Y B R : Type*} [Fintype X] [Fintype Y] [CommSemiring R]
    (items : List B) (factor : X → Y → R) (term : B → X → Y → R) :
    (∑ x : X,∑ y : Y,factor x y * (items.map (fun b => term b x y)).sum) =
      (items.map (fun b => ∑ x : X,∑ y : Y,factor x y * term b x y)).sum := by
  classical
  induction items with
  | nil => simp only [List.map_nil,List.sum_nil,mul_zero,Finset.sum_const_zero]
  | cons b items ih =>
    simp only [List.map_cons,List.sum_cons,mul_add,Finset.sum_add_distrib,ih]

/-- COMPLETE actual original-network D.16 contraction. Only literal network
data, its actual acquired mode menu and actual constructed child leaf values
occur. No table/coefficient/source-vector/projection or collision answer is
supplied. The leaf values on the right are the erased recursive specifications.
-/
theorem network_query_contraction (net : Network) (hw : WellFormed net) (old : Context)
    (hg : Good old net) (q p r a u : ℕ) [NeZero r] (i : Fin a)
    (z : SemiprimeD1JetRingBits.Run) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (hprecision : p = (node net r a u old.precision i).precision)
    (hpos : old.Positive) (hq : 0 < q) (hp : 0 < p)
    (ht : SemiprimeD1WireKernelOriginal.point a t.val ≠ 0)
    (hi : padicValInt 2 (SemiprimeD1WireKernelOriginal.point a t.val) = i.val) :
    ((SemiprimeD1NetworkIntegralDeformation.networkPolynomial old.axes net.leftCount net.rows.length r a
      (arity net.rows) (owner net.rows) t net.left.toList net.right.toList).map
        (scalarMap (dims old.axes) (reduction p))).eval₂
          (SemiprimeD1JetBlockPolynomial.actualEmbedding old q p)
          (interpret ⟨q::old.axes,p⟩ z.words) =
      ((node net r a u old.precision i).modes.values.map (fun beta =>
        ∏ g : Fin r,interpret ⟨q::old.axes,p⟩
          (leaf ⟨q::old.axes,p⟩ (child net old [q] p r a u i g z t beta)).words)).sum := by
  let current : Context := ⟨q::old.axes,p⟩
  let f : Carrier ⟨old.axes,p⟩ →+* Carrier current :=
    SemiprimeD1JetBlockPolynomial.actualEmbedding old q p
  let source := node net r a u old.precision i
  let sigma := fun x y : OriginalBits net r a => endpointBits net r a
    (SemiprimeD1PacketAssignmentRows.tagBits net.leftCount net.rows.length r a
      (arity net.rows) (owner net.rows) x y)
  let query := fun beta (x y : OriginalBits net r a) =>
    ∏ fg : Fin (original net r a).state.packets.length × Fin r,
      queryEntry current z net.leftCount net.rows.length r a u old.precision
        (arity net.rows) (owner net.rows) i fg (sigma x y) t beta
  have hcurrent : current.Positive := by
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hq
    · exact hpos j hj
  have hs := SemiprimeD1NetworkPacketPolynomial.network_packet_polynomial old.axes current f
    (SemiprimeD1ChildFreshLiftValue.actualEmbedding_constants old q p) z net r a u old.precision i t
      hprecision hcurrent hp ht hi
  have heval (x y : OriginalBits net r a) :
      MvPolynomial.eval
        (SemiprimeD1PacketSourceVector.values current net.leftCount net.rows.length r a (p-1)
          (arity net.rows) (owner net.rows) i (sigma x y))
        (∏ packet : Fin (original net r a).state.packets.length,∏ g : Fin r,
          SemiprimeD1PacketRowProducts.packetPolynomial current z net.leftCount net.rows.length r a u
            old.precision (arity net.rows) (owner net.rows) i packet g (sigma x y) t) =
      (source.modes.values.map (fun beta => query beta x y)).sum := by
    have he := original_eval_queries current z net.leftCount net.rows.length r a u old.precision
      (arity net.rows) (owner net.rows) i (sigma x y) t hprecision hcurrent hp ht hi
    have hprod :
        (∏ packet : Fin (original net r a).state.packets.length,∏ g : Fin r,
          SemiprimeD1PacketRowProducts.packetPolynomial current z net.leftCount net.rows.length r a u
            old.precision (arity net.rows) (owner net.rows) i packet g (sigma x y) t) =
        ∏ fg : Fin (original net r a).state.packets.length × Fin r,
          SemiprimeD1PacketRowProducts.packetPolynomial current z net.leftCount net.rows.length r a u
            old.precision (arity net.rows) (owner net.rows) i fg.1 fg.2 (sigma x y) t := by
      rw [Fintype.prod_prod_type]
    exact (congrArg (MvPolynomial.eval
      (SemiprimeD1PacketSourceVector.values current net.leftCount net.rows.length r a (p-1)
        (arity net.rows) (owner net.rows) i (sigma x y))) hprod).trans he
  calc
    _ = ∑ x : OriginalBits net r a,∑ y : OriginalBits net r a,
        oldFactor net old q p r a x y *
        MvPolynomial.eval
          (SemiprimeD1PacketSourceVector.values current net.leftCount net.rows.length r a (p-1)
            (arity net.rows) (owner net.rows) i (sigma x y))
          (∏ packet : Fin (original net r a).state.packets.length,∏ g : Fin r,
            SemiprimeD1PacketRowProducts.packetPolynomial current z net.leftCount net.rows.length r a u
              old.precision (arity net.rows) (owner net.rows) i packet g (sigma x y) t) := hs
    _ = ∑ x : OriginalBits net r a,∑ y : OriginalBits net r a,
        oldFactor net old q p r a x y * (source.modes.values.map (fun beta => query beta x y)).sum := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      exact congrArg (fun value => oldFactor net old q p r a x y * value) (heval x y)
    _ = (source.modes.values.map (fun beta => ∑ x : OriginalBits net r a,∑ y : OriginalBits net r a,
        oldFactor net old q p r a x y * query beta x y)).sum :=
      sum_double_list source.modes.values (oldFactor net old q p r a) query
    _ = _ := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro beta _
      have hpoint (x y : OriginalBits net r a) :=
        child_product_original net hw old hg q p r a u hq i z t beta x y hcurrent
      have hsum := SemiprimeD1ChildContractionSum.sum_child_contractions net old [q] p r a u i z t beta hcurrent
      simp only [List.singleton_append] at hsum
      refine Eq.trans ?_ hsum
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      exact (hpoint x y).symm

end
end RiemannGaussian.SemiprimeD1NetworkAcquiredQueries
