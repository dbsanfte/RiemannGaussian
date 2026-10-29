/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecursiveRecoveryRun
import RiemannGaussian.SemiprimeD1JetBlockPolynomial

/-! # Concrete phase composition from the acquired network query
The continuation premise is an induction hypothesis on actual constructed
children. The other premise is the precise original-network query identity;
there is no supplied block, coefficient, width or entry answer.
-/
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1RecursivePhaseCorrectness
open scoped BigOperators
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1RecursiveCounter
open SemiprimeD1JetInterpretation SemiprimeD1JetAffineCoefficient
open SemiprimeD1WireKernelOriginal SemiprimeD1HermiteNodes SemiprimeD1JetRecoveryGrid
open SemiprimeD1RecursivePhaseControl SemiprimeD1RecursiveRecovery
attribute [local irreducible] SemiprimeD1OriginalModeAcquisition.acquire

/-- Correctness required only of the structurally smaller continuation. -/
def NextCorrect (next : Context → Network → JetRun) : Prop :=
  ∀ ctx net, ctx.Positive → WellFormed net → Good ctx net →
    interpret ctx (next ctx net).words = interpret ctx (leaf ctx net).words

/-- Actual retained-node valuation index, with its bound derived from the grid. -/
def phaseIndex (net : Network) (a u : ℕ) (t : Fin (size a)) (hua : u ≤ a)
    (ht : t.val ∈ active a (SemiprimeD1TaperedLoss.height (edgeCount net) u) u) : Fin a :=
  ⟨_,(active_guard net a u t hua ht).1⟩

/-- Erased view of the exact inner product/sum component in `phase`. Its
component clock is not asserted to include the surrounding source acquisition. -/
def phaseTotal (next : Context → Network → JetRun) (ctx : Context) (net : Network)
    (a u : ℕ) (t : Fin (size a)) (i : Fin a) : JetRun :=
  let source := SemiprimeD1OriginalModeAcquisition.acquire net.leftCount net.rows.length 64
    a u i.val ctx.precision (arity net.rows) (owner net.rows)
  let q := SemiprimeD1ModeRate.jetHeight (edgeCount net) u * (u-i.val)
  let fresh := SemiprimeD1FreshJetBits.acquireFresh ctx q source.precision
  let current : Context := ⟨q::ctx.axes,source.precision⟩
  sumRuns current (source.modes.values.map (fun beta =>
    product current ((List.finRange 64).map (fun g =>
      let child := SemiprimeD1ChildNetwork.fromSource net source i g
        ctx [q] source.precision fresh t beta
      let answer := next current child.network
      (⟨answer.words,child.clock+answer.clock+5⟩ : JetRun)))))

/-- A generic type barrier keeps actual source acquisition out of ring-instance
unification. This is an erased equality, not an acquired entry interface. -/
def queryEquation (ctx : Context) (q p : ℕ)
    (F : Polynomial (Carrier ⟨ctx.axes,p⟩))
    (words : List (List Bool))
    (rhs : Carrier ⟨q::ctx.axes,p⟩) : Prop :=
  F.eval₂ (SemiprimeD1JetBlockPolynomial.actualEmbedding ctx q p)
    (interpret ⟨q::ctx.axes,p⟩ words) = rhs

/-- Generic equality composition and block extraction keep concrete source
programs out of ring-instance inference. -/
theorem extract_of_query (ctx : Context) (q p j : ℕ) (input : JetRun)
    (hpos : ctx.Positive) (hj : j < q) (F : Polynomial (Carrier ⟨ctx.axes,p⟩))
    (rhs : Carrier ⟨q::ctx.axes,p⟩)
    (htotal : interpret ⟨q::ctx.axes,p⟩ input.words = rhs)
    (hquery : queryEquation ctx q p F
      (SemiprimeD1FreshJetBits.acquireFresh ctx q p).words rhs) :
    interpret ⟨ctx.axes,p⟩ (SemiprimeD1JetBlockBits.extractRun ctx j input).words = F.coeff j := by
  exact SemiprimeD1JetBlockPolynomial.extractRun_polynomial ctx q p j input hpos hj F
    (htotal.trans hquery.symm)

/-- The original integral polynomial reduced at an explicit scalar precision.
Keeping the precision abstract prevents executable acquisition during elaboration. -/
noncomputable def reducedPolynomial (ctx : Context) (net : Network) (a : ℕ)
    (t : Fin (size a)) (p : ℕ) : Polynomial (Carrier ⟨ctx.axes,p⟩) :=
  (SemiprimeD1NetworkIntegralDeformation.networkPolynomial ctx.axes
    net.leftCount net.rows.length 64 a (arity net.rows) (owner net.rows)
    t net.left.toList net.right.toList).map
      (SemiprimeD1JetScalarMap.scalarMap (SemiprimeD1JetBoxIndex.dims ctx.axes)
        (SemiprimeD1DyadicInteger.reduction p))

/-- Erased finite sum of actual child leaf values, at an explicit context. -/
noncomputable def leafSum (net : Network) {a : ℕ} (source : SemiprimeD1ChildNetwork.Source net a)
    (i : Fin a) (ctx : Context) (q p : ℕ) (fresh : SemiprimeD1JetRingBits.Run)
    (t : Fin (size a)) : Carrier ⟨q::ctx.axes,p⟩ :=
  (source.modes.values.map (fun beta => ∏ g : Fin 64, interpret ⟨q::ctx.axes,p⟩
    (leaf ⟨q::ctx.axes,p⟩ (SemiprimeD1ChildNetwork.fromSource net source i g
      ctx [q] p fresh t beta).network).words)).sum

/-- The exact query identity needed at one actual node. Every polynomial,
mode, child network and fresh word is constructed from the original input. -/
def QueryAt (ctx : Context) (net : Network) (a u : ℕ) (t : Fin (size a)) (i : Fin a) : Prop :=
  let source := SemiprimeD1OriginalModeAcquisition.acquire net.leftCount net.rows.length 64
    a u i.val ctx.precision (arity net.rows) (owner net.rows)
  let q := SemiprimeD1ModeRate.jetHeight (edgeCount net) u * (u-i.val)
  let fresh := SemiprimeD1FreshJetBits.acquireFresh ctx q source.precision
  let F := reducedPolynomial ctx net a t source.precision
  queryEquation ctx q source.precision F fresh.words
    (leafSum net source i ctx q source.precision fresh t)

/-- Actual cached products and sums inherit the continuation's child correctness. -/
theorem phaseTotal_value (next : Context → Network → JetRun) (ctx : Context)
    (net : Network) (a u : ℕ) (t : Fin (size a)) (i : Fin a)
    (hnext : NextCorrect next) (hg : Good ctx net)
    (hpos : (⟨(SemiprimeD1ModeRate.jetHeight (edgeCount net) u * (u-i.val))::ctx.axes,
      (SemiprimeD1OriginalModeAcquisition.acquire net.leftCount net.rows.length 64
        a u i.val ctx.precision (arity net.rows) (owner net.rows)).precision⟩ : Context).Positive) :
    let source := SemiprimeD1OriginalModeAcquisition.acquire net.leftCount net.rows.length 64
      a u i.val ctx.precision (arity net.rows) (owner net.rows)
    let q := SemiprimeD1ModeRate.jetHeight (edgeCount net) u * (u-i.val)
    let current : Context := ⟨q::ctx.axes,source.precision⟩
    let fresh := SemiprimeD1FreshJetBits.acquireFresh ctx q source.precision
    interpret current (phaseTotal next ctx net a u t i).words =
      (source.modes.values.map (fun beta => ∏ g : Fin 64, interpret current
        (leaf current (SemiprimeD1ChildNetwork.fromSource net source i g
          ctx [q] source.precision fresh t beta).network).words)).sum := by
  dsimp only
  unfold phaseTotal
  rw [sumRuns_value _ _ hpos]
  simp only [List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro beta _
  rw [product_value _ hpos]
  simp only [List.map_map,Function.comp_def]
  have hq : 0 < SemiprimeD1ModeRate.jetHeight (edgeCount net) u * (u-i.val) :=
    hpos _ (List.mem_cons_self ..)
  let source := SemiprimeD1OriginalModeAcquisition.acquire net.leftCount net.rows.length 64
    a u i.val ctx.precision (arity net.rows) (owner net.rows)
  let q := SemiprimeD1ModeRate.jetHeight (edgeCount net) u * (u-i.val)
  let fresh := SemiprimeD1FreshJetBits.acquireFresh ctx q source.precision
  have hchild := fun g : Fin 64 => hnext _ _ hpos
    (SemiprimeD1ChildNetwork.fromSource_wellFormed net source i g ctx [q] source.precision fresh t beta)
    (SemiprimeD1ChildNetwork.fromSource_good net source i g ctx [q] source.precision fresh t beta hg
      (by simpa only [List.prod_cons,List.prod_nil,mul_one] using hq))
  rw [← List.ofFn_eq_map,List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro g _
  exact hchild g

/-- A retained phase uses the actual original multiplicity as its fresh axis. -/
theorem phaseIndex_multiplicity (net : Network) (a u : ℕ) (t : Fin (size a))
    (hua : u ≤ a)
    (ht : t.val ∈ active a (SemiprimeD1TaperedLoss.height (edgeCount net) u) u) :
    SemiprimeD1ModeRate.jetHeight (edgeCount net) u *
      (u-(phaseIndex net a u t hua ht).val) =
      nodeMultiplicity a (SemiprimeD1TaperedLoss.height (edgeCount net) u) u t.val := by
  dsimp only [phaseIndex]
  rw [order_value]
  rfl

/-- Literal array lookup in the actually constructed ascending block list. -/
theorem blocks_read (ctx : Context) (q j : ℕ) (words : List (List Bool)) (hj : j < q) :
    ((((List.range q).map (fun k => SemiprimeD1JetBlockBits.extract ctx k words)).map
      (fun block => block.words)).toArray[j]?).getD [] =
      (SemiprimeD1JetBlockBits.extract ctx j words).words := by
  simp [List.map_map,Function.comp_def,hj]

/-- The exact controller phase stores the exact extraction of its cached total. -/
theorem phase_block (next : Context → Network → JetRun) (ctx : Context) (net : Network)
    (a u : ℕ) (t : Fin (size a)) (hua : u ≤ a)
    (ht : t.val ∈ active a (SemiprimeD1TaperedLoss.height (edgeCount net) u) u)
    (j : ℕ) (hj : j < nodeMultiplicity a (SemiprimeD1TaperedLoss.height (edgeCount net) u) u t.val) :
    ((phase next ctx net a u t).blocks[j]?).getD [] =
      (SemiprimeD1JetBlockBits.extract ctx j
        (phaseTotal next ctx net a u t (phaseIndex net a u t hua ht)).words).words := by
  have hg := active_guard net a u t hua ht
  dsimp only at hg
  have hj' := hj
  rw [← phaseIndex_multiplicity net a u t hua ht] at hj'
  dsimp only [phase]
  rw [dite_eq_left hg]
  exact blocks_read ctx _ j _ hj'

/-- The phase's actual stored precision is the actual acquired source precision. -/
theorem phase_precision (next : Context → Network → JetRun) (ctx : Context) (net : Network)
    (a u : ℕ) (t : Fin (size a)) (hua : u ≤ a)
    (ht : t.val ∈ active a (SemiprimeD1TaperedLoss.height (edgeCount net) u) u) :
    (phase next ctx net a u t).precision =
      (SemiprimeD1OriginalModeAcquisition.acquire net.leftCount net.rows.length 64
        a u (phaseIndex net a u t hua ht).val ctx.precision (arity net.rows) (owner net.rows)).precision := by
  have hg := active_guard net a u t hua ht
  dsimp only at hg
  dsimp only [phase]
  rw [dite_eq_left hg]
  rfl

/-- Concrete network query semantics and correctness of actual children suffice
for every retained block postcondition needed by the original D.5 recovery. -/
theorem phaseCorrect_of_query (next : Context → Network → JetRun) (ctx : Context)
    (net : Network) (a u : ℕ) (hpos : ctx.Positive) (hg : Good ctx net)
    (hua : u ≤ a) (hnext : NextCorrect next)
    (hquery : ∀ t : Fin (size a), ∀ ht : t.val ∈
      active a (SemiprimeD1TaperedLoss.height (edgeCount net) u) u,
      QueryAt ctx net a u t (phaseIndex net a u t hua ht)) :
    PhaseCorrect next ctx net a u := by
  intro t ht j hj
  let i := phaseIndex net a u t hua ht
  let source := SemiprimeD1OriginalModeAcquisition.acquire net.leftCount net.rows.length 64
    a u i.val ctx.precision (arity net.rows) (owner net.rows)
  let q := SemiprimeD1ModeRate.jetHeight (edgeCount net) u * (u-i.val)
  let current : Context := ⟨q::ctx.axes,source.precision⟩
  have hc : current.Positive := active_context_positive ctx net a u t hpos ht
  have hjq : j < q := by
    dsimp only [q,i]
    rw [phaseIndex_multiplicity]
    exact hj
  have htotal := phaseTotal_value next ctx net a u t i hnext hg hc
  let F := reducedPolynomial ctx net a t source.precision
  have hquery' := hquery t ht
  dsimp only [QueryAt,leafSum] at hquery'
  have he := extract_of_query ctx q source.precision j
    (phaseTotal next ctx net a u t i) hpos hjq F
    ((source.modes.values.map (fun beta => ∏ g : Fin 64, interpret current
      (leaf current (SemiprimeD1ChildNetwork.fromSource net source i g ctx [q]
        source.precision (SemiprimeD1FreshJetBits.acquireFresh ctx q source.precision) t beta).network).words)).sum)
    htotal hquery'
  rw [phase_block next ctx net a u t hua ht j hj]
  rw [phase_precision next ctx net a u t hua ht]
  exact he

end RiemannGaussian.SemiprimeD1RecursivePhaseCorrectness
