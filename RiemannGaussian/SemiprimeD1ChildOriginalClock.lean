/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildModeResources
import RiemannGaussian.SemiprimeD1ChildSourceLinear
import RiemannGaussian.SemiprimeD1PhysicalSourceBudget
import RiemannGaussian.SemiprimeD1ChildPullbackBudget
import RiemannGaussian.SemiprimeD1PacketModeMaskBudget

/-! # Original-input actual child table clock, without metadata/entry suppliers
All original source, mode, header, pullback, endpoint and degree conditions are
obtained from the actual constructors and original numeric guards. Source and
fresh reports are retained once outside and once per actual right table.
The conclusion bounds the mixed physical/native-list report, not a complete
primitive address/tape execution.
-/
set_option autoImplicit false
set_option maxHeartbeats 220000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1ChildOriginalClock
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1TensorNetworkRecursion
open SemiprimeD1ChildNetworkClock SemiprimeD1ChildBudgetMono SemiprimeD1ChildSourceLinear

/-- Actual source from this literal cached parent, with no external packet/menu input. -/
abbrev source (net : Network) (old : Context) (a u : ℕ) (i : Fin a) :=
  SemiprimeD1OriginalModeAcquisition.acquire net.leftCount net.rows.length 64 a u i.val old.precision
    (arity net.rows) (owner net.rows)

/-- Literal original total port count, equal to the stored network scope. -/
def ports (net : Network) : ℕ := ∑e,arity net.rows e

/-- Original derived metadata scalars; only fixed arithmetic and original constructors occur. -/
def dataCap (net : Network) (a : ℕ) : ℕ :=
  SemiprimeD1PacketReplayBudget.budget net.leftCount net.rows.length 64 a (ports net)+
    SemiprimeD1ChildPullbackBudget.overhead net.leftCount net.rows.length 64 a (ports net)

/-- Original graph producer report, including retained sparse replay. -/
def graphCap (net : Network) (a : ℕ) : ℕ :=
  SemiprimeD1PacketReplayBudget.budget net.leftCount net.rows.length 64 a (ports net)+
    SemiprimeD1OriginalChildGraphBudget.overhead net.leftCount net.rows.length 64 a (ports net)

/-- The full prepared-data report is retained in EVERY per-vertex routing scan. -/
def orderCap (net : Network) (a : ℕ) : ℕ :=
  dataCap net a+SemiprimeD1ChildOrderBudget.overhead (ports net) (2*(ports net)^2)

/-- Closed original-dimensional budget, linear in actual source/fresh producer
reports and exponential only in the fixed original global degree cap. -/
def originalBudget (net : Network) (old : Context) (extra : List ℕ) (lam a u : ℕ)
    (i : Fin a) (Z : ℕ) : ℕ :=
  let src := source net old a u i
  let M := ports net
  let D := 2^((9*lam+9)/10)
  let K := SemiprimeD1ChildModeResources.catalogueLength net a u i old.precision
  let E := SemiprimeD1PacketReplayBudget.budget net.leftCount net.rows.length 64 a M
  let H0 := SemiprimeD1PacketModeMaskBudget.prepareOverhead net.leftCount net.rows.length 64 a M src.precision
  ((M+1)*(src.work+Z)+prefactor old extra src.precision a D (2*2^a) K
    src.precision (2^a) src.precision K E (net.leftCount+net.rows.length) M (2*M^2)
      0 (dataCap net a) (graphCap net a) 0 (orderCap net a) H0)*2^D

/-- Actual original fromSource acquisition has a closed computed envelope.
The only inputs beyond literal data are original degree/packing/precision
arithmetic guards; no labels, metadata clocks, entries or fit answers occur. -/
theorem fromSource_clock_original (net : Network) (old : Context) (extra : List ℕ)
    (lam a u : ℕ) (i : Fin a) (g : Fin 64)
    (z : SemiprimeD1JetAffineCoefficient.JetRun) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (beta : List ℕ)
    (hbeta : beta ∈ (source net old a u i).modes.values)
    (hw : WellFormed net) (hg : Good old net) (he : 0 < extra.prod)
    (hz : SemiprimeD1JetAffineCoefficientBounds.Good ⟨extra++old.axes,(source net old a u i).precision⟩ z.words)
    (hlam : 1000 ≤ lam) (haSmall : a ≤ 4*(lam/131072)) (hM : edgeCount net ≤ 2^lam)
    (hd : DegreeBound net (2^((9*lam+9)/10)))
    (hsmall : 2*(64^(2*a))^2*(2^((9*lam+9)/10)) ≤ edgeCount net)
    (hsize : 64^(2*a)*2^a ≤ edgeCount net) (hu : 0 < u) (huM : u ≤ edgeCount net)
    (hp : old.precision*u ≤ edgeCount net*2^(a-i.val)) (ha : (a+1)*u ≤ 2^(a-i.val)) :
    (SemiprimeD1ChildNetwork.fromSource net (source net old a u i) i g old extra
      (source net old a u i).precision z t beta).clock ≤ originalBudget net old extra lam a u i z.clock := by
  let src := source net old a u i
  let D := 2^((9*lam+9)/10)
  let M := ports net
  let K := SemiprimeD1ChildModeResources.catalogueLength net a u i old.precision
  let data := SemiprimeD1ChildPortPullback.fromReplay (owner net.rows) src.packets i g
  let G := SemiprimeD1ChildNetwork.graph net src i g
  let rows := SemiprimeD1TensorNetworkLayout.childRows G
  let E := SemiprimeD1PacketReplayBudget.budget net.leftCount net.rows.length 64 a M
  let H0 := SemiprimeD1PacketModeMaskBudget.prepareOverhead net.leftCount net.rows.length 64 a M src.precision
  have hslots : 2*2^a ≤ D := SemiprimeD1ChildModeResources.slots_bound lam a hlam haSmall
  have hcoeff := SemiprimeD1ChildModeResources.coefficient_envelope net hw lam a u i old.precision
    hlam haSmall hM hd hsmall hsize hu huM hp ha
  have hbs := SemiprimeD1PhysicalSourceBudget.mode_bounds net.leftCount net.rows.length 64 a u i.val old.precision
    (arity net.rows) (owner net.rows) beta hbeta
  have hbetaLength : beta.length=K := by
    dsimp only [K,SemiprimeD1ChildModeResources.catalogueLength]
    rw [SemiprimeD1ModeCatalog.catalog_length]
    exact hbs.1
  have hb : ∀b∈beta,b ≤ src.precision := fun b hm => (hbs.2 b hm).trans (Nat.sub_le _ _)
  have hdata : data.work ≤ dataCap net a := by
    have h := SemiprimeD1ChildPullbackBudget.fromReplay_work net.leftCount net.rows.length 64 a
      (arity net.rows) (owner net.rows) i g
    have hs := SemiprimeD1PacketReplayBudget.acquire_work net.leftCount net.rows.length 64 a
      (arity net.rows) (owner net.rows)
    exact h.trans (Nat.add_le_add_right hs _)
  have hgraph : G.work ≤ graphCap net a := by
    have h := SemiprimeD1OriginalChildGraphBudget.fromReplay_work net.leftCount net.rows.length 64 a
      (arity net.rows) (owner net.rows) i g
    have hs := SemiprimeD1PacketReplayBudget.acquire_work net.leftCount net.rows.length 64 a
      (arity net.rows) (owner net.rows)
    exact h.trans (Nat.add_le_add_right hs _)
  have hlinks : data.links.length ≤ 2*M^2 := by
    exact SemiprimeD1ChildPullbackBudget.links_length net.leftCount net.rows.length 64 a
      (arity net.rows) (owner net.rows) i g
  have hrows : rows.length ≤ M := by
    have hh := SemiprimeD1OriginalChildGraphBudget.factors_length net.leftCount net.rows.length 64 a
      (arity net.rows) (owner net.rows) i g
    change (SemiprimeD1TensorNetworkLayout.childRows G).length ≤ M
    rw [SemiprimeD1TensorNetworkLayout.childRows_length]
    exact hh
  have hleft (v : Fin (net.leftCount+net.rows.length)) :
      let order := SemiprimeD1ChildTableOrder.acquire (owner net.rows) data v
      order.old.length ≤ D ∧ order.child.length ≤ D ∧
        (leftPorts (SemiprimeD1TensorNetworkLayout.childRows data.graph) v).length ≤ D ∧
        (SemiprimeD1ChildNetwork.parentVertex net v).ports.length ≤ D ∧ order.clock ≤ orderCap net a := by
    have hf := SemiprimeD1ChildOriginalFields.left_fields net a u i g old extra src.precision z t beta D hw hd hslots v
    have ho := SemiprimeD1ChildPullbackBudget.order_clock net.leftCount net.rows.length 64 a
      (arity net.rows) (owner net.rows) i g v
    have hs := SemiprimeD1PacketReplayBudget.acquire_work net.leftCount net.rows.length 64 a
      (arity net.rows) (owner net.rows)
    have ho' : (SemiprimeD1ChildTableOrder.acquire (owner net.rows) data v).clock ≤ orderCap net a :=
      ho.trans (Nat.add_le_add_right (Nat.add_le_add_right hs _) _)
    exact ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2,ho'⟩
  have hright (e : Fin rows.length) :
      let header := SemiprimeD1PacketTensorTables.prepare (owner net.rows) src
        (SemiprimeD1ChildNetwork.packetIndex net src i g e) i g
      header.endpoints.length ≤ 2*2^a ∧ header.masks.items.length=K ∧
        (∀item∈header.masks.items,item.mode.order ≤ src.precision) ∧
        (∀item∈header.masks.items,item.tile ≤ 2^a) ∧
        (∀endpoint∈header.endpoints,endpoint.slot.length ≤ a) ∧
        (∀endpoint∈header.endpoints,endpoint.edge.length ≤ E) ∧ header.clock ≤ src.work+H0 := by
    let packet := SemiprimeD1ChildNetwork.packetIndex net src i g e
    have hA := SemiprimeD1PacketTensorTables.original_degree_bound net.leftCount net.rows.length 64 a u i.val old.precision
      (arity net.rows) (owner net.rows) packet i g
    have hK := SemiprimeD1ChildOriginalFields.header_items_length net src i g packet
    have hc := SemiprimeD1PacketModeMaskBudget.prepare_item_caps net.leftCount net.rows.length 64 a u i.val old.precision
      (arity net.rows) (owner net.rows) packet i g
    have hpayload := SemiprimeD1PacketModeMaskBudget.prepare_payload net.leftCount net.rows.length 64 a u i.val old.precision
      (arity net.rows) (owner net.rows) packet i g
    have hh := SemiprimeD1PacketModeMaskBudget.prepare_clock net.leftCount net.rows.length 64 a u i.val old.precision
      (arity net.rows) (owner net.rows) packet i g
    exact ⟨hA,hK,(fun item hm => (hc item hm).1),(fun item hm => (hc item hm).2),
      (fun endpoint hm => (hpayload endpoint hm).2.2),(fun endpoint hm => (hpayload endpoint hm).2.1),hh⟩
  have h := SemiprimeD1ChildNetworkClock.fromSource_clock net src i g old extra src.precision z t beta
    D (2*2^a) K src.precision (2^a) src.precision E (orderCap net a) (src.work+H0)
    hg he hz hb hcoeff hleft hright
  have hm := budget_mono old extra src.precision a D (2*2^a) K src.precision (2^a) src.precision beta.length E
    (net.leftCount+net.rows.length) rows.length data.links.length src.work data.work G.work z.clock (orderCap net a) (src.work+H0)
    M (2*M^2) src.work (dataCap net a) (graphCap net a) z.clock (orderCap net a) (src.work+H0)
    hrows hlinks le_rfl hdata hgraph le_rfl le_rfl le_rfl
  have hout := h.trans hm
  rw [budget_source_linear,hbetaLength] at hout
  exact hout

end RiemannGaussian.SemiprimeD1ChildOriginalClock
