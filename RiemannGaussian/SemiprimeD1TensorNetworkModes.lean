/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorNetworkRecursion
import RiemannGaussian.SemiprimeD1OriginalModeAcquisition
import RiemannGaussian.SemiprimeD1CatalogSize

/-! # Uniform actual mode acquisition from literal network histories
All graph, packing, inherited-precision and positive-level guards are derived
from the literal data and the fixed original-scale schedule. No labels, packets,
mode lists, precision envelope, or packing-acceptance answers are inputs.
The bounds remain acquisition/list/physical-word reports, not a final bit clock.
-/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace RiemannGaussian.SemiprimeD1TensorNetworkModes
open SemiprimeD1TensorNetwork SemiprimeD1TensorNetworkLayout
open SemiprimeD1TensorNetworkRecursion SemiprimeD1Schedule

/-- Acquire the ORIGINAL source and actual menu at one computed history node. -/
def acquire (s depth p0 : ℕ) (history : ℕ → Network) (phase : ℕ → ℕ) :=
  let lam := SemiprimeD1PackingReady.logarithm s
  let net := history depth
  SemiprimeD1OriginalModeAcquisition.acquire net.leftCount net.rows.length 64
    (exponent lam depth) (levels lam depth) (phase depth)
    (precision lam (fun j => edgeCount (history j)) phase p0 depth)
    (arity net.rows) (owner net.rows)

/-- Actual catalogue dimension, determined by the just-acquired sparse packets
and the executed working precision, rather than a catalogue-size input. -/
def catalogueLength (s depth p0 : ℕ) (history : ℕ → Network) (phase : ℕ → ℕ) : ℕ :=
  let source := acquire s depth p0 history phase
  (SemiprimeD1ModeCatalog.catalog (source.packets.state.packets.length*2^(phase depth+1))
    (source.precision-1)).length

/-- Explicit retained original packet/catalogue/controller report envelope.
Every finite dimension and the working precision are computed from the actual
history. Host scalar/control and final memory/address lowering stay explicit. -/
noncomputable def workBudget (s depth p0 : ℕ) (history : ℕ → Network) (phase : ℕ → ℕ) : ℝ :=
  let lam := SemiprimeD1PackingReady.logarithm s
  let net := history depth
  let a := exponent lam depth
  let u := levels lam depth
  let i := phase depth
  let p := precision lam (fun j => edgeCount (history j)) phase p0 depth
  let M := edgeCount net
  let count := (SemiprimeD1PacketReplayOriginal.acquire net.leftCount net.rows.length 64 a
    (arity net.rows) (owner net.rows)).state.packets.length
  let P := SemiprimeD1ModeRate.modeBudget M u a i p
  (SemiprimeD1PacketReplayBudget.budget net.leftCount net.rows.length 64 a M+
    M+count+a+i+u+p+20 : ℕ) +
    (SemiprimeD1WeightedCardinality.modeFactor (count*2^(i+1)) P : ℝ)*
      Real.exp (48*(M : ℝ)/Real.sqrt (u : ℝ)) +
    (SemiprimeD1WeightedCardinality.modeOverhead (count*2^(i+1)) P : ℝ)

/-- Every active node in EVERY literal network history has the actual acquired
menu exponent48M/sqrt(u), AND its full catalogue has dimension at most246M².
Earlier active-path size conditions are structural history invariants; no
per-node packing or precision acceptance condition is assumed. -/
theorem eventually_acquisition : ∀ᶠ s : ℕ in Filter.atTop,
    ∀ (depth p0 : ℕ) (history : ℕ → Network) (phase : ℕ → ℕ),
      p0 ≤ s → WellFormed (history depth) →
      DegreeBound (history depth) (SemiprimeD1PackingReady.degreeCap s) →
      (∀ j < depth, edgeCount (history j) ≤ s ∧
        levels (SemiprimeD1PackingReady.logarithm s) j ≤ edgeCount (history j)) →
      Active s (SemiprimeD1PackingReady.logarithm s) depth (edgeCount (history depth)) →
      phase depth < levels (SemiprimeD1PackingReady.logarithm s) depth →
      (((acquire s depth p0 history phase).modes.values.length : ℝ) ≤
        Real.exp (48*(edgeCount (history depth) : ℝ)/
          Real.sqrt (levels (SemiprimeD1PackingReady.logarithm s) depth : ℕ))) ∧
      catalogueLength s depth p0 history phase ≤ 246*(edgeCount (history depth))^2 ∧
      ((acquire s depth p0 history phase).work : ℝ) ≤ workBudget s depth p0 history phase := by
  filter_upwards [SemiprimeD1PackingReady.eventually_all_depths] with s hs
  intro depth p0 history phase hp0 hw hd hpath hactive hi
  let lam := SemiprimeD1PackingReady.logarithm s
  let net := history depth
  let a := exponent lam depth
  let u := levels lam depth
  let i := phase depth
  let p := precision lam (fun j => edgeCount (history j)) phase p0 depth
  have hg := hs depth (edgeCount net) (SemiprimeD1PackingReady.degreeCap s) hactive le_rfl
  have hdegree := original_degree_contract net hw (SemiprimeD1PackingReady.degreeCap s) a hd
  have hnumeric := active_guards s lam depth (fun j => edgeCount (history j)) phase p0 hp0 hpath hactive hi
  have hpos : 0 < u := active_positive s lam depth (edgeCount net) hactive
  have hM : (SemiprimeD1CollisionOriginal.ports net.leftCount net.rows.length a (arity net.rows)).length =
      edgeCount net := by rw [original_ports]; rfl
  have hsmall : 2*(64^(2*a))^2*SemiprimeD1PackingReady.degreeCap s ≤
      (SemiprimeD1CollisionOriginal.ports net.leftCount net.rows.length a (arity net.rows)).length := by
    rw [hM]
    exact hg.1.le
  have hsize : 64^(2*a)*2^a ≤
      (SemiprimeD1CollisionOriginal.ports net.leftCount net.rows.length a (arity net.rows)).length := by
    rw [hM]
    exact hg.2.1.le
  have hmenu := SemiprimeD1OriginalModeAcquisition.menu_bound net.leftCount net.rows.length 64 a u i p
    (arity net.rows) (owner net.rows) (SemiprimeD1PackingReady.degreeCap s)
    hdegree.1 hdegree.2 hsmall hsize hnumeric.1 hpos
    (by rw [hM]; exact hactive.2.2) (by rw [hM]; exact hnumeric.2.1)
    hnumeric.2.2
  rw [hM] at hmenu
  have hwork := SemiprimeD1OriginalModeAcquisition.work_bound net.leftCount net.rows.length 64 a u i p
    (arity net.rows) (owner net.rows) (SemiprimeD1PackingReady.degreeCap s)
    hdegree.1 hdegree.2 hsmall hsize hnumeric.1 hpos
    (by rw [hM]; exact hactive.2.2) (by rw [hM]; exact hnumeric.2.1)
    hnumeric.2.2
  dsimp only at hwork
  rw [hM] at hwork
  refine ⟨hmenu, ?_, hwork⟩
  have hpackets := SemiprimeD1PacketReplayCapacity.threeM_capacity net.leftCount net.rows.length 64 a
    (arity net.rows) (owner net.rows) (SemiprimeD1PackingReady.degreeCap s)
    hdegree.1 hdegree.2 hsmall hsize
  rw [hM] at hpackets
  have hcatalog := SemiprimeD1CatalogSize.catalog_quadratic
    (SemiprimeD1PacketReplayOriginal.acquire net.leftCount net.rows.length 64 a (arity net.rows)
      (owner net.rows)).state.packets.length (edgeCount net) u a i p
    hnumeric.1 hpackets hpos hactive.2.2 hnumeric.2.1 hnumeric.2.2
  change (SemiprimeD1ModeCatalog.catalog _
    ((SemiprimeD1OriginalModeAcquisition.acquire net.leftCount net.rows.length 64 a u i p
      (arity net.rows) (owner net.rows)).precision-1)).length ≤ _
  rw [SemiprimeD1OriginalModeAcquisition.precision_original, hM]
  exact hcatalog

end RiemannGaussian.SemiprimeD1TensorNetworkModes
