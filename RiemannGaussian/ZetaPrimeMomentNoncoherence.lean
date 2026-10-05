/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeMomentCoherence
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Block deviation and ordinary-prime non-coherence

The exact block is `[13 N / 32, 19 N / 32] ∩ ℕ`: its lower endpoint
is rounded UP, not down. Convergence of a complex sequence forces the
mean squared deviation on these moving blocks to vanish. Positive
limsup, or a fixed positive deviation on cofinally many blocks, therefore
rules out coherence.

The converse coherence theorem gives `nonvanishing → non-coherence`.
Its contrapositive does NOT give `non-coherence → nonvanishing`. A
pointwise reverse criterion below keeps the missing forward-coherence
premise explicit. The separate strip module proves the useful global
criterion by the already-proved exposed-zero selection theorem, without
an exposure premise on the zero-free criterion itself.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaPrimeMomentNoncoherence
open ZetaPrimeMomentCoherence

/-- The integer points in the literal closed rational factorial block. -/
def block (N : ℕ) : Finset ℕ := Finset.Icc ((13*N+31)/32) (19*N/32)

/-- Mean squared deviation from `-m`, with empty-block mean defined as zero. -/
def blockDeviation (a : ℕ → ℂ) (m N : ℕ) : ℝ :=
  (∑ k ∈ block N, ‖a k+(m : ℂ)‖^2)/(block N).card

/-- No negative positive-integer source limit at this radius and height. -/
def Noncoherent (u y : ℝ) : Prop :=
  ∀ m : ℕ, 0<m → ¬Tendsto (moments u y) atTop (𝓝 (-(m : ℂ)))

/-- A fixed positive mean-square deviation occurs on cofinally many blocks. -/
def CofinalBlockDeviation (a : ℕ → ℂ) (m : ℕ) : Prop :=
  ∃ ε : ℝ, 0<ε ∧ ∃ᶠ N in atTop, ε≤blockDeviation a m N

@[simp] theorem mem_block {N k : ℕ} :
    k ∈ block N ↔ 13*N≤32*k ∧ 32*k≤19*N := by
  simp only [block, Finset.mem_Icc]
  omega

/-- The block is nonempty for every sufficiently large integer order. -/
theorem block_nonempty {N : ℕ} (hN : 32≤N) : (block N).Nonempty := by
  refine ⟨(13*N+31)/32, ?_⟩
  simp only [block, Finset.mem_Icc]
  omega

/-- Every block index tends to infinity, uniformly over the whole block. -/
theorem block_indices_eventually_ge (M : ℕ) :
    ∀ᶠ N in atTop, ∀ k ∈ block N, M≤k := by
  filter_upwards [eventually_ge_atTop (32*M)] with N hN k hk
  have h := (mem_block.mp hk).1
  omega

/-- Squared deviations and their mean are nonnegative, including empty blocks. -/
theorem blockDeviation_nonneg (a : ℕ → ℂ) (m N : ℕ) :
    0≤blockDeviation a m N := by
  unfold blockDeviation
  positivity

/-- A uniform squared-deviation bound controls the whole block average. -/
theorem blockDeviation_le {a : ℕ → ℂ} {m N : ℕ} {ε : ℝ}
    (hN : (block N).Nonempty)
    (ha : ∀ k ∈ block N, ‖a k+(m : ℂ)‖^2≤ε) :
    blockDeviation a m N≤ε := by
  have hc : (0 : ℝ)<(block N).card := by
    exact_mod_cast Finset.card_pos.mpr hN
  apply (div_le_iff₀ hc).mpr
  calc
    _ ≤ ∑ _k ∈ block N, ε := Finset.sum_le_sum ha
    _ = _ := by simp [mul_comm]

/-- A coherent source forces mean-square block deviation to tend to zero.
This is a moving-block consequence of convergence, not an arithmetic estimate. -/
theorem tendsto_blockDeviation_of_tendsto {a : ℕ → ℂ} {m : ℕ}
    (ha : Tendsto a atTop (𝓝 (-(m : ℂ)))) :
    Tendsto (blockDeviation a m) atTop (𝓝 0) := by
  have hd : Tendsto (fun k => ‖a k+(m : ℂ)‖^2) atTop (𝓝 0) := by
    simpa using ((ha.add_const (m : ℂ)).norm.pow 2)
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Eventually.of_forall (fun N => hb.trans_le (blockDeviation_nonneg a m N))
  · intro b hb
    obtain ⟨M,hM⟩ := eventually_atTop.mp (hd.eventually (gt_mem_nhds (half_pos hb)))
    filter_upwards [block_indices_eventually_ge M, eventually_ge_atTop 32] with N hNM hN
    have hle : blockDeviation a m N≤b/2 :=
      blockDeviation_le (block_nonempty hN) (fun k hk => (hM k (hNM k hk)).le)
    exact hle.trans_lt (half_lt_self hb)

/-- Positive real limsup of block deviation precludes the corresponding
negative-integer limit. No boundedness premise is needed for this implication:
convergence itself would force the real limsup to be zero. -/
theorem not_tendsto_of_pos_limsup_blockDeviation {a : ℕ → ℂ} {m : ℕ}
    (hdev : 0<limsup (blockDeviation a m) atTop) :
    ¬Tendsto a atTop (𝓝 (-(m : ℂ))) := by
  intro ha
  have hlim := (tendsto_blockDeviation_of_tendsto ha).limsup_eq
  rw [hlim] at hdev
  exact (lt_irrefl 0) hdev

/-- The cofinal positive-deviation formulation also detects unbounded
deviations, without using a default real limsup for an unbounded sequence. -/
theorem not_tendsto_of_cofinalBlockDeviation {a : ℕ → ℂ} {m : ℕ}
    (hdev : CofinalBlockDeviation a m) :
    ¬Tendsto a atTop (𝓝 (-(m : ℂ))) := by
  intro ha
  obtain ⟨ε,hε,hfreq⟩ := hdev
  have hev := (tendsto_blockDeviation_of_tendsto ha).eventually (gt_mem_nhds hε)
  obtain ⟨N,hNlo,hNhi⟩ := (hfreq.and_eventually hev).exists
  exact (not_lt_of_ge hNlo) hNhi

/-- Positive block limsup at every possible multiplicity excludes every
negative-integer coherent source at the fixed radius and height. -/
theorem noncoherent_of_pos_limsup {u y : ℝ}
    (hdev : ∀ m : ℕ, 0<m → 0<limsup (blockDeviation (moments u y) m) atTop) :
    Noncoherent u y := by
  intro m hm
  exact not_tendsto_of_pos_limsup_blockDeviation (hdev m hm)

/-- A cofinal positive mean-square block gap is an alternative sufficient
criterion for non-coherence, with no exposure or Riesz premise. -/
theorem noncoherent_of_cofinalBlockDeviation {u y : ℝ}
    (hdev : ∀ m : ℕ, 0<m → CofinalBlockDeviation (moments u y) m) :
    Noncoherent u y := by
  intro m hm
  exact not_tendsto_of_cofinalBlockDeviation (hdev m hm)

/-- The actual contrapositive of the converse coherence theorem.
It has no exposure hypothesis and does not prove the inverse implication. -/
theorem noncoherent_of_nonvanishing {u y : ℝ} (hu : 0<u) (hu1 : u<1)
    (hne : riemannZeta (candidate u y)≠0) : Noncoherent u y := by
  intro m hm ha
  obtain ⟨rho,hrho,_⟩ := exists_zero_multiplicity_of_tendsto hu hu1 hm ha
  exact hne (hrho ▸ rho.2.1)

/-- A POINTWISE zero-free criterion requires the additional forward
implication explicitly. Non-coherence alone is not its contrapositive. -/
theorem nonvanishing_of_noncoherent_of_forward {u y : ℝ}
    (hforward : riemannZeta (candidate u y)=0 →
      ∃ m : ℕ, 0<m ∧ Tendsto (moments u y) atTop (𝓝 (-(m : ℂ))))
    (hnc : Noncoherent u y) : riemannZeta (candidate u y)≠0 := by
  intro hz
  obtain ⟨m,hm,ha⟩ := hforward hz
  exact hnc m hm ha

/-- The pointwise characterization is valid once the missing forward
coherence theorem is supplied; the converse supplies the other direction. -/
theorem nonvanishing_iff_noncoherent_of_forward {u y : ℝ} (hu : 0<u) (hu1 : u<1)
    (hforward : riemannZeta (candidate u y)=0 →
      ∃ m : ℕ, 0<m ∧ Tendsto (moments u y) atTop (𝓝 (-(m : ℂ)))) :
    riemannZeta (candidate u y)≠0 ↔ Noncoherent u y := by
  exact ⟨noncoherent_of_nonvanishing hu hu1,
    nonvanishing_of_noncoherent_of_forward hforward⟩

/-- Pointwise positive block limsup gives nonvanishing WHEN a forward
zero-to-coherence theorem is also supplied. That premise is not hidden. -/
theorem nonvanishing_of_pos_limsup_of_forward {u y : ℝ}
    (hforward : riemannZeta (candidate u y)=0 →
      ∃ m : ℕ, 0<m ∧ Tendsto (moments u y) atTop (𝓝 (-(m : ℂ))))
    (hdev : ∀ m : ℕ, 0<m → 0<limsup (blockDeviation (moments u y) m) atTop) :
    riemannZeta (candidate u y)≠0 := by
  exact nonvanishing_of_noncoherent_of_forward hforward (noncoherent_of_pos_limsup hdev)

/-- The analogous pointwise criterion for cofinal fixed positive block gaps. -/
theorem nonvanishing_of_cofinalBlockDeviation_of_forward {u y : ℝ}
    (hforward : riemannZeta (candidate u y)=0 →
      ∃ m : ℕ, 0<m ∧ Tendsto (moments u y) atTop (𝓝 (-(m : ℂ))))
    (hdev : ∀ m : ℕ, 0<m → CofinalBlockDeviation (moments u y) m) :
    riemannZeta (candidate u y)≠0 := by
  exact nonvanishing_of_noncoherent_of_forward hforward
    (noncoherent_of_cofinalBlockDeviation hdev)

end RiemannGaussian.ZetaPrimeMomentNoncoherence
