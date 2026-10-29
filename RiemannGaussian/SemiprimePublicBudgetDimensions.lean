/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeFullSetupPublicController

/-! # Polynomial public dimensions used by the actual counter budget
These bounds concern the original indexed public graph and retained local and
decoder reports. They do not charge public graph construction or assert a
complete primitive-bit clock.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimePublicBudgetDimensions
open SemiprimePublicAcquiredExecution SemiprimeMacroParameters

/-- The literal public input width is bounded by the actual wire count. -/
theorem bitLength_le (N : ℕ) (hN : 0<N) : bitLength N ≤ wireCount N := by
  rw [wireCount_eq]
  exact input_le_variableCount (bitLength_pos hN)

/-- The literal transform dimension has a uniform polynomial wire envelope. -/
theorem transform_le (N : ℕ) (hN : 0<N) : transformLength (bitLength N) ≤ 64*wireCount N := by
  have hu := transform_square_upper (bitLength_pos hN)
  have hl := bitLength_le N hN
  have hs : transformLength (bitLength N) ≤ transformLength (bitLength N)^2 := Nat.le_self_pow (by decide) _
  omega

/-- Both actual axes are bounded by their positive product. -/
theorem axes_le_transform (L : ℕ) (hL : 0<L) :
    firstAxis L ≤ transformLength L ∧ secondAxis L ≤ transformLength L := by
  have hp := axes_product L
  have hg := axes_ge_two hL
  constructor <;> nlinarith

/-- The actual active digit count and radix width have polynomial wire envelopes. -/
theorem digit_radix_le (N : ℕ) (hN : 0<N) :
    digitCount (bitLength N) ≤ 64*wireCount N ∧ radixBits (bitLength N) ≤ 64*wireCount N := by
  have hd := digitCount_bounds (bitLength_pos hN)
  have hr := transform_eq_four_radixBits (bitLength_pos hN)
  have ht := transform_le N hN
  omega

/-- All original and equality factors fit within the actual public wire count. -/
theorem factorCount_le (N : ℕ) (hN : 0<N) : factorCount N ≤ wireCount N := by
  have hd := digitCount_bounds (bitLength_pos hN)
  have ha := axes_le_transform (bitLength N) (bitLength_pos hN)
  have hk := (transform_loop_characterization (bitLength_pos hN)).1
  rw [factorCount, (vertexEnumeration N).length_eq_card, wireCount_eq, variableCount]
  rw [SemiprimeMacroGraph.subdivided_vertex_card _ _ _ hd.1,
    SemiprimeMacroGraph.edge_card _ _ _ hd.1, axes_product]
  have hs : 2 ≤ (13*transformLength (bitLength N)+1)*(transformLength (bitLength N)+1)+
      4*digitCount (bitLength N) := by omega
  have he := Nat.sub_add_cancel hs
  nlinarith

/-- A polynomial scope envelope used only in polynomial preprocessing costs. -/
def scopeEnvelope (n : ℕ) : ℕ := (256*n+3)*(64*n+1)

/-- This coarse scope envelope is not substituted into an exponential table size. -/
theorem scope_le (N : ℕ) (hN : 0<N) : scopeBound (bitLength N) ≤ scopeEnvelope (wireCount N) := by
  have ha := axes_le_transform (bitLength N) (bitLength_pos hN)
  have ht := transform_le N hN
  unfold scopeBound scopeEnvelope
  apply Nat.mul_le_mul <;> omega

/-- Fixed polynomial envelope of the original local-checker and prefix report. -/
def entryEnvelope (n : ℕ) : ℕ :=
  1048576*(64*n+2)^10+n*(3*scopeEnvelope n+2)+1

/-- The same derived polynomial bound covers every reachable-prefix entry budget. -/
theorem entryBudget_le (N : ℕ) (hN : 0<N) :
    SemiprimeFullSetupPublicController.entryBudget N ≤ entryEnvelope (wireCount N) := by
  have hl := bitLength_le N hN
  have hs := scope_le N hN
  unfold SemiprimeFullSetupPublicController.entryBudget entryEnvelope
  gcongr

/-- Fixed polynomial selected-operation decoder envelope for at most n labels. -/
def decoderEnvelope (n : ℕ) : ℕ :=
  64*n*((64*n+1)*(8*n+9)+128*n+8)+128*n+3*(64*n+1)^2+3

/-- The actual retained decoder report needs no extra nonuniform width premise. -/
theorem decoderBudget_le (N : ℕ) (hN : 0<N) (v : ℕ) (hv : v ≤ wireCount N) :
    SemiprimePaidFactorDecoder.budget N v ≤ decoderEnvelope (wireCount N) := by
  have ht := transform_le N hN
  obtain ⟨hd,hr⟩ := digit_radix_le N hN
  unfold SemiprimePaidFactorDecoder.budget decoderEnvelope
  rw [axes_product]
  calc
    _  ≤  64*wireCount N*((64*wireCount N+1)*(2*wireCount N+6*wireCount N+9)+
        2*(64*wireCount N)+8)+2*(64*wireCount N)+3*(64*wireCount N+1)^2+3 := by gcongr
    _ = _ := by ring

end RiemannGaussian.SemiprimePublicBudgetDimensions
