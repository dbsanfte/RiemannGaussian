/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetUnitExecution
/-! # All-prefix physical unit-vector acquisition bounds -/
set_option autoImplicit false
set_option synthInstance.maxSize 8192
set_option maxRecDepth 8192
namespace RiemannGaussian.SemiprimeD1StackJetUnitBounds
open SemiprimeD1StackJetUnit SemiprimeD1StackJetUnitExecution
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1JetAxes (Context)

/-- Every successful original prefix ends by the actual proved halt. -/
theorem prefix_fuel_le (ctx : Context) (width rank : List Bool) (hw : width.length=ctx.precision)
    (hrank : rank.length=ctx.rank) (fuel : ℕ) (out : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial width rank)=some out) :
    fuel ≤ timeBound width.length rank.length := by
  have hf : fuel ≤ totalTime width rank := by
    by_contra hn
    have he : fuel=totalTime width rank+(1+(fuel-(totalTime width rank+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,source_run ctx width rank hw hrank,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hh : SemiprimeD1StackCalls.run program 1
        (⟨none,none,none,bank width rank [] [] (vectorBits (SemiprimeD1JetAffineCoefficient.one ctx).words),[]⟩:
          SemiprimeD1StackCalls.State Stack Label)=none := rfl
    rw [hh,Option.bind_none] at hr
    cases hr
  exact hf.trans (totalTime_le width rank)

/-- All physical data and real return frames are polynomially bounded. -/
theorem prefix_cells (ctx : Context) (width rank : List Bool) (hw : width.length=ctx.precision)
    (hrank : rank.length=ctx.rank) (fuel : ℕ) (out : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial width rank)=some out) :
    (∑s:Stack,(out.data s).length)+out.frames.length ≤
      16*(width.length+rank.length+timeBound width.length rank.length+1) := by
  have hf:=prefix_fuel_le ctx width rank hw hrank fuel out hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (width.length+rank.length) _ out (by
    intro k
    rcases k with k|k
    · rcases k with k|k
      · cases k <;> simp [initial,bank,SemiprimeD1StackJetAdd.store,SemiprimeD1StackJetScalarAdd.store]
      · cases k <;> simp [initial,bank,SemiprimeD1StackJetAdd.store,SemiprimeD1StackJetScalarAdd.store]
    · cases k <;> simp [initial,bank,SemiprimeD1StackJetAdd.store]) hr
  have hframes:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hframes
  have hs : (∑s:Stack,(out.data s).length) ≤ 15*(width.length+rank.length+fuel) := by
    calc
      _ ≤ ∑_s:Stack,(width.length+rank.length+fuel) := Finset.sum_le_sum (fun s _=>hd s)
      _ = 15*(width.length+rank.length+fuel) := by
        have hc : Fintype.card Stack=15 := by decide
        simp [hc]
  omega

/-- The same all-prefix cap holds for the actual compiled finite machine. -/
theorem machine_prefix_cells (ctx : Context) (width rank : List Bool) (hw : width.length=ctx.precision)
    (hrank : rank.length=ctx.rank) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial width rank)))=some cfg) :
    (∑s:Stack,(cfg.stk (some s)).length)+(cfg.stk none).length ≤
      16*(width.length+rank.length+timeBound width.length rank.length+1) := by
  let start:=initial width rank
  have he:=SemiprimeD1StackCalls.run_correct widthCache output Label.seed0 program fuel start
  change (SemiprimeD1StackCalls.run program fuel start).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration start)) at he
  cases hc:SemiprimeD1StackCalls.run program fuel start with
  | none => rw [hc,hr] at he; cases he
  | some out =>
    rw [hc,hr] at he
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj he
    rw [←hcfg]
    exact prefix_cells ctx width rank hw hrank fuel out hc

end RiemannGaussian.SemiprimeD1StackJetUnitBounds
