/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOrdinalBankExecution
/-! # Original-input actual transition bounds for the shared port/ordinal acquisition -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortOrdinalBankBounds
open SemiprimeD1StackPortOrdinalBank SemiprimeD1StackPortOrdinalBankExecution
/-- Scalar arithmetic helper, isolated from executable source definitions. -/
theorem count_numeric (M F X:ℕ) (hc:M≤F*(10*X^2)) (hf:F≤X) : M≤10*X^3 := by
  have hm:=Nat.mul_le_mul_right (10*X^2) hf
  nlinarith only [hc,hm]
/-- Pure scalar resource substitution with normalized literal coefficients. -/
theorem numeric_budget (W M X:ℕ) (hW:1≤W) (hX:1≤X) (hc:M≤10*X^3)
    (hs:X^6≤64000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000*W) :
    10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000*W+1000*(M+1)^2+3≤100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000*W := by
  have h3:1≤X^3:=by
    have hx:0<X:=by omega
    have h:0<X^3:=Nat.pow_pos hx
    omega
  have hp:M+1≤11*X^3:=by omega
  have hp2:(M+1)^2≤121*X^6:=by
    calc
      _≤(11*X^3)^2:=Nat.pow_le_pow_left hp 2
      _=121*X^6:=by ring
  omega
/-- Power substitution is proved with fresh scalar variables, before actual source expressions are instantiated. -/
theorem power_cap (n X:ℕ) (hs:X≤2000000000000000*(n+1)^5) :
    X^6≤64000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000*(n+1)^30 := by
  have h:=Nat.pow_le_pow_left hs 6
  have hC:(2000000000000000:ℕ)^6=64000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000:=by norm_num
  rw [mul_pow,←pow_mul,hC] at h
  norm_num only [show (5:ℕ)*6=30 by decide] at h
  exact h
/-- The physically acquired occurrence cardinality has an original-input resource bound. -/
theorem occurrences_le (bits:List Bool) : occurrences bits≤10*
    (SemiprimeD1StackPortCataloguePolynomial.size (SemiprimeD1StackPortCatalogueExecution.vertices bits))^3 := by
  unfold occurrences
  let vs:=SemiprimeD1StackPortCatalogueExecution.vertices bits
  let X:=SemiprimeD1StackPortCataloguePolynomial.size vs
  have hb:=SemiprimeD1StackPortCataloguePolynomial.original_bounded vs
  have h:=SemiprimeD1StackPortCataloguePolynomial.count_le vs X hb
  have hl:vs.length≤X:=(SemiprimeD1StackPortCataloguePolynomial.vertices_le_tape vs).trans
    (by unfold X SemiprimeD1StackPortCataloguePolynomial.size;omega)
  exact count_numeric _ _ X h hl
/-- Both actual suppliers are paid, with no once-only sharing beyond their literal real calls. -/
theorem budget_le (bits:List Bool) (hb:bits≠[]) : budget bits≤10^104*(bits.length+1)^30 := by
  let X:=SemiprimeD1StackPortCataloguePolynomial.size (SemiprimeD1StackPortCatalogueExecution.vertices bits)
  have hX:1≤X:=by unfold X SemiprimeD1StackPortCataloguePolynomial.size;omega
  have hc:=occurrences_le bits
  change occurrences bits≤10*X^3 at hc
  have hs:=SemiprimeD1StackPortCatalogueBounds.size_le bits hb
  have hs6:=power_cap bits.length X hs
  have hw:1≤(bits.length+1)^30:=Nat.succ_le_of_lt (Nat.pow_pos (Nat.succ_pos bits.length))
  have h100:(10:ℕ)^100=10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000:=by norm_num
  have h104:(10:ℕ)^104=100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000:=by norm_num
  have hl:=congrArg (fun c:ℕ=>c*(bits.length+1)^30+1000*(occurrences bits+1)^2+3) h100
  have hr:=congrArg (fun c:ℕ=>c*(bits.length+1)^30) h104
  calc
    budget bits=10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000*(bits.length+1)^30+1000*(occurrences bits+1)^2+3:=hl
    _≤100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000*(bits.length+1)^30:=
      numeric_budget ((bits.length+1)^30) (occurrences bits) X hw hX hc hs6
    _=10^104*(bits.length+1)^30:=hr.symm
/-- Whole original-N physical source, including actual padded M-word ID allocation. -/
theorem source_run_polynomial (bits:List Bool) (hb:bits≠[]) :
    ∃ time ≤ 10^104*(bits.length+1)^30,C.run program time (initial bits)=some (done bits) := by
  obtain ⟨m,hm,hr⟩:=source_run bits hb
  exact ⟨m,hm.trans (budget_le bits hb),hr⟩
/-- Successful executed prefixes cannot pass the actual proved final halt. -/
theorem prefix_fuel_le (bits:List Bool) (hb:bits≠[]) (fuel:ℕ) (out:C.State Stack Label)
    (hr:C.run program fuel (initial bits)=some out) : fuel≤10^104*(bits.length+1)^30 := by
  obtain ⟨time,ht,he⟩:=source_run_polynomial bits hb
  have hf:fuel≤time:=by
    by_contra hn
    have h:fuel=time+(1+(fuel-(time+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:C.run program 1 (done bits)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- ALL eighty-seven Boolean stacks and real return frames at EVERY actual source prefix. -/
theorem prefix_cells (bits:List Bool) (hb:bits≠[]) (fuel:ℕ) (out:C.State Stack Label)
    (hr:C.run program fuel (initial bits)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤10^107*(bits.length+1)^30 := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length _ out (by
    intro k
    cases k with
    | inl k =>
      change (P.input bits k).length≤bits.length
      rw [port_input]
      split <;> simp
    | inr k => exact Nat.zero_le _) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length)≤87*(bits.length+fuel):=by
    calc
      _≤∑_k:Stack,(bits.length+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits hb fuel out hr
  have hn:bits.length≤(bits.length+1)^30:=by
    have h:bits.length+1≤(bits.length+1)^30:=by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 1≤bits.length+1 by omega) (show 1≤30 by omega)
    omega
  omega
/-- ALL actual compiled-machine prefixes start from initList of binary N alone. -/
theorem machine_prefix_cells (bits:List Bool) (hb:bits≠[]) (fuel:ℕ) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤10^107*(bits.length+1)^30 := by
  have he:=SemiprimeD1StackCalls.run_correct ((portStack P.originalInput)) ids (.inl .start)
    program fuel (initial bits)
  change (C.run program fuel (initial bits)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (initial bits))) at he
  have hh:(C.run program fuel (initial bits)).map SemiprimeD1StackCalls.configuration=some cfg:=
    he.trans ((congrArg (fun start:machine.Cfg=>
      (fun q:Option machine.Cfg=>q.bind machine.step)^[fuel] (some start)) (initial_eq bits).symm).trans hr)
  cases hc:C.run program fuel (initial bits) with
  | none => rw [hc] at hh;cases hh
  | some out =>
    rw [hc] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells bits hb fuel out hc
/-- Actual finite-machine full-acquisition certificate, rather than a reported-cost assumption. -/
noncomputable def portOrdinalBankInTime (bits:List Bool) (hb:bits≠[]) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (10^104*(bits.length+1)^30) := by
  rw [initial_eq bits]
  apply SemiprimeD1StackCalls.evalsCorrect ((portStack P.originalInput)) ids (.inl .start) program
  let cert:=source_run_polynomial bits hb
  let m:=Classical.choose cert
  have hs:=Classical.choose_spec cert
  exact ⟨⟨m,hs.2⟩,hs.1⟩
end RiemannGaussian.SemiprimeD1StackPortOrdinalBankBounds
