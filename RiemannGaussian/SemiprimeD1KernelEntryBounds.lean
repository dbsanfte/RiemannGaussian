/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1KernelEntryBits

/-! # Original-dimension bounds for the acquired physical entry
All factors, contents and division widths are derived from actual grid words.
The clock retains digit-stage reports; lowering native dimension/displacement
and digit primitives to one tape machine remains a separate obligation.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1KernelEntryBounds
open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitIndexClipping
open SemiprimeD1RecoveryIntegerBits SemiprimeD1KernelEntryBits
open SemiprimeD1WireKernelOriginal

/-- Actual skip/normalization budget per original grid item. -/
def stepBudget (k W : ℕ) : ℕ :=
  41*(W+1)+3*(W+1)+1+SemiprimeD1NormalizedLinearBits.budget k W+5

/-- Cached acquisition cannot create additional grid factors. -/
theorem gather_length (k : ℕ) (j d : List Bool) (qs : List (List Bool)) :
    (gather k j d qs).values.length≤qs.length := by
  rw [gather_values,List.length_map]
  exact List.length_filter_le _ _

/-- Every actual retained factor inherits widths from original grid words. -/
theorem gather_width (k W : ℕ) (j d : List Bool) (qs : List (List Bool))
    (hj:j.length≤W) (hqs:∀q∈qs,q.length≤W)
    (f : SemiprimeD1NormalizedLinearBits.Run) (hf:f∈(gather k j d qs).values) :
    f.content.length≤k+W+2 ∧f.constant.magnitude.length≤W+1 ∧f.slope.length≤k+1 := by
  rw [gather_values] at hf
  obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hf
  have hmem: q∈qs:=(List.mem_filter.mp hq).1
  exact SemiprimeD1NormalizedLinearBits.acquire_width k W j q hj (hqs q hmem)

/-- All skip scans and actual retained factor callbacks are paid. -/
theorem gather_clock (k W : ℕ) (j d : List Bool) (qs : List (List Bool))
    (hj:j.length≤W) (hd:d.length≤W) (hqs:∀q∈qs,q.length≤W) :
    (gather k j d qs).clock≤qs.length*stepBudget k W+1 := by
  induction qs with
  | nil => simp only [gather,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons q qs ih =>
    have hq:=hqs q List.mem_cons_self
    have ht:=ih (fun z hz=>hqs z (List.mem_cons_of_mem q hz))
    have hs:=subSignedBits_cost_width (left:=positive q) (right:=positive d) hq hd
    have hn:=nonzeroBits_cost (subSignedBits (positive q) (positive d)).word.magnitude
    have hf:=SemiprimeD1NormalizedLinearBits.acquire_clock k W j q hj hq
    dsimp only [gather]
    split <;> dsimp only <;>
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul] <;> unfold stepBudget at * <;> omega

/-- Original numerator content word width. -/
def contentWidth (a N : ℕ) : ℕ := 2*N*(2*a+5)+1

/-- Original derivative content word width. -/
def denominatorWidth (a N : ℕ) : ℕ := 2*N*(a+2)+2

/-- Monotonicity of the already executed short-factor product budget. -/
theorem product_budget_mono (n N W : ℕ) (h:n≤N) :
    SemiprimeD1KernelProductBits.budget n W≤SemiprimeD1KernelProductBits.budget N W := by
  unfold SemiprimeD1KernelProductBits.budget
  gcongr

/-- Original grid words bound the full cached content product. -/
theorem numerator_width (a : ℕ) (t : Fin (size a)) (x y : Fin (2^a)) :
    (SemiprimeD1KernelEntryBits.acquireOriginal a t x y).numeratorContent.length≤contentWidth a (size a) := by
  let grid:=SemiprimeSourceCompactWordIds.acquire (size a)
  let j:=SemiprimeEncodedRowSelection.digits (a+1) t.val
  let d:=SemiprimeEncodedRowSelection.digits (a+1) (displacement a x y).val
  let fs:=gather (a+1) j.bits d.bits grid.value
  have hj:j.bits.length≤a+2:=by rw [SemiprimeEncodedRowSelection.digits_length];omega
  have hgrid:∀q∈grid.value,q.length≤a+2:=by
    intro q hq
    exact (SemiprimeD1KernelDenominatorBits.grid_width a q hq).trans (by omega)
  have hlen:fs.values.length≤ size a:=(gather_length _ _ _ _).trans
    (by rw [SemiprimeSourceCompactWordIds.acquire_length])
  have hw:∀w∈fs.values.map (fun f=>positive f.content),w.magnitude.length≤2*a+5:=by
    intro w hw
    obtain ⟨f,hf,rfl⟩:=List.mem_map.mp hw
    have h:=(gather_width (a+1) (a+2) j.bits d.bits grid.value hj hgrid f hf).1
    change f.content.length≤_
    omega
  have hp:=SemiprimeD1KernelProductBits.run_width _ (2*a+5) hw
  rw [List.length_map] at hp
  change (SemiprimeD1KernelProductBits.run _).word.magnitude.length≤_
  unfold contentWidth
  exact hp.trans (by gcongr)

/-- Derivative content width follows the actual derivative and strip recursion. -/
theorem denominator_content_width (a : ℕ) :
    (SemiprimeD1KernelDenominatorBits.run a).content.length≤denominatorWidth a (size a) := by
  have hs:=(SemiprimeD1RecoveryStripBits.lengths
    (SemiprimeD1KernelDenominatorBits.raw a).word.magnitude).1
  have hr:=SemiprimeD1KernelDenominatorBits.raw_width a
  change (SemiprimeD1RecoveryStripBits.acquire
    (SemiprimeD1KernelDenominatorBits.raw a).word.magnitude).content.length≤_
  unfold denominatorWidth
  omega

/-- Quotient width is derived from the positive actual derivative content. -/
theorem powerFactor_width (a : ℕ) (t : Fin (size a)) (x y : Fin (2^a)) :
    (SemiprimeD1KernelEntryBits.acquireOriginal a t x y).powerFactor.length≤contentWidth a (size a) := by
  have hp:0<bitValue (SemiprimeD1KernelDenominatorBits.run a).content:=by
    rw [SemiprimeD1KernelDenominatorBits.run_content];positivity
  have hw:=(divideBits_widths (xs:=(SemiprimeD1KernelEntryBits.acquireOriginal a t x y).numeratorContent) hp).2
  change (divideBits _ _).quotient.length≤_
  exact hw.le.trans (numerator_width a t x y)

/-- Fixed polynomial in original grid dimensions, with every repeated setup retained. -/
def budget (a N : ℕ) : ℕ :=
  N*(30*(a+4)+20)+1+2*(4*(a+1)+1)+N*stepBudget (a+1) (a+2)+1+
  SemiprimeD1KernelProductBits.budget N (2*a+5)+
  SemiprimeD1KernelDenominatorBits.budget a N+
  contentWidth a N*(16*denominatorWidth a N+20)+7*denominatorWidth a N+4+12

/-- Original cached factor count and all literal factor widths. -/
theorem acquire_factor_bounds (a : ℕ) (t : Fin (size a)) (x y : Fin (2^a)) :
    (SemiprimeD1KernelEntryBits.acquireOriginal a t x y).factors.length≤ size a ∧
    ∀f∈(SemiprimeD1KernelEntryBits.acquireOriginal a t x y).factors,
      f.content.length≤2*a+5 ∧f.constant.magnitude.length≤a+3 ∧f.slope.length≤a+2 := by
  constructor
  · exact (gather_length _ _ _ _).trans (by rw [SemiprimeSourceCompactWordIds.acquire_length])
  · intro f hf
    have hj:(SemiprimeEncodedRowSelection.digits (a+1) t.val).bits.length≤a+2:=by
      rw [SemiprimeEncodedRowSelection.digits_length];omega
    have hg:∀q∈(SemiprimeSourceCompactWordIds.acquire (size a)).value,q.length≤a+2:=by
      intro q hq
      exact (SemiprimeD1KernelDenominatorBits.grid_width a q hq).trans (by omega)
    have h:=gather_width (a+1) (a+2) _ _ _ hj hg f hf
    rcases h with ⟨hc,hm,hs⟩
    exact ⟨by omega,by omega,by omega⟩

/-- Full acquisition clock from original dimensions, with no supplied answers. -/
theorem acquire_clock (a : ℕ) (t : Fin (size a)) (x y : Fin (2^a)) :
    (SemiprimeD1KernelEntryBits.acquireOriginal a t x y).clock≤budget a (size a) := by
  let grid:=SemiprimeSourceCompactWordIds.acquire (size a)
  let j:=SemiprimeEncodedRowSelection.digits (a+1) t.val
  let d:=SemiprimeEncodedRowSelection.digits (a+1) (displacement a x y).val
  let fs:=gather (a+1) j.bits d.bits grid.value
  let numerator:=SemiprimeD1KernelProductBits.run (fs.values.map (fun f=>positive f.content))
  let denominator:=SemiprimeD1KernelDenominatorBits.run a
  let power:=divideBits numerator.word.magnitude denominator.content
  have hj:j.bits.length≤a+2:=by rw [SemiprimeEncodedRowSelection.digits_length];omega
  have hd:d.bits.length≤a+2:=by rw [SemiprimeEncodedRowSelection.digits_length];omega
  have hgrid:∀q∈grid.value,q.length≤a+2:=by
    intro q hq
    exact (SemiprimeD1KernelDenominatorBits.grid_width a q hq).trans (by omega)
  have hfs:fs.clock≤ size a*stepBudget (a+1) (a+2)+1:=by
    have h:=gather_clock (a+1) (a+2) j.bits d.bits grid.value hj hd hgrid
    rw [SemiprimeSourceCompactWordIds.acquire_length] at h
    exact h
  have hlen:fs.values.length≤ size a:=(gather_length _ _ _ _).trans
    (by rw [SemiprimeSourceCompactWordIds.acquire_length])
  have hw:∀w∈fs.values.map (fun f=>positive f.content),w.magnitude.length≤2*a+5:=by
    intro w hw
    obtain ⟨f,hf,rfl⟩:=List.mem_map.mp hw
    have h:=(gather_width (a+1) (a+2) j.bits d.bits grid.value hj hgrid f hf).1
    change f.content.length≤_
    omega
  have hn:numerator.clock≤SemiprimeD1KernelProductBits.budget (size a) (2*a+5):=by
    have h:=SemiprimeD1KernelProductBits.run_clock _ (2*a+5) hw
    rw [List.length_map] at h
    exact h.trans (product_budget_mono _ _ _ hlen)
  have hnum:numerator.word.magnitude.length≤contentWidth a (size a):=numerator_width a t x y
  have hden:denominator.content.length≤denominatorWidth a (size a):=denominator_content_width a
  have hdiv:power.clock≤contentWidth a (size a)*(16*denominatorWidth a (size a)+20)+
      7*denominatorWidth a (size a)+4:=by
    have h:=divideBits_cost numerator.word.magnitude denominator.content
    exact h.trans (by gcongr)
  have hdc:denominator.clock≤SemiprimeD1KernelDenominatorBits.budget a (size a):=
    SemiprimeD1KernelDenominatorBits.run_clock a
  have hjc:j.work=4*(a+1)+1:=SemiprimeEncodedRowSelection.digits_work _ _
  have hdd:d.work=4*(a+1)+1:=SemiprimeEncodedRowSelection.digits_work _ _
  have hid:grid.work≤ size a*(30*(a+4)+20)+1:=by
    have h:=SemiprimeSourceCompactWordIds.acquire_clock (size a)
    have hn:1≤ size a:=by unfold size;exact Nat.one_le_two_pow
    have hl:Nat.clog 2 (size a+1)≤a+2:=by
      apply Nat.clog_le_of_le_pow
      have he:2^(a+2)=2*size a:=by unfold size;rw [show a+2=(a+1)+1 by omega,pow_succ];ring
      rw [he];omega
    have hs:SemiprimeSourceCompactWordIds.stepBudget (size a)≤30*(a+4)+20:=by
      unfold SemiprimeSourceCompactWordIds.stepBudget;omega
    exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hs) 1)
  change grid.work+j.work+d.work+fs.clock+numerator.clock+denominator.clock+power.clock+12≤_
  unfold budget
  omega

/-- Literal retained Boolean payload in one cached normalized factor. -/
def factorCells (f : SemiprimeD1NormalizedLinearBits.Run) : ℕ :=
  f.content.length+f.constant.magnitude.length+f.slope.length

/-- Finite metadata-list summation counts every retained cell. -/
theorem list_cells_le {α : Type} (xs : List α) (cells : α→ℕ) (C : ℕ)
    (h:∀x∈xs,cells x≤C) : (xs.map cells).sum≤xs.length*C := by
  induction xs with
  | nil => simp only [List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,le_refl]
  | cons x xs ih =>
    have hx:=h x List.mem_cons_self
    have ht:=ih (fun y hy=>h y (List.mem_cons_of_mem x hy))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- Original factor count and widths give a concrete retained-cache payload bound. -/
theorem acquire_factor_cells (a : ℕ) (t : Fin (size a)) (x y : Fin (2^a)) :
    (((SemiprimeD1KernelEntryBits.acquireOriginal a t x y).factors).map factorCells).sum≤
      size a*(4*a+10) := by
  have hb:=acquire_factor_bounds a t x y
  have hh:=list_cells_le (SemiprimeD1KernelEntryBits.acquireOriginal a t x y).factors
    factorCells (4*a+10) (by
      intro f hf
      rcases hb.2 f hf with ⟨hc,hm,hs⟩
      unfold factorCells
      omega)
  exact hh.trans (Nat.mul_le_mul_right _ hb.1)

end RiemannGaussian.SemiprimeD1KernelEntryBounds
