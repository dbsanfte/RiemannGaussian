/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1Deformation
import RiemannGaussian.SemiprimeD1PacketReplayOriginal

/-! # Exact D.8 startup from actual original sparse packet placements
Physical slot and packet bytes are read from the literal original replay.
Unique real slot addresses derive the identity wire; no desired matrix or
endpoint alignment is supplied. Polynomials below are erased specifications.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1OriginalDeformation
open scoped BigOperators
open Polynomial SemiprimeD1WireKernelPaper SemiprimeD1WireKernelOriginal
open SemiprimeBitArithmetic SemiprimeD1PacketReplayOriginal
variable {R : Type*} [CommRing R]

/-- Fixed-length physical words have unique values, including padding zeros. -/
theorem fixed_width_injective (left right : List Bool) (hlen : left.length=right.length)
    (hvalue : bitValue left=bitValue right) : left=right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons b left ih =>
    cases right with
    | nil => simp at hlen
    | cons c right =>
      have htail : left.length=right.length := by simp only [List.length_cons] at hlen;omega
      cases b <;> cases c <;> simp [bitValue,bitNat] at hvalue
      · exact congrArg (List.cons false) (ih right htail (by omega))
      · omega
      · omega
      · exact congrArg (List.cons true) (ih right htail (by omega))

/-- Original placements in their exact real incidence order. -/
abbrev Placements (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :=
  (acquire n F r a arity owner).placements

/-- Physical original packet bytes for one real edge occurrence. -/
def packet (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (i : Fin (Placements n F r a arity owner).length) : List Bool :=
  ((Placements n F r a arity owner)[i.val]).packet

/-- Original slot index with its bound derived from acquired bytes. -/
def slot (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (i : Fin (Placements n F r a arity owner).length) : Fin (2^a) :=
  ⟨bitValue ((Placements n F r a arity owner)[i.val]).slot,by
    have h := placement_valid n F r a arity owner _ (List.getElem_mem i.isLt)
    simpa only [h.2] using bitValue_lt_width ((Placements n F r a arity owner)[i.val]).slot⟩

/-- Real packet/slot addresses identify original occurrences uniquely. -/
theorem address_injective (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    Function.Injective (fun i => (packet n F r a arity owner i,slot n F r a arity owner i)) := by
  intro i j he
  have hp := congrArg Prod.fst he
  have hs := congrArg (fun value => value.2.val) he
  change packet n F r a arity owner i=packet n F r a arity owner j at hp
  have hli := (placement_valid n F r a arity owner _ (List.getElem_mem i.isLt)).2
  have hlj := (placement_valid n F r a arity owner _ (List.getElem_mem j.isLt)).2
  have hslot : ((Placements n F r a arity owner)[i.val]).slot=
      ((Placements n F r a arity owner)[j.val]).slot :=
    fixed_width_injective _ _ (hli.trans hlj.symm) hs
  have hn := List.nodup_iff_injective_getElem.mp (slots_nodup n F r a arity owner)
  have haddr : SemiprimeSourceHistogramKeyBits.frame
      ((Placements n F r a arity owner)[i.val]).packet ((Placements n F r a arity owner)[i.val]).slot=
    SemiprimeSourceHistogramKeyBits.frame
      ((Placements n F r a arity owner)[j.val]).packet ((Placements n F r a arity owner)[j.val]).slot := by
    change SemiprimeSourceHistogramKeyBits.frame (packet n F r a arity owner i) _=
      SemiprimeSourceHistogramKeyBits.frame (packet n F r a arity owner j) _
    rw [hp,hslot]
  have hi : i.val=j.val := by
    have hh := @hn ⟨i.val,by simpa only [List.length_map] using i.isLt⟩
      ⟨j.val,by simpa only [List.length_map] using j.isLt⟩
      (by simpa only [List.getElem_map] using haddr)
    exact Fin.mk.inj hh
  exact Fin.ext hi

/-- Original sparse-packet wire polynomial; no matrix executes. -/
noncomputable def wire (f : ℚ→+*R) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (i j : Fin (Placements n F r a arity owner).length) : R[X] :=
  if packet n F r a arity owner i=packet n F r a arity owner j then
    (kernel a (displacement a (slot n F r a arity owner i) (slot n F r a arity owner j)).val).map f
  else 0

/-- The original real-edge wire is the identity at zero, from slot uniqueness. -/
theorem wire_zero (f : ℚ→+*R) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (i j : Fin (Placements n F r a arity owner).length) :
    (wire f n F r a arity owner i j).eval 0=if i=j then 1 else 0 := by
  classical
  by_cases hp : packet n F r a arity owner i=packet n F r a arity owner j
  · rw [wire,ite_eq_left hp]
    have hm := Polynomial.eval_map_apply f
      (p:=kernel a (displacement a (slot n F r a arity owner i) (slot n F r a arity owner j)).val) 0
    simp only [map_zero,packet_kernel_zero] at hm
    rw [hm]
    by_cases hs : slot n F r a arity owner i=slot n F r a arity owner j
    · have hi := address_injective n F r a arity owner (Prod.ext hp hs)
      simp only [hi,ite_true,map_one]
    · have hi : i≠j := by intro he;subst j;exact hs rfl
      simp only [hs,hi,ite_false,map_zero]
  · have hi : i≠j := by intro he;subst j;exact hp rfl
    simp only [wire,hp,ite_false,eval_zero,hi]

/-- Original per-wire degree before scalar or nilpotent substitution. -/
theorem kernel_degree (a : ℕ) (d : Fin (size a)) : (kernel a d.val).natDegree ≤ size a-1 := by
  have ho : (omitted a d.val).natDegree ≤ size a-1 := by
    have h := Polynomial.natDegree_prod_le
      ((Finset.range (size a)).erase d.val) (fun q => (X-C (point a q:ℚ)))
    have he : (∑ q∈(Finset.range (size a)).erase d.val,(X-C (point a q:ℚ)).natDegree) ≤
        ∑ _q∈(Finset.range (size a)).erase d.val,1 := by
      apply Finset.sum_le_sum
      intro q _
      exact (natDegree_sub_le _ _).trans (by simp)
    have hc : ((Finset.range (size a)).erase d.val).card=size a-1 := by
      simpa only [Finset.card_range] using Finset.card_erase_of_mem (Finset.mem_range.mpr d.isLt)
    exact h.trans (by simpa only [Finset.sum_const,smul_eq_mul,mul_one,hc] using he)
  unfold kernel
  exact natDegree_mul_le.trans (by simpa only [natDegree_C,zero_add] using ho)

/-- The actual sparse original wires have the D.8 degree budget. -/
theorem wire_degree (f : ℚ→+*R) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (i j : Fin (Placements n F r a arity owner).length) :
    (wire f n F r a arity owner i j).natDegree ≤ size a-1 := by
  unfold wire
  split_ifs
  · exact Polynomial.natDegree_map_le.trans (kernel_degree a _)
  · simp

/-- D.8 at zero is the original contraction in actual real occurrence order. -/
theorem original_at_zero (f : ℚ→+*R) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (A B : (Fin (Placements n F r a arity owner).length→Bool)→R) :
    (SemiprimeD1Deformation.polynomial _ A B (wire f n F r a arity owner)).eval 0=
      ∑ bits,A bits*B bits :=
  SemiprimeD1Deformation.at_zero _ A B _ (wire_zero f n F r a arity owner)

/-- The actual sparse deformation meets the tapered-Hermite degree premise. -/
theorem original_degree (f : ℚ→+*R) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (A B : (Fin (Placements n F r a arity owner).length→Bool)→R) :
    (SemiprimeD1Deformation.polynomial _ A B (wire f n F r a arity owner)).natDegree ≤
      (Placements n F r a arity owner).length*(2*(2^a)-1) := by
  simpa only [size,pow_succ,mul_comm 2] using
    SemiprimeD1Deformation.degree_le _ (size a-1) A B _ (wire_degree f n F r a arity owner)

end RiemannGaussian.SemiprimeD1OriginalDeformation
