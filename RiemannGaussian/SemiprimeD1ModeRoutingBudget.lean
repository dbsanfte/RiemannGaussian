/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ModeRoutingBits
import RiemannGaussian.SemiprimeD1ChildMetadataPrimitives

/-! # Actual packet-key routing parser/copy costs
Every field and temporary is bounded from the original key bytes and axis count,
including malformed packets. No semantic colours or routing answer is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace RiemannGaussian.SemiprimeD1ModeRoutingBudget
open SemiprimeD1OrientationInverse SemiprimeD1OrientationInverseBounds
open SemiprimeD1ModeRoutingBits SemiprimeSourceHistogramKeyBits
open SemiprimeSourceCompactBits SemiprimeD1ChildMetadataPrimitives

/-- Every inverse-recovered colour is an original key slice or its physical copy. -/
theorem recover_fields (key slots : List Bool) :
    (∀x∈(recover key slots).left,x.length ≤ key.length) ∧
    (∀x∈(recover key slots).right,x.length ≤ key.length) := by
  induction slots generalizing key with
  | nil => simp [recover]
  | cons bit slots ih =>
    let field:=split key
    let colours:=split field.first
    let tail:=recover field.rest slots
    have hf:=split_metrics key
    have hc:=split_metrics field.first
    have hl : colours.first.length ≤ key.length:=hc.1.trans hf.1
    have hr : colours.rest.length ≤ key.length:=hc.2.1.trans hf.1
    have ht:=ih field.rest
    constructor
    · intro x hx
      change x∈(copy (if _ then _ else if bit then _ else _)).bits::tail.left at hx
      rw [copy_bits] at hx
      rcases List.mem_cons.mp hx with rfl|hx
      · split_ifs <;> assumption
      · exact (ht.1 x hx).trans hf.2.1
    · intro x hx
      change x∈(copy (if _ then _ else if bit then _ else _)).bits::tail.right at hx
      rw [copy_bits] at hx
      rcases List.mem_cons.mp hx with rfl|hx
      · split_ifs <;> assumption
      · exact (ht.2 x hx).trans hf.2.1

/-- Physical source and target colour copies cannot exceed their input key. -/
theorem route_lengths (key : List Bool) (a : ℕ) (i : Fin a) (tile : Fin (2^(i.val+1))) :
    (acquire key a i tile).source.length ≤ key.length ∧ (acquire key a i tile).target.length ≤ key.length := by
  let classes:=recover key (zeros a).bits
  have hf:=recover_fields key (zeros a).bits
  have hl:=coordinate_length classes.left i.val key.length hf.1
  have hr:=coordinate_length classes.right i.val key.length hf.2
  simp only [acquire,copy_bits]
  constructor <;> split_ifs <;> assumption

/-- Fixed physical routing polynomial; T is the actually bounded tile encoding
range, never a precomputed routing catalogue. -/
def budget (a K T : ℕ) : ℕ :=
  4*a+2+200*(a+1)*(K+a+1)+2*(4*a+3*K+4)+
    SemiprimeSourceHistogramPortKeys.encodeBudget T+4*a+2+40*(K+1)+2*(3*K+1)+20

/-- Actual physical inverse, coordinate, bit, compare and copy report. -/
theorem acquire_clock (key : List Bool) (a : ℕ) (i : Fin a) (tile : Fin (2^(i.val+1))) (K : ℕ)
    (hk : key.length ≤ K) : (acquire key a i tile).clock ≤ budget a K (2^a) := by
  let classes:=recover key (zeros a).bits
  let low:=SemiprimeD1ChildGraph.readCoordinate classes.left i.val
  let high:=SemiprimeD1ChildGraph.readCoordinate classes.right i.val
  let tileBits:=SemiprimeSourceHistogramPortKeys.encodeKey tile.val
  let bit:=readBit tileBits.bits i.val
  have hf:=recover_fields key (zeros a).bits
  have hl:low.bits.length ≤ K:=(coordinate_length classes.left i.val key.length hf.1).trans hk
  have hr:high.bits.length ≤ K:=(coordinate_length classes.right i.val key.length hf.2).trans hk
  have hc:=recover_clock key (zeros a).bits
  have hzeros : (zeros a).bits.length=a := by rw [zeros_bits,List.length_replicate]
  conv_rhs at hc => rw [hzeros]
  have hcl:=SemiprimeD1ChildGraph.readCoordinate_clock classes.left i.val K
    (fun x hx=>(hf.1 x hx).trans hk)
  have hcr:=SemiprimeD1ChildGraph.readCoordinate_clock classes.right i.val K
    (fun x hx=>(hf.2 x hx).trans hk)
  have ht : tile.val ≤ 2^a := le_trans (Nat.le_of_lt tile.isLt)
    (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega))
  have htile:=SemiprimeSourceHistogramPortKeys.encodeKey_clock tile.val (2^a) ht
  have hb:=readBit_work tileBits.bits i.val
  have ho:=SemiprimeBitIndexClipping.leSignedBits_cost
    (left:=⟨false,low.bits⟩) (right:=⟨false,high.bits⟩) hl hr
  have hs : (copy (if bit.value then low.bits else high.bits)).clock ≤ 3*K+1 := by
    rw [copy_clock];split_ifs <;> omega
  have hd : (copy (if bit.value then high.bits else low.bits)).clock ≤ 3*K+1 := by
    rw [copy_clock];split_ifs <;> omega
  have hi : i.val ≤ a:=Nat.le_of_lt i.isLt
  have hc' : classes.clock ≤ 200*(a+1)*(K+a+1):=hc.trans (by gcongr)
  change classes.clock ≤ _ at hc'
  change low.clock ≤ _ at hcl
  change high.clock ≤ _ at hcr
  change tileBits.clock ≤ _ at htile
  change bit.work ≤ _ at hb
  change (zeros a).clock+classes.clock+low.clock+high.clock+tileBits.clock+bit.work+
    (SemiprimeBitIndexClipping.leSignedBits ⟨false,low.bits⟩ ⟨false,high.bits⟩).clock+
    (copy (if bit.value then low.bits else high.bits)).clock+
    (copy (if bit.value then high.bits else low.bits)).clock+20 ≤ _
  rw [zeros_clock]
  unfold budget
  omega

/-- Fixed resource monotonicity of the actual report envelope. -/
theorem budget_mono {a K T a' K' T' : ℕ} (ha : a ≤ a') (hk : K ≤ K') (ht : T ≤ T') :
    budget a K T ≤ budget a' K' T' := by
  unfold budget SemiprimeSourceHistogramPortKeys.encodeBudget
  gcongr

end RiemannGaussian.SemiprimeD1ModeRoutingBudget
