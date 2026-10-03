/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBitDivision

/-!
# Bit-only powers and geometric row construction

The scalar backend is composed without evaluating intermediate residues as
naturals. Exponents are literal bit words; row counts are literal unit-list
templates. Every recursive visit and retained row cell is charged. The raw
residue arrays agree with the earlier public-window specification. Encoding
the public inputs, constructing the templates, assigning labels, sorting,
the other pipeline stages and universal one-sixth recovery remain open costs.
-/

namespace RiemannGaussian.SemiprimeBitPowerWalk

open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeWindowConstruction

/-- A positive represented value has a nonempty physical word. -/
theorem positive_word_length {bits : List Bool} (h : 0<bitValue bits) :
    0<bits.length := by
  cases bits with
  | nil => simp only [bitValue,Nat.lt_irrefl] at h
  | cons bit tail => simp only [List.length_cons]; omega

/-- Actual modular power word and its composed primitive and scalar clocks. -/
structure PowerBitsReport where
  /-- The computed residue word, never evaluated in the data path. -/
  bits : List Bool
  /-- All scalar clocks and exponent-bit visits. -/
  clock : ℕ
  /-- Actual square and odd-bit multiplication calls. -/
  multiplications : ℕ
  /-- Actual general division calls, including normalization. -/
  reductions : ℕ
  /-- Every physical exponent bit, including high zero padding. -/
  rounds : ℕ

/-- Recurse on the literal exponent tail, square, and conditionally multiply
by the normalized base. An empty exponent constructs and reduces literal one.
Each positive frame pays its bit read, list test and Boolean branch. -/
def powerBits (modulus a : List Bool) : List Bool → PowerBitsReport
  | [] =>
    let one := divideBits [true] modulus
    ⟨one.remainder,one.clock+2,0,1,0⟩
  | bit::exponent =>
    let child := powerBits modulus a exponent
    let square := modMulBits child.bits child.bits modulus
    if bit=true then
      let normal := divideBits a modulus
      let product := modMulBits square.division.remainder normal.remainder modulus
      ⟨product.division.remainder,child.clock+square.clock+normal.clock+product.clock+3,
        child.multiplications+2,child.reductions+3,child.rounds+1⟩
    else
      ⟨square.division.remainder,child.clock+square.clock+3,
        child.multiplications+1,child.reductions+1,child.rounds+1⟩

/-- The computed bit word is the exact modular power for every modulus,
including zero, and every physical exponent encoding. -/
theorem powerBits_correct (modulus a exponent : List Bool) :
    bitValue (powerBits modulus a exponent).bits=
      (bitValue a^bitValue exponent)%bitValue modulus := by
  induction exponent with
  | nil =>
    simpa only [powerBits,bitValue,bitNat,if_true,Nat.mul_zero,Nat.add_zero,pow_zero]
      using (divideBits_correct [true] modulus).2
  | cons bit exponent ih =>
    have hs : bitValue (modMulBits (powerBits modulus a exponent).bits
        (powerBits modulus a exponent).bits modulus).division.remainder=
        (bitValue a^bitValue exponent*bitValue a^bitValue exponent)%bitValue modulus := by
      rw [modMulBits_correct,ih,←Nat.mul_mod]
    cases bit with
    | false =>
      simp only [powerBits,Bool.false_eq_true,if_false]
      rw [hs]
      simp only [bitValue,bitNat,Bool.false_eq_true,if_false,Nat.zero_add]
      rw [Nat.mul_comm 2 _,pow_mul,pow_two]
    | true =>
      simp only [powerBits,if_true]
      rw [modMulBits_correct,hs,(divideBits_correct a modulus).2,←Nat.mul_mod]
      simp only [bitValue,bitNat,if_true]
      have he : 1+2*bitValue exponent=bitValue exponent+bitValue exponent+1 := by omega
      rw [he,pow_succ,pow_add]

/-- Every power residue at a positive modulus has the fixed physical
modulus width, even when the exponent has high zero padding. -/
theorem powerBits_width {modulus : List Bool} (hN : 0<bitValue modulus)
    (a exponent : List Bool) :
    (powerBits modulus a exponent).bits.length=modulus.length := by
  cases exponent with
  | nil => exact (divideBits_widths (xs:=[true]) hN).1
  | cons bit exponent =>
    rw [powerBits]
    dsimp only
    split <;> dsimp only <;> exact modMulBits_width hN

/-- All physical exponent bits are visited. The scalar counters include
every square, odd-bit normalization and odd-bit product. -/
theorem powerBits_counts (modulus a exponent : List Bool) :
    (powerBits modulus a exponent).rounds=exponent.length ∧
    exponent.length≤(powerBits modulus a exponent).multiplications ∧
    (powerBits modulus a exponent).multiplications≤2*exponent.length ∧
    (powerBits modulus a exponent).reductions≤3*exponent.length+1 ∧
    (powerBits modulus a exponent).reductions+exponent.length=
      2*(powerBits modulus a exponent).multiplications+1 := by
  induction exponent with
  | nil => simp only [powerBits,List.length_nil,Nat.mul_zero,
      Nat.zero_add,Nat.add_zero,le_refl,and_self]
  | cons bit exponent ih =>
    rw [powerBits]
    dsimp only
    split <;> dsimp only [List.length_cons] <;> omega

/-- The actual composed power clock is linear in physical exponent length
and quadratic in the bounded base/modulus word widths. -/
theorem powerBits_cost {L : ℕ} {modulus a : List Bool}
    (hN : 0<bitValue modulus) (hm : modulus.length≤L) (ha : a.length≤L)
    (exponent : List Bool) :
    (powerBits modulus a exponent).clock≤
      exponent.length*(264*(L+1)^2+7)+72*(L+1)^2+2 := by
  have hL : 1≤L := by have h := positive_word_length hN; omega
  induction exponent with
  | nil =>
    have hc := bounded_divideBits (by simp only [List.length_cons,List.length_nil]; omega)
      hm (xs:=[true])
    dsimp only [powerBits,List.length_nil]
    omega
  | cons bit exponent ih =>
    have hw := powerBits_width hN a exponent
    have hs := bounded_modMulBits (by omega) (by omega) hm
      (xs:=(powerBits modulus a exponent).bits)
      (ys:=(powerBits modulus a exponent).bits)
    have hn := bounded_divideBits (by omega : a.length≤3*L) hm
    have hsw := modMulBits_width (xs:=(powerBits modulus a exponent).bits)
      (ys:=(powerBits modulus a exponent).bits) hN
    have hnw := (divideBits_widths (xs:=a) hN).1
    have hp := bounded_modMulBits (by omega) (by omega) hm
      (xs:=(modMulBits (powerBits modulus a exponent).bits
        (powerBits modulus a exponent).bits modulus).division.remainder)
      (ys:=(divideBits a modulus).remainder)
    rw [powerBits]
    dsimp only
    split <;> dsimp only [List.length_cons] <;> nlinarith

/-- A convenient uniform per-exponent-word bound includes the base case
and every normalization; no native exponent halving is assumed. -/
theorem bounded_powerBits {L : ℕ} {modulus a : List Bool}
    (hN : 0<bitValue modulus) (hm : modulus.length≤L) (ha : a.length≤L)
    (exponent : List Bool) :
    (powerBits modulus a exponent).clock≤272*(exponent.length+1)*(L+1)^2 := by
  have hc := powerBits_cost hN hm ha exponent
  have hstep : 264*(L+1)^2+7≤272*(L+1)^2 := by nlinarith
  have hb : 72*(L+1)^2+2≤272*(L+1)^2 := by nlinarith
  have he := Nat.mul_le_mul_left exponent.length hstep
  nlinarith

/-- Actual row words, complete primitive clock and scalar operation counts. -/
structure WalkBitsReport where
  /-- Only residues are constructed here; public labels remain an interface. -/
  residues : List (List Bool)
  /-- Every division/product clock and template visit/retained row cell. -/
  clock : ℕ
  /-- Actual advances, omitting the unused final multiplication. -/
  multiplications : ℕ
  /-- Every current normalization and advance reduction. -/
  reductions : ℕ

/-- Construct rows by following a literal unit-list template. Residues stay
as bit words throughout the loop. Two list tests and a retained row cell are
paid at each row; the empty template pays its terminal list test. -/
def walkBits (modulus start step : List Bool) : List Unit → WalkBitsReport
  | [] => ⟨[],1,0,0⟩
  | [_] =>
    let current := divideBits start modulus
    ⟨[current.remainder],current.clock+3,0,1⟩
  | _::next::template =>
    let current := divideBits start modulus
    let advance := modMulBits current.remainder step modulus
    let tail := walkBits modulus advance.division.remainder step (next::template)
    ⟨current.remainder::tail.residues,current.clock+advance.clock+tail.clock+3,
      tail.multiplications+1,tail.reductions+2⟩

/-- The bit-only walk reproduces every residue in the earlier counted
geometric walk. Labels in this equality are mathematical specifications. -/
theorem walkBits_values (modulus start step : List Bool) (template : List Unit)
    (index : ℕ) :
    (walkBits modulus start step template).residues.map bitValue=
      ((countedWalk (bitValue modulus) (bitValue start) (bitValue step)
        template.length index).records.map Prod.fst) := by
  induction template generalizing start index with
  | nil => simp only [walkBits,List.length_nil,countedWalk,List.map_nil]
  | cons _cell template ih =>
    cases template with
    | nil =>
      simp only [walkBits,List.length_cons,List.length_nil,countedWalk,List.map_cons,
        List.map_nil,(divideBits_correct start modulus).2]
    | cons next template =>
      rw [walkBits]
      simp only [List.map_cons,List.length_cons,countedWalk]
      rw [ih (index:=index+1),modMulBits_correct,(divideBits_correct start modulus).2]
      rfl

/-- The walk retains exactly one row per template cell, performs len-1
advances and charges len+(len-1) general reductions. -/
theorem walkBits_counts (modulus start step : List Bool) (template : List Unit) :
    (walkBits modulus start step template).residues.length=template.length ∧
    (walkBits modulus start step template).multiplications=template.length-1 ∧
    (walkBits modulus start step template).reductions=template.length+(template.length-1) := by
  induction template generalizing start with
  | nil => simp only [walkBits,List.length_nil,Nat.zero_sub,Nat.zero_add,and_self]
  | cons _cell template ih =>
    cases template with
    | nil => simp [walkBits]
    | cons next template =>
      have hc := ih (modMulBits (divideBits start modulus).remainder step modulus).division.remainder
      rw [walkBits]
      dsimp only [List.length_cons] at hc ⊢
      omega

/-- Every retained residue in the positive-modulus walk has the fixed
physical modulus width. No row is canonically trimmed for free. -/
theorem walkBits_widths {modulus : List Bool} (hN : 0<bitValue modulus)
    (start step : List Bool) (template : List Unit) :
    ∀ row∈(walkBits modulus start step template).residues,row.length=modulus.length := by
  induction template generalizing start with
  | nil => simp only [walkBits,List.not_mem_nil,false_implies,implies_true]
  | cons _cell template ih =>
    have hw := (divideBits_widths (xs:=start) hN).1
    cases template with
    | nil => simpa only [walkBits,List.mem_singleton] using fun row h => h ▸ hw
    | cons next template =>
      have ht := ih (modMulBits (divideBits start modulus).remainder step modulus).division.remainder
      intro row hr
      rcases List.mem_cons.mp hr with rfl|hrow
      · exact hw
      · exact ht row hrow

/-- The complete walk clock is linear in the literal number of rows and
quadratic in bounded physical residue/modulus widths. -/
theorem walkBits_cost {L : ℕ} {modulus start step : List Bool}
    (hN : 0<bitValue modulus) (hm : modulus.length≤L)
    (hs : start.length≤L) (ht : step.length≤L) (template : List Unit) :
    (walkBits modulus start step template).clock≤template.length*(168*(L+1)^2+5)+1 := by
  induction template generalizing start with
  | nil => simp only [walkBits,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons _cell template ih =>
    have hc := bounded_divideBits (by omega : start.length≤3*L) hm
    have hw := (divideBits_widths (xs:=start) hN).1
    have ha := bounded_modMulBits (by omega) ht hm
      (xs:=(divideBits start modulus).remainder)
    have haw := modMulBits_width (xs:=(divideBits start modulus).remainder) (ys:=step) hN
    cases template with
    | nil => dsimp only [walkBits,List.length_cons,List.length_nil]; nlinarith
    | cons next template =>
      have hi := ih (start:=(modMulBits (divideBits start modulus).remainder step modulus).division.remainder)
        (by omega)
      rw [walkBits]
      dsimp only [List.length_cons] at hi ⊢
      nlinarith

/-- The actual two setup powers and two residue axes, retaining their costs. -/
structure BitRows where
  /-- Computed active-base centre power. -/
  target : PowerBitsReport
  /-- Computed inverse-base block power. -/
  step : PowerBitsReport
  /-- Computed baby residue axis. -/
  babies : WalkBitsReport
  /-- Computed target-shifted inverse-step residue axis. -/
  giants : WalkBitsReport
  /-- Composed clocks, literal baby-start cell and retained source report. -/
  clock : ℕ

/-- Construct both residue axes without an intermediate natural-value
interface. The exponent words and row template are literal supplied inputs;
their public-input construction and labels still need their own cost proof. -/
def constructBitRows (modulus active inverse centre block : List Bool)
    (template : List Unit) : BitRows :=
  let target := powerBits modulus active centre
  let step := powerBits modulus inverse block
  let babies := walkBits modulus [true] active template
  let giants := walkBits modulus target.bits step.bits template
  ⟨target,step,babies,giants,target.clock+step.clock+babies.clock+giants.clock+2⟩

/-- Both constructed axes have the literal template length, for all moduli. -/
theorem constructBitRows_lengths (modulus active inverse centre block : List Bool)
    (template : List Unit) :
    (constructBitRows modulus active inverse centre block template).babies.residues.length=
      template.length ∧
    (constructBitRows modulus active inverse centre block template).giants.residues.length=
      template.length :=
  ⟨(walkBits_counts modulus [true] active template).1,
    (walkBits_counts modulus (powerBits modulus active centre).bits
      (powerBits modulus inverse block).bits template).1⟩

/-- The composed raw-row clock pays both powers and walks. Supplied physical
exponent lengths and template length remain explicit in the bound. -/
theorem constructBitRows_cost {L : ℕ} {modulus active inverse : List Bool}
    (hN : 0<bitValue modulus) (hm : modulus.length≤L)
    (ha : active.length≤L) (hi : inverse.length≤L)
    (centre block : List Bool) (template : List Unit) :
    (constructBitRows modulus active inverse centre block template).clock≤
      272*(centre.length+block.length+2)*(L+1)^2+
        2*template.length*(168*(L+1)^2+5)+4 := by
  have hL : 1≤L := by have h := positive_word_length hN; omega
  have hp := bounded_powerBits hN hm ha centre
  have hq := bounded_powerBits hN hm hi block
  have hb := walkBits_cost hN hm (by simp only [List.length_cons,List.length_nil]; omega)
    ha template (start:=[true])
  have ht := powerBits_width hN active centre
  have hs := powerBits_width hN inverse block
  have hg := walkBits_cost hN hm (by omega) (by omega) template
    (start:=(powerBits modulus active centre).bits)
    (step:=(powerBits modulus inverse block).bits)
  dsimp only [constructBitRows]
  nlinarith

/-- When the literal exponent already has its minimal physical width, the
bit-only loop preserves all scalar counts of the earlier binary power.
This hypothesis supplies no free trimming operation for padded words. -/
theorem powerBits_countedPower_counts (modulus a exponent : List Bool)
    (hcanonical : exponent.length=Nat.clog 2 (bitValue exponent+1)) :
    (powerBits modulus a exponent).multiplications=
      (countedPower (bitValue modulus) (bitValue a) (bitValue exponent)).multiplications ∧
    (powerBits modulus a exponent).reductions=
      (countedPower (bitValue modulus) (bitValue a) (bitValue exponent)).reductions ∧
    (powerBits modulus a exponent).rounds=
      (countedPower (bitValue modulus) (bitValue a) (bitValue exponent)).halvings := by
  revert hcanonical
  induction exponent with
  | nil =>
    intro _hc
    have hz : countedPower (bitValue modulus) (bitValue a) 0=
        ⟨1%bitValue modulus,0,0,1⟩ := by rw [countedPower,dif_pos rfl]
    simp only [powerBits,bitValue,hz,and_self]
  | cons bit exponent ih =>
    intro hc
    have he : 0<bitValue (bit::exponent) := by
      by_contra hn
      have hz : bitValue (bit::exponent)=0 := by omega
      simp only [hz,Nat.zero_add,List.length_cons] at hc
      norm_num at hc
    have hd : bitValue (bit::exponent)/2=bitValue exponent := by
      cases bit <;> simp only [bitValue,bitNat,Bool.false_eq_true,if_false,if_true] <;> omega
    have hh := clog_halving he
    rw [hd] at hh
    have ht : exponent.length=Nat.clog 2 (bitValue exponent+1) := by
      simp only [List.length_cons] at hc
      omega
    have hi := ih ht
    rw [powerBits,countedPower,dif_neg (Nat.ne_of_gt he),hd]
    dsimp only
    cases bit with
    | false =>
      have hp : bitValue (false::exponent)%2=0 := by
        simp only [bitValue,bitNat,Bool.false_eq_true,if_false]
        omega
      rw [if_pos hp]
      simp only [Bool.false_eq_true,if_false]
      omega
    | true =>
      have hp : ¬bitValue (true::exponent)%2=0 := by
        simp only [bitValue,bitNat,if_true]
        omega
      rw [if_neg hp]
      simp only [if_true]
      omega

/-- The earlier natural binary power's positive-modulus result is the
same canonical residue used by the new bit output specification. -/
theorem countedPower_mod_value {N : ℕ} (hN : 0<N) (a exponent : ℕ) :
    (countedPower N a exponent).value=(a^exponent)%N := by
  have hc : ((countedPower N a exponent).value : ZMod N)=((a^exponent)%N : ZMod N) := by
    simpa only [Nat.cast_pow,ZMod.natCast_mod] using countedPower_correct N a exponent
  have hv := congrArg (fun z : ZMod N => z.val) hc
  simp only [ZMod.val_natCast,Nat.mod_mod] at hv
  rwa [Nat.mod_eq_of_lt (countedPower_value_lt hN a exponent)] at hv

/-- Supplying the actual public quarter-centre/block encodings and row
template gives exactly both earlier raw residue axes. The theorem keeps
these interfaces explicit and does not assume they were constructed free. -/
theorem constructBitRows_raw_values {modulus active inverse centre block : List Bool}
    (hN : 0<bitValue modulus) (B : ℕ) (template : List Unit)
    (hc : bitValue centre=SemiprimeTotientWindow.quarterCentre (bitValue modulus))
    (hb : bitValue block=2*B) (ht : template.length=2*B) :
    (constructBitRows modulus active inverse centre block template).babies.residues.map bitValue=
      (buildRawSource (bitValue modulus) (bitValue active) (bitValue inverse) B).babies.records.map Prod.fst ∧
    (constructBitRows modulus active inverse centre block template).giants.residues.map bitValue=
      (buildRawSource (bitValue modulus) (bitValue active) (bitValue inverse) B).giants.records.map Prod.fst := by
  have hp : bitValue (powerBits modulus active centre).bits=
      (countedPower (bitValue modulus) (bitValue active)
        (SemiprimeTotientWindow.quarterCentre (bitValue modulus))).value := by
    rw [powerBits_correct,hc,countedPower_mod_value hN]
  have hq : bitValue (powerBits modulus inverse block).bits=
      (countedPower (bitValue modulus) (bitValue inverse) (2*B)).value := by
    rw [powerBits_correct,hb,countedPower_mod_value hN]
  constructor
  · simpa only [constructBitRows,buildRawSource,ht,bitValue,bitNat,if_true,
      Nat.mul_zero,Nat.add_zero] using walkBits_values modulus [true] active template 0
  · simpa only [constructBitRows,buildRawSource,ht,hp,hq] using
      walkBits_values modulus (powerBits modulus active centre).bits
        (powerBits modulus inverse block).bits template 0

end RiemannGaussian.SemiprimeBitPowerWalk
