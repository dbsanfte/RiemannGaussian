/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMacroEntryExecution
import RiemannGaussian.SemiprimeBitFermatArithmetic

/-! # Actual Boolean arithmetic interpreter for macro entry expressions -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeMacroEntryBitPrimitives
open scoped BigOperators
open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitFermatArithmetic

/-- Finite residue expressions; literals are actual little-endian bit words. -/
inductive Expr where
  /-- Input or constant bit word, copied to the physical modulus width. -/
  | literal : List Bool → Expr
  /-- Canonical modular addition. -/
  | add : Expr → Expr → Expr
  /-- Canonical modular subtraction. -/
  | sub : Expr → Expr → Expr
  /-- Boolean multiplication followed by restoring remainder. -/
  | mul : Expr → Expr → Expr
  deriving Inhabited

/-- Actual syntax nodes, counting every repeated child traversal. -/
def nodes : Expr → ℕ
  | .literal _ => 1
  | .add a b | .sub a b | .mul a b => nodes a+nodes b+1

/-- The only input validity requirement is canonical literal values. -/
def Valid (modulus : List Bool) : Expr → Prop
  | .literal bits => bitValue bits<bitValue modulus
  | .add a b | .sub a b | .mul a b => Valid modulus a ∧ Valid modulus b

/-- Executed bit output and the sum of the actually visited primitive clocks. -/
structure Run where
  /-- Computed output cells, never a decoded arithmetic oracle. -/
  bits : List Bool
  /-- Primitive backend clocks plus explicit report/reference overhead. -/
  clock : ℕ

/-- Interpret using only the existing carry/borrow/product/remainder backends. -/
def execute (modulus : List Bool) : Expr → Run
  | .literal bits =>
      let copied := fitBits bits modulus
      ⟨copied.bits,bitCost copied+1⟩
  | .add a b =>
      let left := execute modulus a
      let right := execute modulus b
      let result := residueAddBits modulus left.bits right.bits
      ⟨result.output.bits,left.clock+right.clock+result.clock+4⟩
  | .sub a b =>
      let left := execute modulus a
      let right := execute modulus b
      let result := residueSubBits modulus left.bits right.bits
      ⟨result.output.bits,left.clock+right.clock+result.clock+4⟩
  | .mul a b =>
      let left := execute modulus a
      let right := execute modulus b
      let result := modMulBits left.bits right.bits modulus
      ⟨result.division.remainder,left.clock+right.clock+result.clock+4⟩

/-- Natural/ring interpretation is a proof specification, not the data path. -/
def meaning (modulus : List Bool) : Expr → ZMod (bitValue modulus)
  | .literal bits => (bitValue bits : ZMod (bitValue modulus))
  | .add a b => meaning modulus a+meaning modulus b
  | .sub a b => meaning modulus a-meaning modulus b
  | .mul a b => meaning modulus a*meaning modulus b

/-- Every executed node has the fixed physical width and canonical residue. -/
theorem execute_bounds (modulus : List Bool) (hm : 0<bitValue modulus)
    (expr : Expr) (hv : Valid modulus expr) :
    (execute modulus expr).bits.length=modulus.length ∧
      bitValue (execute modulus expr).bits<bitValue modulus := by
  induction expr with
  | literal bits =>
    dsimp only [execute]
    constructor
    · exact (fitBits_counts _ _).1
    · rw [fitBits_value (hv.trans (bitValue_lt_width modulus))]
      exact hv
  | add a b ia ib =>
    obtain ⟨ha,hb⟩ := hv
    obtain ⟨_,hva⟩ := ia ha
    obtain ⟨_,hvb⟩ := ib hb
    exact ⟨residueAddBits_width _ _ _,(residueAddBits_exact hva hvb).2⟩
  | sub a b ia ib =>
    obtain ⟨ha,hb⟩ := hv
    obtain ⟨_,hva⟩ := ia ha
    obtain ⟨_,hvb⟩ := ib hb
    exact ⟨residueSubBits_width _ _ _,(residueSubBits_exact hva hvb).1⟩
  | mul a b ia ib =>
    exact ⟨modMulBits_width hm,by
      change bitValue (modMulBits _ _ modulus).division.remainder<bitValue modulus
      rw [modMulBits_correct]
      exact Nat.mod_lt _ hm⟩

/-- The actual executed Boolean output has the specified ring meaning. -/
theorem execute_correct (modulus : List Bool) (hm : 0<bitValue modulus)
    (expr : Expr) (hv : Valid modulus expr) :
    (bitValue (execute modulus expr).bits : ZMod (bitValue modulus))=meaning modulus expr := by
  induction expr with
  | literal bits =>
    dsimp only [execute,meaning]
    rw [fitBits_value (hv.trans (bitValue_lt_width modulus))]
  | add a b ia ib =>
    have h := residueAddBits_cast (execute_bounds modulus hm a hv.1).2
      (execute_bounds modulus hm b hv.2).2
    simpa only [execute,meaning,ia hv.1,ib hv.2] using h
  | sub a b ia ib =>
    have h := residueSubBits_cast (execute_bounds modulus hm a hv.1).2
      (execute_bounds modulus hm b hv.2).2
    simpa only [execute,meaning,ia hv.1,ib hv.2] using h
  | mul a b ia ib =>
    change (bitValue (modMulBits _ _ modulus).division.remainder : ZMod (bitValue modulus))=_
    rw [modMulBits_correct,ZMod.natCast_mod,Nat.cast_mul,ia hv.1,ib hv.2]
    rfl

/-- One explicit polynomial primitive bound per visited syntax node. -/
def nodeBudget (width : ℕ) : ℕ := 128*(width+1)^2+128

/-- Composition pays every actual backend call; no unit-cost ring oracle. -/
theorem execute_clock (modulus : List Bool) (hm : 0<bitValue modulus)
    (expr : Expr) (hv : Valid modulus expr) :
    (execute modulus expr).clock≤nodes expr*nodeBudget modulus.length := by
  induction expr with
  | literal bits =>
    have h := fitBits_cost bits modulus
    dsimp only [execute,nodes,nodeBudget]
    nlinarith
  | add a b ia ib =>
    have ha := ia hv.1
    have hb := ib hv.2
    have hwa := (execute_bounds modulus hm a hv.1).1
    have hwb := (execute_bounds modulus hm b hv.2).1
    have hc := residueAddBits_cost (le_refl modulus.length) hwa.le hwb.le
    dsimp only [execute,nodes] at *
    unfold nodeBudget at *
    nlinarith
  | sub a b ia ib =>
    have ha := ia hv.1
    have hb := ib hv.2
    have hwa := (execute_bounds modulus hm a hv.1).1
    have hwb := (execute_bounds modulus hm b hv.2).1
    have hc := residueSubBits_cost (le_refl modulus.length) hwa.le hwb.le
    dsimp only [execute,nodes] at *
    unfold nodeBudget at *
    nlinarith
  | mul a b ia ib =>
    have ha := ia hv.1
    have hb := ib hv.2
    have hwa := (execute_bounds modulus hm a hv.1).1
    have hwb := (execute_bounds modulus hm b hv.2).1
    have hc := bounded_modMulBits hwa.le hwb.le (le_refl modulus.length)
    dsimp only [execute,nodes] at *
    unfold nodeBudget at *
    nlinarith


/-- Literal one used by the repeated-multiplication compiler. -/
def oneExpr : Expr := .literal [true]

/-- Compile a power to actual modular products, rather than a native pow call. -/
def powerExpr (base : Expr) : ℕ → Expr
  | 0 => oneExpr
  | e+1 => .mul (powerExpr base e) base

/-- Canonical literals suffice throughout every compiled power. -/
theorem powerExpr_valid (modulus : List Bool) (hm : 1<bitValue modulus)
    (base : Expr) (hv : Valid modulus base) (e : ℕ) :
    Valid modulus (powerExpr base e) := by
  induction e with
  | zero => simpa [powerExpr,oneExpr,Valid,bitValue,bitNat] using hm
  | succ e ih => exact ⟨ih,hv⟩

/-- The compiled Boolean power has the exact ring interpretation. -/
theorem powerExpr_meaning (modulus : List Bool) (base : Expr) (e : ℕ) :
    meaning modulus (powerExpr base e)=(meaning modulus base)^e := by
  induction e with
  | zero => simp [powerExpr,oneExpr,meaning,bitValue,bitNat]
  | succ e ih => simp only [powerExpr,meaning,ih,pow_succ]

/-- Exact expanded syntax size; repeated base traversals are not shared for free. -/
theorem powerExpr_nodes (base : Expr) (e : ℕ) :
    nodes (powerExpr base e)=1+e*(nodes base+1) := by
  induction e with
  | zero => simp [powerExpr,oneExpr,nodes]
  | succ e ih => simp only [powerExpr,nodes,ih]; ring

/-- Compile one actual macro DFT output into the Boolean arithmetic backend. -/
def dotExpr (base : Expr) (stride frequency : ℕ) (input : ℕ → List Bool) : ℕ → Expr
  | 0 => .literal []
  | count+1 => .add (dotExpr base stride frequency input count)
      (.mul (.literal (input count)) (powerExpr base (stride*(count*frequency))))

/-- Input canonicality is checked once before interpreting a DFT expression. -/
theorem dotExpr_valid (modulus : List Bool) (hm : 1<bitValue modulus)
    (base : Expr) (hv : Valid modulus base) (stride frequency count : ℕ)
    (input : ℕ → List Bool) (hi : ∀ j<count,bitValue (input j)<bitValue modulus) :
    Valid modulus (dotExpr base stride frequency input count) := by
  induction count with
  | zero => exact Nat.zero_lt_of_lt hm
  | succ count ih =>
    exact ⟨ih (fun j hj => hi j (by omega)),hi count (by omega),
      powerExpr_valid modulus hm base hv _⟩

/-- The exact polynomial DFT formula follows from the compiled expressions. -/
theorem dotExpr_meaning (modulus : List Bool) (base : Expr) (stride frequency count : ℕ)
    (input : ℕ → List Bool) :
    meaning modulus (dotExpr base stride frequency input count)=
      ∑ j ∈ Finset.range count,(bitValue (input j) : ZMod (bitValue modulus))*
        (meaning modulus base^stride)^(j*frequency) := by
  induction count with
  | zero => simp [dotExpr,meaning,bitValue]
  | succ count ih =>
    simp only [dotExpr,meaning,powerExpr_meaning,ih,Finset.sum_range_succ,pow_mul]

/-- Polynomial syntax bound for every physical macro output. -/
theorem dotExpr_nodes_le (base : Expr) {stride frequency count n : ℕ}
    (hs : stride≤n) (hf : frequency≤n) (hc : count≤n) (input : ℕ → List Bool) :
    nodes (dotExpr base stride frequency input count)≤
      1+count*(4+n^3*(nodes base+1)) := by
  induction count with
  | zero => simp [dotExpr,nodes]
  | succ count ih =>
    have hh := ih (by omega : count≤n)
    have hm := Nat.mul_le_mul hs (Nat.mul_le_mul (by omega : count≤n) hf)
    have hm' : stride*(count*frequency)≤n^3 := by nlinarith
    have hb := Nat.mul_le_mul_right (nodes base+1) hm'
    simp only [dotExpr,nodes,powerExpr_nodes]
    nlinarith

/-- Fully primitive Boolean DFT output: correctness, physical width, canonicality
and polynomial clock are simultaneous conclusions, not supplied evaluator promises. -/
theorem execute_dotExpr (modulus : List Bool) (hm : 1<bitValue modulus)
    (base : Expr) (hv : Valid modulus base) {stride frequency count n : ℕ}
    (hs : stride≤n) (hf : frequency≤n) (hc : count≤n) (input : ℕ → List Bool)
    (hi : ∀ j<count,bitValue (input j)<bitValue modulus) :
    let result := execute modulus (dotExpr base stride frequency input count)
    result.bits.length=modulus.length ∧ bitValue result.bits<bitValue modulus ∧
    (bitValue result.bits : ZMod (bitValue modulus))=
      ∑ j ∈ Finset.range count,(bitValue (input j) : ZMod (bitValue modulus))*
        (meaning modulus base^stride)^(j*frequency) ∧
    result.clock≤(1+n*(4+n^3*(nodes base+1)))*nodeBudget modulus.length := by
  have hvd := dotExpr_valid modulus hm base hv stride frequency count input hi
  have hp : 0<bitValue modulus := by omega
  have hbounds := execute_bounds modulus hp _ hvd
  refine ⟨hbounds.1,hbounds.2,?_,?_⟩
  · rw [execute_correct modulus hp _ hvd,dotExpr_meaning]
  · have hcost := execute_clock modulus hp _ hvd
    have hnodes := dotExpr_nodes_le base hs hf hc input
    have hn : nodes (dotExpr base stride frequency input count)≤
        1+n*(4+n^3*(nodes base+1)) := by
      exact hnodes.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hc) _)
    exact hcost.trans (Nat.mul_le_mul_right _ hn)


/-- Boolean comparison result and the clocks of its actually run subtractors. -/
structure CheckRun where
  /-- Computed Boolean result. -/
  accepted : Bool
  /-- Primitive bit operations and explicit result tests. -/
  clock : ℕ

/-- Exact integer equality via two physical borrow comparisons. -/
def equalBits (xs ys : List Bool) : CheckRun :=
  let forward := subBits xs ys false
  let reverse := subBits ys xs false
  ⟨!forward.borrow && !reverse.borrow,
    bitCost forward.result+bitCost reverse.result+3⟩

/-- Equality does not rely on a native decoded integer comparison. -/
theorem equalBits_correct (xs ys : List Bool) :
    (equalBits xs ys).accepted=true ↔ bitValue xs=bitValue ys := by
  have hf := subBits_borrow_iff xs ys false
  have hr := subBits_borrow_iff ys xs false
  simp only [bitNat,Bool.false_eq_true,ite_false,Nat.add_zero] at hf hr
  simp only [equalBits,Bool.and_eq_true,Bool.not_eq_true']
  constructor
  · intro h
    have hnf : ¬bitValue xs<bitValue ys := by rw [← hf]; simp [h.1]
    have hnr : ¬bitValue ys<bitValue xs := by rw [← hr]; simp [h.2]
    omega
  · intro h
    constructor
    · apply Bool.eq_false_iff.mpr
      intro hb
      have hh := hf.mp hb
      omega
    · apply Bool.eq_false_iff.mpr
      intro hb
      have hh := hr.mp hb
      omega

/-- Fully charged equality clock for bounded actual input words. -/
theorem equalBits_clock {xs ys : List Bool} {width : ℕ}
    (hx : xs.length≤width) (hy : ys.length≤width) :
    (equalBits xs ys).clock≤24*width+7 := by
  have hf := subBits_cost xs ys false
  have hr := subBits_cost ys xs false
  have hxy : max xs.length ys.length≤width := max_le hx hy
  have hyx : max ys.length xs.length≤width := max_le hy hx
  dsimp only [equalBits]
  omega

/-- The physical INTEGER carry relation, computed from shifts and ripple sums. -/
def carryEquationBits (offset coefficient previous target next : List Bool) : CheckRun :=
  let shifted := shiftTemplateBits offset next
  let left := addBits coefficient previous false
  let right := addBits target shifted.bits false
  let checked := equalBits left.bits right.bits
  ⟨checked.accepted,bitCost shifted+bitCost left+bitCost right+checked.clock+4⟩

/-- No modular congruence is substituted for the actual integer carry equation. -/
theorem carryEquationBits_correct (offset coefficient previous target next : List Bool) :
    (carryEquationBits offset coefficient previous target next).accepted=true ↔
      bitValue coefficient+bitValue previous=
        bitValue target+2^offset.length*bitValue next := by
  dsimp only [carryEquationBits]
  rw [equalBits_correct,addBits_correct,addBits_correct,(shiftTemplateBits_exact offset next).1]
  simp only [bitNat,Bool.false_eq_true,ite_false,Nat.add_zero]

/-- Integer carry checks have linear primitive cost in the physical word bound. -/
theorem carryEquationBits_clock {offset coefficient previous target next : List Bool} {width : ℕ}
    (ho : offset.length≤width) (hc : coefficient.length≤width) (hp : previous.length≤width)
    (ht : target.length≤width) (hn : next.length≤width) :
    (carryEquationBits offset coefficient previous target next).clock≤100*width+100 := by
  have hs := shiftTemplateBits_exact offset next
  have hl := addBits_cost coefficient previous false
  have hr := addBits_cost target (shiftTemplateBits offset next).bits false
  have hll := (addBits_counts coefficient previous false).2.2.2.2
  have hrl := (addBits_counts target (shiftTemplateBits offset next).bits false).2.2.2.2
  have hmx : max coefficient.length previous.length≤width := max_le hc hp
  have hmy : max target.length (shiftTemplateBits offset next).bits.length≤2*width := by
    rw [hs.2.1]
    exact max_le (by omega) (by omega)
  have he := equalBits_clock (width:=2*width+1)
    (xs:=(addBits coefficient previous false).bits)
    (ys:=(addBits target (shiftTemplateBits offset next).bits false).bits)
    (by omega) (by omega)
  dsimp only [carryEquationBits]
  nlinarith [hs.2.2]


/-- Literal ordered port cells, in the backend's little-endian list format. -/
def portBits {width : ℕ} (input : Fin width → Bool) : List Bool := List.ofFn input

/-- Port-list construction retains exactly the physical word width. -/
theorem portBits_length {width : ℕ} (input : Fin width → Bool) :
    (portBits input).length=width := List.length_ofFn

/-- The existing Boolean arithmetic sees exactly the proved public decoder. -/
theorem portBits_value {width : ℕ} (input : Fin width → Bool) :
    bitValue (portBits input)=SemiprimeMacroEntryExecution.binaryDecode input := by
  induction width with
  | zero => simp [portBits,SemiprimeMacroEntryExecution.binaryDecode,bitValue]
  | succ width ih =>
    rw [show portBits input=input 0::portBits (input ∘ Fin.succ) by
      simp only [portBits,List.ofFn_succ,Function.comp_def]]
    rw [bitValue,ih]
    change bitNat (input 0)+2*Nat.ofBits (input ∘ Fin.succ)=Nat.ofBits input
    rw [Nat.ofBits_succ]
    cases input 0 <;> simp [bitNat,Nat.add_comm]

/-- Physical less-than gate, using the final borrow of an executed subtractor. -/
def lessBits (xs ys : List Bool) : CheckRun :=
  let difference := subBits xs ys false
  ⟨difference.borrow,bitCost difference.result+1⟩

/-- Canonicality and source width tests use actual bits, not decoded order oracles. -/
theorem lessBits_correct (xs ys : List Bool) :
    (lessBits xs ys).accepted=true ↔ bitValue xs<bitValue ys := by
  simpa only [lessBits,bitNat,Bool.false_eq_true,ite_false,Nat.add_zero]
    using subBits_borrow_iff xs ys false

/-- Every physical less-than gate has a linear primitive clock. -/
theorem lessBits_clock {xs ys : List Bool} {width : ℕ}
    (hx : xs.length≤width) (hy : ys.length≤width) :
    (lessBits xs ys).clock≤12*width+3 := by
  have h := subBits_cost xs ys false
  have hmax : max xs.length ys.length≤width := max_le hx hy
  dsimp only [lessBits]
  omega


/-- Actual equality of two compiled modular expressions, including both runs. -/
def residueEqualityBits (modulus : List Bool) (left right : Expr) : CheckRun :=
  let lhs := execute modulus left
  let rhs := execute modulus right
  let compared := equalBits lhs.bits rhs.bits
  ⟨compared.accepted,lhs.clock+rhs.clock+compared.clock+3⟩

/-- Canonical outputs let physical integer equality check exactly ring equality. -/
theorem residueEqualityBits_correct (modulus : List Bool) (hm : 0<bitValue modulus)
    (left right : Expr) (hl : Valid modulus left) (hr : Valid modulus right) :
    (residueEqualityBits modulus left right).accepted=true ↔
      meaning modulus left=meaning modulus right := by
  dsimp only [residueEqualityBits]
  rw [equalBits_correct]
  have hleft := execute_correct modulus hm left hl
  have hright := execute_correct modulus hm right hr
  have hbl := (execute_bounds modulus hm left hl).2
  have hbr := (execute_bounds modulus hm right hr).2
  rw [← hleft,← hright]
  constructor
  · intro h
    rw [h]
  · intro h
    have hv := congrArg ZMod.val h
    simpa only [ZMod.val_natCast_of_lt hbl,ZMod.val_natCast_of_lt hbr] using hv

/-- Full bit cost of checking an output, including both expression evaluations. -/
theorem residueEqualityBits_clock (modulus : List Bool) (hm : 0<bitValue modulus)
    (left right : Expr) (hl : Valid modulus left) (hr : Valid modulus right) :
    (residueEqualityBits modulus left right).clock≤
      (nodes left+nodes right+1)*nodeBudget modulus.length := by
  have hcl := execute_clock modulus hm left hl
  have hcr := execute_clock modulus hm right hr
  have hwl := (execute_bounds modulus hm left hl).1
  have hwr := (execute_bounds modulus hm right hr).1
  have hcheck := equalBits_clock hwl.le hwr.le
  dsimp only [residueEqualityBits]
  unfold nodeBudget at *
  nlinarith

end RiemannGaussian.SemiprimeMacroEntryBitPrimitives
