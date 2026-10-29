/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMacroEntryBitPrimitives

/-! # Composed actual Boolean checks for the ordered macro vertices -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeMacroEntryBitCheck
open scoped BigOperators
open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitFermatArithmetic
open SemiprimeMacroFermatNetwork SemiprimeMacroBitNetwork
open SemiprimeMacroGraph SemiprimeMacroGraphSemantics SemiprimeMacroEntryExecution
open SemiprimeMacroEntryBitPrimitives

/-- Executed conjunction; both child runs have already been paid. -/
def andRun (left right : CheckRun) : CheckRun :=
  ⟨left.accepted && right.accepted,left.clock+right.clock+1⟩

/-- Stream an actual finite array of checks, retaining only the accumulated run. -/
def allRun : {size : ℕ} → (Fin size → CheckRun) → CheckRun
  | 0, _ => ⟨true,1⟩
  | _+1, checks => andRun (checks 0) (allRun (checks ∘ Fin.succ))

/-- The finite traversal has exactly the intended universal semantics. -/
theorem allRun_correct {size : ℕ} (checks : Fin size → CheckRun) :
    (allRun checks).accepted=true ↔ ∀ i,(checks i).accepted=true := by
  induction size with
  | zero => simp [allRun]
  | succ size ih =>
    simp only [allRun,andRun,Bool.and_eq_true,ih,Function.comp_apply]
    constructor
    · rintro ⟨h0,hs⟩ i
      exact Fin.cases h0 hs i
    · intro h
      exact ⟨h 0,fun i => h i.succ⟩

/-- Every traversed check and loop step contributes to the actual clock. -/
theorem allRun_clock {size budget : ℕ} (checks : Fin size → CheckRun)
    (h : ∀ i,(checks i).clock≤budget) :
    (allRun checks).clock≤ size*(budget+1)+1 := by
  induction size with
  | zero => simp [allRun]
  | succ size ih =>
    have ht := ih (checks ∘ Fin.succ) (fun i => h i.succ)
    have hh := h 0
    dsimp only [allRun,andRun]
    nlinarith

/-- A failed canonicality gate prevents evaluating its guarded arithmetic body. -/
def guardRun (gate : CheckRun) (body : Unit → CheckRun) : CheckRun :=
  if gate.accepted then
    let result := body ()
    ⟨result.accepted,gate.clock+result.clock+1⟩
  else ⟨false,gate.clock+1⟩

/-- Guard execution is exact, including the false-input branch. -/
theorem guardRun_correct (gate : CheckRun) (body : Unit → CheckRun) :
    (guardRun gate body).accepted=true ↔ gate.accepted=true ∧ (body ()).accepted=true := by
  cases h : gate.accepted <;> simp [guardRun,h]

/-- The physical Fermat modulus is constructed by the existing bit routine. -/
def modulus (p : Config) : List Bool :=
  (fermatModulusBits (List.replicate (p.r*p.t) false)).bits

/-- Actual public transform size and positivity, needed by the physical backend. -/
theorem config_size (p : Config) : p.r*p.t=macroLength p.depth ∧ 4≤p.r*p.t := by
  exact ⟨p.shape,by have h:=p.quarter; have hp:=p.bits_pos; omega⟩

/-- The constructed modulus has its literal value. -/
theorem modulus_value (p : Config) : bitValue (modulus p)=2^(macroLength p.depth)+1 := by
  unfold modulus
  rw [fermatModulusBits_value]
  simp only [List.length_replicate,p.shape]

/-- Every modulus word occupies exactly n+1 physical bits. -/
theorem modulus_length (p : Config) : (modulus p).length=p.r*p.t+1 := by
  have h := (fermatModulusBits_width_cost
    (template:=List.replicate (p.r*p.t) false) (by simpa only [List.length_replicate] using (show 0<p.r*p.t by have := (config_size p).2; omega))).1
  simpa only [modulus,List.length_replicate] using h

/-- Zero literal expression. -/
def zeroExpr : Expr := .literal []

/-- Literal two expression. -/
def twoExpr : Expr := .literal [false,true]

/-- Literal root-four expression. -/
def fourExpr : Expr := .literal [false,false,true]

/-- The actual forward or inverse root, with inverse compiled to products. -/
def rootExpr (p : Config) : Transform → Expr
  | .inl _ => fourExpr
  | .inr _ => powerExpr fourExpr (p.r*p.t-1)

/-- The actual inverse normalization compiled to powers and subtraction. -/
def normalizationExpr (p : Config) : Transform → Expr
  | .inl _ => oneExpr
  | .inr _ => .sub zeroExpr (powerExpr twoExpr (p.r*p.t-(p.depth+1)))

/-- Ring interpretation at an explicitly given natural modulus. -/
def genericMeaning (M : ℕ) : Expr → ZMod M
  | .literal bits => (bitValue bits : ZMod M)
  | .add a b => genericMeaning M a+genericMeaning M b
  | .sub a b => genericMeaning M a-genericMeaning M b
  | .mul a b => genericMeaning M a*genericMeaning M b

/-- Interpret syntax in the frozen actual macro ring. -/
def ringMeaning (p : Config) (expr : Expr) : MacroRing p.depth :=
  genericMeaning (2^(macroLength p.depth)+1) expr

/-- Physical expression semantics is the explicit generic interpretation. -/
theorem meaning_generic (modulus : List Bool) (expr : Expr) :
    meaning modulus expr=genericMeaning (bitValue modulus) expr := by
  induction expr <;> simp_all [meaning,genericMeaning]

/-- Equality of numerical moduli transports the computed ring expression. -/
theorem genericMeaning_heq {M N : ℕ} (h : M=N) (expr : Expr) :
    HEq (genericMeaning M expr) (genericMeaning N expr) := by
  cases h
  rfl

/-- The physical-modulus expression meaning is the actual macro-ring meaning. -/
theorem ringMeaning_eq (p : Config) (expr : Expr) :
    HEq (meaning (modulus p) expr) (ringMeaning p expr) := by
  rw [meaning_generic]
  exact genericMeaning_heq (modulus_value p) expr


/-- The physical modulus is larger than every fixed root literal. -/
theorem modulus_gt_four (p : Config) : 4<bitValue (modulus p) := by
  rw [modulus_value]
  have hn : 2 ≤ macroLength p.depth := by have := config_size p; omega
  have hp : 2^2≤2^(macroLength p.depth) := Nat.pow_le_pow_right (by omega) hn
  norm_num at hp
  omega

/-- All literals and compiled roots/normalizers are canonically licensed. -/
theorem rootExpr_valid (p : Config) (tr : Transform) : Valid (modulus p) (rootExpr p tr) := by
  have hm := modulus_gt_four p
  have hv : Valid (modulus p) fourExpr := by
    simpa [Valid,fourExpr,bitValue,bitNat] using hm
  cases tr with
  | inl side => exact hv
  | inr marker => exact powerExpr_valid _ (by omega) _ hv _

/-- Actual normalized expressions do not require unit or primality assumptions. -/
theorem normalizationExpr_valid (p : Config) (tr : Transform) :
    Valid (modulus p) (normalizationExpr p tr) := by
  have hm := modulus_gt_four p
  cases tr with
  | inl side => simpa [normalizationExpr,oneExpr,Valid,bitValue,bitNat] using (show 1<bitValue (modulus p) by omega)
  | inr marker =>
    constructor
    · exact Nat.zero_lt_of_lt hm
    · apply powerExpr_valid _ (by omega)
      simpa [twoExpr,Valid,bitValue,bitNat] using (show 2<bitValue (modulus p) by omega)

/-- The expression power has the same interpretation in any modulus. -/
theorem genericMeaning_power (M : ℕ) (base : Expr) (e : ℕ) :
    genericMeaning M (powerExpr base e)=genericMeaning M base^e := by
  induction e with
  | zero => simp [powerExpr,oneExpr,genericMeaning,bitValue,bitNat]
  | succ e ih => simp only [powerExpr,genericMeaning,ih,pow_succ]

/-- Literal root expressions equal the exact roots of the actual ordered table. -/
theorem rootExpr_meaning (p : Config) (tr : Transform) : ringMeaning p (rootExpr p tr)=root p tr := by
  cases tr <;> simp [rootExpr,root,ringMeaning,genericMeaning_power,fourExpr,
    genericMeaning,bitValue,bitNat,inverseRoot,p.shape]

/-- Literal normalizer expressions equal the counted table's actual normalization. -/
theorem normalizationExpr_meaning (p : Config) (tr : Transform) :
    ringMeaning p (normalizationExpr p tr)=normalization p tr := by
  cases tr <;> simp [normalizationExpr,normalization,ringMeaning,genericMeaning_power,
    zeroExpr,twoExpr,oneExpr,genericMeaning,bitValue,bitNat,normalizer_eq_explicit,
    explicitNormalizer,p.shape]

universe u

/-- Equality of two terms transports across heterogeneous equality of their types. -/
theorem eq_iff_heq {α β : Sort u} {a b : α} {c d : β} (ha : HEq a c) (hb : HEq b d) :
    a=b ↔ c=d := by
  cases ha
  cases hb
  rfl

/-- The executed residue comparison checks precisely the actual macro-ring equation. -/
theorem residueCheck_correct (p : Config) (left right : Expr)
    (hl : Valid (modulus p) left) (hr : Valid (modulus p) right) :
    (residueEqualityBits (modulus p) left right).accepted=true ↔
      ringMeaning p left=ringMeaning p right := by
  rw [residueEqualityBits_correct _ (Nat.zero_lt_of_lt (modulus_gt_four p)) _ _ hl hr]
  exact eq_iff_heq (ringMeaning_eq p left) (ringMeaning_eq p right)

/-- Canonicality of the actual ordered words is computed by borrow gates. -/
def canonicalRun {size : ℕ} (p : Config) (words : Fin size → List Bool) : CheckRun :=
  allRun (fun i => lessBits (words i) (modulus p))

/-- Every input and output word is checked, including malformed encodings. -/
theorem canonicalRun_correct {size : ℕ} (p : Config) (words : Fin size → List Bool) :
    (canonicalRun p words).accepted=true ↔ ∀ i,bitValue (words i)<bitValue (modulus p) := by
  simp only [canonicalRun,allRun_correct,lessBits_correct]


/-- Extend the actual finite input array only for the public loop's natural indices. -/
def wordAt {size : ℕ} (words : Fin size → List Bool) (j : ℕ) : List Bool :=
  if hj : j<size then words ⟨j,hj⟩ else []

/-- The expression compiler's DFT identity at any explicitly specified modulus. -/
theorem genericMeaning_dot (M : ℕ) (base : Expr) (stride frequency count : ℕ)
    (input : ℕ → List Bool) :
    genericMeaning M (dotExpr base stride frequency input count)=
      ∑ j ∈ Finset.range count,(bitValue (input j) : ZMod M)*
        (genericMeaning M base^stride)^(j*frequency) := by
  induction count with
  | zero => simp [dotExpr,genericMeaning,bitValue]
  | succ count ih =>
    simp only [dotExpr,genericMeaning,genericMeaning_power,ih,Finset.sum_range_succ,pow_mul]

/-- The compiled expression on actual finite input words has the literal DFT sum. -/
theorem ringMeaning_dot {size : ℕ} (p : Config) (tr : Transform) (stride frequency : ℕ)
    (words : Fin size → List Bool) :
    ringMeaning p (dotExpr (rootExpr p tr) stride frequency (wordAt words) size)=
      ∑ j : Fin size,(bitValue (words j) : MacroRing p.depth)*
        (root p tr^stride)^(j.val*frequency) := by
  change genericMeaning _ _=_
  rw [genericMeaning_dot]
  have hr := rootExpr_meaning p tr
  change genericMeaning _ (rootExpr p tr)=_ at hr
  rw [hr,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp only [wordAt,dite_eq_left j.isLt]

/-- One literal macro DFT block, with actual canonical gates before arithmetic. -/
def transformRun {size : ℕ} (p : Config) (tr : Transform) (stride : ℕ) (factor : Expr)
    (input output : Fin size → List Bool) : CheckRun :=
  guardRun (andRun (canonicalRun p input) (canonicalRun p output)) (fun _ =>
    allRun (fun k => residueEqualityBits (modulus p) (.literal (output k))
      (.mul factor (dotExpr (rootExpr p tr) stride k.val (wordAt input) size))))

/-- The full executed DFT-block checker is exactly its literal ring equations. -/
theorem transformRun_correct {size : ℕ} (p : Config) (tr : Transform) (stride : ℕ)
    (factor : Expr) (hf : Valid (modulus p) factor) (input output : Fin size → List Bool) :
    (transformRun p tr stride factor input output).accepted=true ↔
      (∀ j,bitValue (input j)<bitValue (modulus p)) ∧
      (∀ k,bitValue (output k)<bitValue (modulus p)) ∧
      ∀ k,(bitValue (output k) : MacroRing p.depth)=ringMeaning p factor*
        ∑ j : Fin size,(bitValue (input j) : MacroRing p.depth)*(root p tr^stride)^(j.val*k.val) := by
  simp only [transformRun,guardRun_correct,andRun,Bool.and_eq_true,canonicalRun_correct,
    allRun_correct]
  have he (hi : ∀ j,bitValue (input j)<bitValue (modulus p))
      (ho : ∀ k,bitValue (output k)<bitValue (modulus p)) (k : Fin size) :
      (residueEqualityBits (modulus p) (.literal (output k))
        (.mul factor (dotExpr (rootExpr p tr) stride k.val (wordAt input) size))).accepted=true ↔
      (bitValue (output k) : MacroRing p.depth)=ringMeaning p factor*
        ∑ j : Fin size,(bitValue (input j) : MacroRing p.depth)*(root p tr^stride)^(j.val*k.val) := by
    have hd := dotExpr_valid (modulus p) (by have := modulus_gt_four p; omega)
      (rootExpr p tr) (rootExpr_valid p tr) stride k.val size (wordAt input)
      (fun j hj => by simpa only [wordAt,dite_eq_left hj] using hi ⟨j,hj⟩)
    have hlit : Valid (modulus p) (.literal (output k)) := ho k
    have hprod : Valid (modulus p) (.mul factor
        (dotExpr (rootExpr p tr) stride k.val (wordAt input) size)) := ⟨hf,hd⟩
    rw [residueCheck_correct p _ _ hlit hprod]
    change (bitValue (output k) : MacroRing p.depth)=ringMeaning p factor*
      ringMeaning p (dotExpr (rootExpr p tr) stride k.val (wordAt input) size) ↔ _
    rw [ringMeaning_dot]
  constructor
  · rintro ⟨⟨hi,ho⟩,hk⟩
    exact ⟨hi,ho,fun k => (he hi ho k).mp (hk k)⟩
  · rintro ⟨hi,ho,hk⟩
    exact ⟨⟨hi,ho⟩,fun k => (he hi ho k).mpr (hk k)⟩

/-- A physically constructed strict power-of-two comparison bound. -/
def boundBits (width : ℕ) : List Bool :=
  (powerTemplateBits (List.replicate width false)).bits

/-- No native exponentiation constructs the comparison word in the bit data path. -/
theorem boundBits_value (width : ℕ) : bitValue (boundBits width)=2^width := by
  simpa only [boundBits,List.length_replicate] using
    (powerTemplateBits_exact (List.replicate width false)).1

/-- An actual low source flag, computed from borrow/equality gates on its word. -/
def flagRun (index : ℕ) (word : List Bool) (flag : Bool) : CheckRun :=
  let check := if index=0 then lessBits word [false,true] else equalBits word []
  ⟨decide (flag=(!check.accepted)),check.clock+2⟩

/-- The source flag implementation uses precisely the compiler's nontriviality rule. -/
theorem flagRun_correct (index : ℕ) (word : List Bool) (flag : Bool) :
    (flagRun index word flag).accepted=true ↔ flag=digitFlag index (bitValue word) := by
  have htwo := lessBits_correct word [false,true]
  have hzero := equalBits_correct word []
  norm_num [bitValue,bitNat] at htwo hzero
  by_cases hi : index=0
  · simp only [flagRun,decide_eq_true_eq,digitFlag,hi,ite_true]
    have he : (!(lessBits word [false,true]).accepted)=decide (2≤bitValue word) := by
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.not_eq_true',decide_eq_true_eq,Bool.eq_false_iff]
      exact (not_congr htwo).trans (by omega)
    rw [he]
  · simp only [flagRun,decide_eq_true_eq,digitFlag,hi,ite_false]
    have he : (!(equalBits word []).accepted)=decide (bitValue word≠0) := by
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.not_eq_true',decide_eq_true_eq,Bool.eq_false_iff]
      exact not_congr hzero
    rw [he]


/-- Read-only target words are the literal public descriptor, not evaluator outputs. -/
structure Targets (p : Config) where
  /-- The actual little-endian target digit cells. -/
  words : Fin (p.r*p.t) → List Bool
  /-- Digits retain their physical radix-width encoding. -/
  width : ∀ i,(words i).length≤p.bits
  /-- Descriptor values match the frozen public numerical target. -/
  value : ∀ i,bitValue (words i)=p.target i.val

/-- An explicit bit view of the already public target digits. -/
def configTargets (p : Config) : Targets p where
  words i := portBits (SemiprimeBooleanNetwork.encode p.bits (p.target i.val)).getLsb
  width i := (portBits_length _).le
  value i := by
    rw [portBits_value,← readWord_eq_binaryDecode,readWord_bits]
    exact SemiprimeBooleanNetwork.decode_encode (p.target_lt i.val i.isLt)

/-- One output equation with actual canonical gates before its compiled arithmetic. -/
def equationRun {size : ℕ} (p : Config) (input : Fin size → List Bool)
    (output : List Bool) (expr : Expr) : CheckRun :=
  guardRun (andRun (canonicalRun p input) (lessBits output (modulus p))) (fun _ =>
    residueEqualityBits (modulus p) (.literal output) expr)

/-- The guarded arithmetic body is used only under its proved literal conditions. -/
theorem equationRun_correct {size : ℕ} (p : Config) (input : Fin size → List Bool)
    (output : List Bool) (expr : Expr)
    (hv : (∀ j,bitValue (input j)<bitValue (modulus p)) → Valid (modulus p) expr) :
    (equationRun p input output expr).accepted=true ↔
      (∀ j,bitValue (input j)<bitValue (modulus p)) ∧
      bitValue output<bitValue (modulus p) ∧
      (bitValue output : MacroRing p.depth)=ringMeaning p expr := by
  simp only [equationRun,guardRun_correct,andRun,Bool.and_eq_true,
    canonicalRun_correct,lessBits_correct]
  constructor
  · rintro ⟨⟨hi,ho⟩,he⟩
    exact ⟨hi,ho,(residueCheck_correct p (.literal output) expr (show Valid (modulus p) (.literal output) from ho) (hv hi)).mp he⟩
  · rintro ⟨hi,ho,he⟩
    exact ⟨⟨hi,ho⟩,(residueCheck_correct p (.literal output) expr (show Valid (modulus p) (.literal output) from ho) (hv hi)).mpr he⟩

/-- Actual ordered word roles converted to the Boolean-list backend. -/
def localWord {width : ℕ} (input : Fin width → Bool) : List Bool := portBits input

/-- The source vertex, including its unique active flag role. -/
def sourceRun (p : Config) (i : Fin (p.r*p.t))
    (input : LocalSlot (.input (0 : Fin 2) i : Vertex p.r p.t p.digits) → Bool) : CheckRun :=
  let word := localWord (fun bit => input (.inl bit))
  if hi : i.val<p.digits then
    andRun (lessBits word (boundBits (p.width ⟨i.val,hi⟩)))
      (flagRun i.val word (input (.inr ⟨⟨i.val,hi⟩,rfl⟩)))
  else equalBits word []

/-- A carry is checked as an integer relation and with all strict physical guards. -/
def carryRun (p : Config) (target coefficient previous next : List Bool) : CheckRun :=
  andRun (lessBits coefficient (modulus p))
    (andRun (lessBits previous (boundBits (p.r*p.t)))
      (andRun (lessBits next (boundBits (p.r*p.t)))
        (carryEquationBits (List.replicate p.bits false) coefficient previous target next)))

/-- Every vertex has a literal composed bit checker, with no tensor-value oracle. -/
def localRun (p : Config) (targets : Targets p) :
    (v : Vertex p.r p.t p.digits) → (LocalSlot v → Bool) → CheckRun
  | .input _ i,x =>
      let word := localWord (fun bit => x (.inl bit))
      if hi : i.val<p.digits then
        andRun (lessBits word (boundBits (p.width ⟨i.val,hi⟩)))
          (flagRun i.val word (x (.inr ⟨⟨i.val,hi⟩,rfl⟩)))
      else equalBits word []
  | .first tr _,x =>
      transformRun p tr p.r oneExpr
        (fun j => localWord (fun bit => x (.inl (j,bit))))
        (fun k => localWord (fun bit => x (.inr (k,bit))))
  | .scale tr j k,x =>
      let input := localWord (fun bit => x (.inl bit))
      let output := localWord (fun bit => x (.inr bit))
      equationRun p (fun _ : Fin 1 => input) output
        (.mul (.literal input) (powerExpr (rootExpr p tr) (j.val*k.val)))
  | .second tr _,x =>
      transformRun p tr p.t (normalizationExpr p tr)
        (fun j => localWord (fun bit => x (.inl (j,bit))))
        (fun k => localWord (fun bit => x (.inr (k,bit))))
  | .product _,x =>
      let input := fun side : Fin 2 => localWord (fun bit => x (.inl (side,bit)))
      let output := localWord (fun bit => x (.inr bit))
      equationRun p input output (.mul (.literal (input 0)) (.literal (input 1)))
  | .carryInitial,x => equalBits (localWord x) []
  | .carry k,x =>
      carryRun p (targets.words k)
        (localWord (fun bit => x (.inl (0,bit))))
        (localWord (fun bit => x (.inl (1,bit))))
        (localWord (fun bit => x (.inr bit)))
  | .carryTerminal,x => equalBits (localWord x) []
  | .orGate _ _,x => ⟨decide (x 2=(x 0 || x 1)),5⟩
  | .inputCheck _,x => ⟨x 0,1⟩

/-- The actual integer carry checker exactly matches the public carry predicate. -/
theorem carryRun_correct (p : Config) (target coefficient previous next : List Bool) :
    (carryRun p target coefficient previous next).accepted=true ↔
      bitValue coefficient<2^(p.r*p.t)+1 ∧ bitValue previous<2^(p.r*p.t) ∧
      bitValue next<2^(p.r*p.t) ∧
      bitValue coefficient+bitValue previous=bitValue target+2^p.bits*bitValue next := by
  simp only [carryRun,andRun,Bool.and_eq_true,lessBits_correct,boundBits_value,
    carryEquationBits_correct,List.length_replicate,modulus_value,← p.shape]

/-- Every literal local word has exactly the frozen numerical interpretation. -/
theorem localWord_value {width : ℕ} (input : Fin width → Bool) :
    bitValue (localWord input)=readWord width input := by
  rw [localWord,portBits_value,readWord_eq_binaryDecode]


/-- Literal expression interpretation in the actual ring. -/
theorem ringMeaning_literal (p : Config) (bits : List Bool) :
    ringMeaning p (.literal bits)=(bitValue bits : MacroRing p.depth) := rfl

/-- Product expression interpretation in the actual ring. -/
theorem ringMeaning_mul (p : Config) (a b : Expr) :
    ringMeaning p (.mul a b)=ringMeaning p a*ringMeaning p b := rfl

/-- The compiled unit expression has literal unit value. -/
theorem ringMeaning_one (p : Config) : ringMeaning p oneExpr=1 := by
  simp [ringMeaning,oneExpr,genericMeaning,bitValue,bitNat]

/-- Powers preserve the actual macro-ring expression interpretation. -/
theorem ringMeaning_power (p : Config) (base : Expr) (e : ℕ) :
    ringMeaning p (powerExpr base e)=ringMeaning p base^e := genericMeaning_power _ _ _

/-- Every actual vertex checker agrees with the frozen ordered local table. -/
theorem localRun_correct (p : Config) (targets : Targets p)
    (v : Vertex p.r p.t p.digits) (input : LocalSlot v → Bool) :
    (localRun p targets v input).accepted=true ↔ localTable p v input := by
  cases v with
  | input side i =>
    simp only [localRun,localTable]
    split
    · rename_i hi
      simp only [andRun,Bool.and_eq_true,lessBits_correct,boundBits_value,flagRun_correct,
        localWord_value]
      constructor
      · rintro ⟨hw,hf⟩
        refine ⟨hw,?_⟩
        intro j
        have hj : j=⟨⟨i.val,hi⟩,rfl⟩ := by
          apply Subtype.ext
          apply Fin.ext
          exact j.property
        simpa only [hj] using hf
      · rintro ⟨hw,hf⟩
        exact ⟨hw,hf ⟨⟨i.val,hi⟩,rfl⟩⟩
    · simp only [equalBits_correct,localWord_value,bitValue]
  | first tr i =>
    have hv : Valid (modulus p) oneExpr := by
      have h := normalizationExpr_valid p (.inl 0)
      exact h
    have h := transformRun_correct p tr p.r oneExpr hv
      (fun j => localWord (fun bit => input (.inl (j,bit))))
      (fun k => localWord (fun bit => input (.inr (k,bit))))
    simpa only [localRun,localTable,modulus_value,← p.shape,localWord_value,
      ringMeaning_one,one_mul] using h
  | scale tr j k =>
    let word := localWord (fun bit => input (.inl bit))
    let output := localWord (fun bit => input (.inr bit))
    have hv : (∀ _i : Fin 1,bitValue word<bitValue (modulus p)) →
        Valid (modulus p) (.mul (.literal word) (powerExpr (rootExpr p tr) (j.val*k.val))) := by
      intro h
      exact ⟨h 0,powerExpr_valid _ (by have := modulus_gt_four p; omega) _ (rootExpr_valid p tr) _⟩
    have h := equationRun_correct p (fun _ : Fin 1 => word) output _ hv
    simpa only [localRun,localTable,word,output,modulus_value,← p.shape,localWord_value,
      ringMeaning_mul,ringMeaning_literal,ringMeaning_power,rootExpr_meaning,
      Fin.forall_fin_one] using h
  | second tr i =>
    have h := transformRun_correct p tr p.t (normalizationExpr p tr) (normalizationExpr_valid p tr)
      (fun j => localWord (fun bit => input (.inl (j,bit))))
      (fun k => localWord (fun bit => input (.inr (k,bit))))
    simpa only [localRun,localTable,modulus_value,← p.shape,localWord_value,
      normalizationExpr_meaning] using h
  | product i =>
    let words := fun side : Fin 2 => localWord (fun bit => input (.inl (side,bit)))
    let output := localWord (fun bit => input (.inr bit))
    have hv : (∀ j,bitValue (words j)<bitValue (modulus p)) →
        Valid (modulus p) (.mul (.literal (words 0)) (.literal (words 1))) := by
      intro h
      exact ⟨h 0,h 1⟩
    have h := equationRun_correct p words output _ hv
    simpa only [localRun,localTable,words,output,modulus_value,← p.shape,localWord_value,
      ringMeaning_mul,ringMeaning_literal] using h
  | carryInitial => simp only [localRun,localTable,equalBits_correct,localWord_value,bitValue]
  | carry k =>
    simp only [localRun,localTable,carryRun_correct,localWord_value,targets.value]
  | carryTerminal => simp only [localRun,localTable,equalBits_correct,localWord_value,bitValue]
  | orGate side j => simp only [localRun,localTable,decide_eq_true_eq]
  | inputCheck side => rfl

/-- The complete primitive checker receives the actual ordered Fin port word. -/
def entryRun (p : Config) (targets : Targets p) (v : Vertex p.r p.t p.digits)
    (input : Fin (arity v) → Bool) : CheckRun :=
  localRun p targets v (fun slot => input ((localSlotFinEquiv v) slot))

/-- Literal full-entry refinement, including malformed and noncanonical encodings. -/
theorem entryRun_correct (p : Config) (targets : Targets p) (v : Vertex p.r p.t p.digits)
    (input : Fin (arity v) → Bool) : (entryRun p targets v input).accepted=table p v input := by
  apply Bool.eq_iff_iff.mpr
  simp only [entryRun,table,decide_eq_true_eq]
  exact localRun_correct p targets v _


/-- Shared polynomial bound for the compiled root syntax. -/
theorem rootExpr_nodes (p : Config) (tr : Transform) : nodes (rootExpr p tr)≤2*(p.r*p.t)+1 := by
  cases tr <;> simp only [rootExpr,fourExpr,nodes,powerExpr_nodes]
  · omega
  · have h := Nat.sub_le (p.r*p.t) 1
    omega

/-- Shared polynomial bound for the compiled normalization syntax. -/
theorem normalizationExpr_nodes (p : Config) (tr : Transform) :
    nodes (normalizationExpr p tr)≤2*(p.r*p.t)+4 := by
  cases tr <;> simp only [normalizationExpr,oneExpr,zeroExpr,twoExpr,nodes,powerExpr_nodes]
  · omega
  · have h := Nat.sub_le (p.r*p.t) (p.depth+1)
    omega

/-- Canonicality gate budget for at most n physical words. -/
def canonicalBudget (n : ℕ) : ℕ := n*(12*(n+1)+4)+1

/-- DFT expression syntax budget, including the normalization. -/
def transformNodes (n : ℕ) : ℕ := (2*n+4)+(1+n*(4+n^3*(2*n+2)))+3

/-- Primitive bound of one executed DFT-output comparison. -/
def transformOutputBudget (n : ℕ) : ℕ := transformNodes n*nodeBudget (n+1)

/-- Complete backend bound of a checked DFT block. -/
def transformBudget (n : ℕ) : ℕ :=
  2*canonicalBudget n+1+(n*(transformOutputBudget n+1)+1)+1

/-- One equation with at most n input words. -/
def equationBudget (n exprNodes : ℕ) : ℕ :=
  canonicalBudget n+(12*(n+1)+3)+1+(exprNodes+2)*nodeBudget (n+1)+1

/-- The actual guard's body is charged only when it is executed. -/
theorem guardRun_clock (gate : CheckRun) (body : Unit → CheckRun) {g b : ℕ}
    (hg : gate.clock≤g) (hb : gate.accepted=true → (body ()).clock≤b) :
    (guardRun gate body).clock≤g+b+1 := by
  cases he : gate.accepted with
  | false => simp only [guardRun,he,Bool.false_eq_true,ite_false]; omega
  | true =>
    have h := hb he
    simp only [guardRun,he,ite_true]
    omega

/-- Canonical gates charge every physical comparison and traversal step. -/
theorem canonicalRun_clock {size : ℕ} (p : Config) (words : Fin size → List Bool)
    (hs : size≤p.r*p.t) (hw : ∀ i,(words i).length≤p.r*p.t+1) :
    (canonicalRun p words).clock≤canonicalBudget (p.r*p.t) := by
  have h := allRun_clock (fun i => lessBits (words i) (modulus p))
    (fun i => lessBits_clock (hw i) (modulus_length p).le)
  unfold canonicalRun canonicalBudget
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hs) _)

/-- A complete modular equation has a polynomial backend clock after its gate. -/
theorem equationRun_clock {size : ℕ} (p : Config) (input : Fin size → List Bool)
    (output : List Bool) (expr : Expr) (hs : size≤p.r*p.t)
    (hi : ∀ j,(input j).length≤p.r*p.t+1) (ho : output.length≤p.r*p.t+1)
    (hv : (∀ j,bitValue (input j)<bitValue (modulus p)) → Valid (modulus p) expr) :
    (equationRun p input output expr).clock≤equationBudget (p.r*p.t) (nodes expr) := by
  apply guardRun_clock
    (g:=canonicalBudget (p.r*p.t)+(12*(p.r*p.t+1)+3)+1)
    (b:=(nodes expr+2)*nodeBudget (p.r*p.t+1))
  · have hc := canonicalRun_clock p input hs hi
    have hl := lessBits_clock ho (modulus_length p).le
    dsimp only [andRun]
    omega
  · intro hg
    have hh := (show (canonicalRun p input).accepted=true ∧
        (lessBits output (modulus p)).accepted=true by
      simpa only [andRun,Bool.and_eq_true] using hg)
    have hvexpr := hv ((canonicalRun_correct p input).mp hh.1)
    have hvout : Valid (modulus p) (.literal output) := (lessBits_correct _ _).mp hh.2
    have h := residueEqualityBits_clock (modulus p) (Nat.zero_lt_of_lt (modulus_gt_four p))
      (.literal output) expr hvout hvexpr
    simpa only [nodes,modulus_length,Nat.add_comm 1] using h

/-- Full DFT-block backend cost, including both canonical arrays and every output. -/
theorem transformRun_clock {size : ℕ} (p : Config) (tr : Transform) (stride : ℕ)
    (factor : Expr) (hf : Valid (modulus p) factor) (hfn : nodes factor≤2*(p.r*p.t)+4)
    (input output : Fin size → List Bool) (hs : size≤p.r*p.t) (hst : stride≤p.r*p.t)
    (hi : ∀ j,(input j).length≤p.r*p.t+1) (ho : ∀ j,(output j).length≤p.r*p.t+1) :
    (transformRun p tr stride factor input output).clock≤transformBudget (p.r*p.t) := by
  apply guardRun_clock (g:=2*canonicalBudget (p.r*p.t)+1)
    (b:=p.r*p.t*(transformOutputBudget (p.r*p.t)+1)+1)
  · have hci := canonicalRun_clock p input hs hi
    have hco := canonicalRun_clock p output hs ho
    dsimp only [andRun]
    omega
  · intro hg
    have hh := (show (canonicalRun p input).accepted=true ∧ (canonicalRun p output).accepted=true by
      simpa only [andRun,Bool.and_eq_true] using hg)
    have hvi := (canonicalRun_correct p input).mp hh.1
    have hvo := (canonicalRun_correct p output).mp hh.2
    have hp : 0<bitValue (modulus p) := Nat.zero_lt_of_lt (modulus_gt_four p)
    have hcheck (k : Fin size) :
        (residueEqualityBits (modulus p) (.literal (output k))
          (.mul factor (dotExpr (rootExpr p tr) stride k.val (wordAt input) size))).clock≤
        transformOutputBudget (p.r*p.t) := by
      have hd := dotExpr_valid (modulus p) (by have := modulus_gt_four p; omega)
        _ (rootExpr_valid p tr) stride k.val size (wordAt input)
        (fun j hj => by simpa only [wordAt,dite_eq_left hj] using hvi ⟨j,hj⟩)
      have hcost := residueEqualityBits_clock (modulus p) hp (.literal (output k))
        (.mul factor (dotExpr (rootExpr p tr) stride k.val (wordAt input) size)) (hvo k) ⟨hf,hd⟩
      have hdn := dotExpr_nodes_le (rootExpr p tr) hst
        ((Nat.le_of_lt k.isLt).trans hs) hs (wordAt input)
      have hrn := rootExpr_nodes p tr
      have hnodes : nodes (.literal (output k))+
          nodes (.mul factor (dotExpr (rootExpr p tr) stride k.val (wordAt input) size))+1≤
          transformNodes (p.r*p.t) := by
        dsimp only [nodes,transformNodes]
        have hdn' := hdn.trans (Nat.add_le_add_left
          (Nat.mul_le_mul_right (4+(p.r*p.t)^3*(nodes (rootExpr p tr)+1)) hs) 1)
        have hmul' : p.r*p.t*(4+(p.r*p.t)^3*(nodes (rootExpr p tr)+1))≤
            p.r*p.t*(4+(p.r*p.t)^3*(2*(p.r*p.t)+2)) := by
          exact Nat.mul_le_mul_left _ (Nat.add_le_add_left
            (Nat.mul_le_mul_left _ (show nodes (rootExpr p tr)+1≤2*(p.r*p.t)+2 by omega)) 4)
        omega
      exact hcost.trans (by rw [modulus_length]; exact Nat.mul_le_mul_right _ hnodes)
    have h := allRun_clock _ hcheck
    exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hs) _)


/-- Public shape bounds for every loop, radix and literal comparison word. -/
theorem config_axes (p : Config) :
    0<p.r ∧ 0<p.t ∧ p.r≤p.r*p.t ∧ p.t≤p.r*p.t ∧ p.bits≤p.r*p.t := by
  have hn := (config_size p).2
  have hq := p.quarter
  have hp := p.bits_pos
  have hr : 0<p.r := by nlinarith
  have ht : 0<p.t := by nlinarith
  refine ⟨hr,ht,?_,?_,?_⟩ <;> nlinarith

/-- The local Boolean-list view keeps exactly the word's physical cells. -/
theorem localWord_length {width : ℕ} (input : Fin width → Bool) :
    (localWord input).length=width := portBits_length input

/-- Physical power bounds have one high true cell beyond their offset template. -/
theorem boundBits_length (width : ℕ) : (boundBits width).length=width+1 := by
  simpa only [boundBits,List.length_replicate] using
    (powerTemplateBits_exact (List.replicate width false)).2.1

/-- Source flags pay the actual chosen comparison and one Boolean equality. -/
theorem flagRun_clock {word : List Bool} {width : ℕ} (index : ℕ) (flag : Bool)
    (hw : word.length≤width) (hwidth : 2≤width) :
    (flagRun index word flag).clock≤24*width+9 := by
  unfold flagRun
  split
  · have h := lessBits_clock hw (show ([false,true] : List Bool).length≤width by simpa using hwidth)
    dsimp only
    omega
  · have h := equalBits_clock hw (show ([] : List Bool).length≤width by simp)
    dsimp only
    omega

/-- Full backend clock for the strict physical carry vertex. -/
theorem carryRun_clock (p : Config) {target coefficient previous next : List Bool}
    (ht : target.length≤p.r*p.t+1) (hc : coefficient.length≤p.r*p.t+1)
    (hp : previous.length≤p.r*p.t+1) (hn : next.length≤p.r*p.t+1) :
    (carryRun p target coefficient previous next).clock≤136*(p.r*p.t+1)+112 := by
  have hb : (boundBits (p.r*p.t)).length≤p.r*p.t+1 := (boundBits_length _).le
  have hcoef := lessBits_clock hc (modulus_length p).le
  have hprev := lessBits_clock hp hb
  have hnext := lessBits_clock hn hb
  have hoff : (List.replicate p.bits false).length≤p.r*p.t+1 := by
    simp only [List.length_replicate]
    have := (config_axes p).2.2.2.2
    omega
  have he := carryEquationBits_clock hoff hc hp ht hn
  dsimp only [carryRun,andRun]
  omega

/-- Scale syntax budget; each actual twiddle index product is at most n. -/
def scaleNodes (n : ℕ) : ℕ := 3+n*(2*n+2)

/-- An explicit fixed polynomial bounds every actual local backend clock. -/
def entryBudget (n : ℕ) : ℕ := transformBudget n+equationBudget n (scaleNodes n)+
  equationBudget n 3+200*(n+1)+200

/-- Whole literal-vertex backend clock, including malformed-input branches. -/
theorem localRun_clock (p : Config) (targets : Targets p)
    (v : Vertex p.r p.t p.digits) (input : LocalSlot v → Bool) :
    (localRun p targets v input).clock≤entryBudget (p.r*p.t) := by
  have haxes := config_axes p
  have hfour := (config_size p).2
  have hlinear : 200*(p.r*p.t+1)+200≤entryBudget (p.r*p.t) := by unfold entryBudget; omega
  have htransform : transformBudget (p.r*p.t)≤entryBudget (p.r*p.t) := by unfold entryBudget; omega
  have hscale : equationBudget (p.r*p.t) (scaleNodes (p.r*p.t))≤entryBudget (p.r*p.t) := by unfold entryBudget; omega
  have hproduct : equationBudget (p.r*p.t) 3≤entryBudget (p.r*p.t) := by unfold entryBudget; omega
  cases v with
  | input side i =>
    dsimp only [localRun]
    split
    · rename_i hi
      have hw := (localWord_length (fun bit => input (.inl bit))).le
      have hb : (boundBits (p.width ⟨i.val,hi⟩)).length≤p.r*p.t+1 := by
        rw [boundBits_length]
        exact Nat.add_le_add_right ((p.width_le _).trans haxes.2.2.2.2) 1
      have hless := lessBits_clock hw hb
      have hflag := flagRun_clock i.val (input (.inr ⟨⟨i.val,hi⟩,rfl⟩)) hw (by omega)
      dsimp only [andRun]
      omega
    · have h := equalBits_clock (localWord_length (fun bit => input (.inl bit))).le (show ([] : List Bool).length≤p.r*p.t+1 by simp)
      exact h.trans (by omega)
  | first tr i =>
    have hf : Valid (modulus p) oneExpr := normalizationExpr_valid p (.inl 0)
    exact (transformRun_clock p tr p.r oneExpr hf (by simp [oneExpr,nodes])
      _ _ haxes.2.2.2.1 haxes.2.2.1
      (fun _ => (localWord_length _).le) (fun _ => (localWord_length _).le)).trans htransform
  | scale tr j k =>
    let word := localWord (fun bit => input (.inl bit))
    let output := localWord (fun bit => input (.inr bit))
    have hv : (∀ _i : Fin 1,bitValue word<bitValue (modulus p)) →
        Valid (modulus p) (.mul (.literal word) (powerExpr (rootExpr p tr) (j.val*k.val))) := by
      intro h
      exact ⟨h 0,powerExpr_valid _ (by have := modulus_gt_four p; omega) _ (rootExpr_valid p tr) _⟩
    have h := equationRun_clock p (fun _ : Fin 1 => word) output _ (by omega)
      (fun _ => (localWord_length _).le) (localWord_length _).le hv
    have he : j.val*k.val≤p.r*p.t := Nat.mul_le_mul (Nat.le_of_lt j.isLt) (Nat.le_of_lt k.isLt)
    have hr := rootExpr_nodes p tr
    have hnodes : nodes (.mul (.literal word) (powerExpr (rootExpr p tr) (j.val*k.val)))≤
        scaleNodes (p.r*p.t) := by
      simp only [nodes,powerExpr_nodes,scaleNodes]
      have hh := Nat.mul_le_mul he (show nodes (rootExpr p tr)+1≤2*(p.r*p.t)+2 by omega)
      omega
    have hm : equationBudget (p.r*p.t)
        (nodes (.mul (.literal word) (powerExpr (rootExpr p tr) (j.val*k.val))))≤
        equationBudget (p.r*p.t) (scaleNodes (p.r*p.t)) := by
      unfold equationBudget
      exact Nat.add_le_add_right (Nat.add_le_add_left
        (Nat.mul_le_mul_right _ (Nat.add_le_add_right hnodes 2)) _) 1
    exact h.trans (hm.trans hscale)
  | second tr i =>
    exact (transformRun_clock p tr p.t (normalizationExpr p tr) (normalizationExpr_valid p tr)
      (normalizationExpr_nodes p tr) _ _ haxes.2.2.1 haxes.2.2.2.1
      (fun _ => (localWord_length _).le) (fun _ => (localWord_length _).le)).trans htransform
  | product i =>
    let words := fun side : Fin 2 => localWord (fun bit => input (.inl (side,bit)))
    let output := localWord (fun bit => input (.inr bit))
    have hv : (∀ j,bitValue (words j)<bitValue (modulus p)) →
        Valid (modulus p) (.mul (.literal (words 0)) (.literal (words 1))) := fun h => ⟨h 0,h 1⟩
    have h := equationRun_clock p words output _ (by omega)
      (fun _ => (localWord_length _).le) (localWord_length _).le hv
    exact h.trans hproduct
  | carryInitial =>
    have h := equalBits_clock (localWord_length input).le (show ([] : List Bool).length≤p.r*p.t+1 by simp)
    exact h.trans (by omega)
  | carry k =>
    have ht : (targets.words k).length≤p.r*p.t+1 := (targets.width k).trans (by omega)
    have h := carryRun_clock p ht
      (localWord_length (fun bit => input (.inl (0,bit)))).le
      (localWord_length (fun bit => input (.inl (1,bit)))).le
      (localWord_length (fun bit => input (.inr bit))).le
    exact h.trans (by omega)
  | carryTerminal =>
    have h := equalBits_clock (localWord_length input).le (show ([] : List Bool).length≤p.r*p.t+1 by simp)
    exact h.trans (by omega)
  | orGate side j => exact (show 5≤200*(p.r*p.t+1)+200 by omega).trans hlinear
  | inputCheck side => exact (show 1≤200*(p.r*p.t+1)+200 by omega).trans hlinear

/-- Uniform backend bound on the actual ordered entry evaluator. -/
theorem entryRun_clock (p : Config) (targets : Targets p) (v : Vertex p.r p.t p.digits)
    (input : Fin (arity v) → Bool) :
    (entryRun p targets v input).clock≤entryBudget (p.r*p.t) := localRun_clock p targets v _


/-- The explicit backend budget is a fixed polynomial of the transform length. -/
theorem entryBudget_polynomial (n : ℕ) : entryBudget n≤1048576*(n+2)^10 := by
  unfold entryBudget transformBudget equationBudget scaleNodes canonicalBudget
    transformOutputBudget transformNodes nodeBudget
  ring_nf
  omega

/-- Every actual ordered vertex has a uniform polynomial primitive backend bound. -/
theorem entryRun_polynomial (p : Config) (targets : Targets p) (v : Vertex p.r p.t p.digits)
    (input : Fin (arity v) → Bool) :
    (entryRun p targets v input).clock≤1048576*(p.r*p.t+2)^10 :=
  (entryRun_clock p targets v input).trans (entryBudget_polynomial _)


open SemiprimeMacroParameters

/-- The literal public-N entry run; target words are explicitly constructed. -/
def publicBitEntry (N : ℕ) (hN : 0<N)
    (v : Vertex (firstAxis (bitLength N)) (secondAxis (bitLength N)) (digitCount (bitLength N)))
    (input : Fin (arity v) → Bool) : CheckRun :=
  entryRun (executablePublicConfig N hN) (configTargets (executablePublicConfig N hN)) v input

/-- The actual public primitive checker is precisely the previously counted tensor. -/
theorem publicBitEntry_correct (N : ℕ) (hN : 0<N)
    (v : Vertex (firstAxis (bitLength N)) (secondAxis (bitLength N)) (digitCount (bitLength N)))
    (input : Fin (arity v) → Bool) :
    (publicBitEntry N hN v input).accepted=table (SemiprimePublicFactorCount.publicConfig N hN) v input := by
  have h := entryRun_correct (executablePublicConfig N hN) (configTargets _) v input
  exact h.trans ((executableEntry_eq_table (executablePublicConfig N hN) v input).symm.trans
    (publicEntry_eq N hN v input))

/-- The public primitive backend bound is a fixed polynomial in input bit length. -/
theorem publicBitEntry_polynomial (N : ℕ) (hN : 0<N)
    (v : Vertex (firstAxis (bitLength N)) (secondAxis (bitLength N)) (digitCount (bitLength N)))
    (input : Fin (arity v) → Bool) :
    (publicBitEntry N hN v input).clock≤1048576*(64*bitLength N+2)^10 := by
  have hL := bitLength_pos hN
  have hn2 := transform_square_upper hL
  have hnpos : 0<transformLength (bitLength N) := by unfold transformLength; positivity
  have hn : transformLength (bitLength N)≤64*bitLength N := by nlinarith
  have h := entryRun_polynomial (executablePublicConfig N hN) (configTargets _) v input
  change (publicBitEntry N hN v input).clock≤
    1048576*(firstAxis (bitLength N)*secondAxis (bitLength N)+2)^10 at h
  rw [axes_product] at h
  exact h.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (Nat.add_le_add_right hn 2) 10))


/-- All physical local entries have a polynomial flat binary input width. -/
theorem arity_flat_bound (p : Config) (v : Vertex p.r p.t p.digits) :
    arity v≤4*(p.r*p.t+1)^2 := by
  have ha := config_axes p
  have hn := (config_size p).2
  cases v <;> simp only [arity]
  all_goals try split
  all_goals nlinarith

/-- Every literal cell retained in an expanded expression, counting repetitions. -/
def literalCells : Expr → ℕ
  | .literal bits => bits.length
  | .add a b | .sub a b | .mul a b => literalCells a+literalCells b

/-- Physical width condition on each literal of a compiled expression. -/
def Sized (width : ℕ) : Expr → Prop
  | .literal bits => bits.length≤width
  | .add a b | .sub a b | .mul a b => Sized width a ∧ Sized width b

/-- Expanded syntax allocation includes, rather than hides, all literal bit cells. -/
theorem literalCells_le (expr : Expr) (width : ℕ) (h : Sized width expr) :
    literalCells expr≤nodes expr*width := by
  induction expr with
  | literal bits => simpa only [literalCells,nodes,Sized,Nat.one_mul] using h
  | add a b ia ib | sub a b ia ib | mul a b ia ib =>
    have ha := ia h.1
    have hb := ib h.2
    simp only [literalCells,nodes]
    nlinarith

/-- Power compilation preserves every literal's physical width. -/
theorem powerExpr_sized (base : Expr) (width e : ℕ) (hw : 1≤width) (h : Sized width base) :
    Sized width (powerExpr base e) := by
  induction e with
  | zero => simpa [powerExpr,oneExpr,Sized] using hw
  | succ e ih => exact ⟨ih,h⟩

/-- DFT compilation preserves the actual input and root literal widths. -/
theorem dotExpr_sized (base : Expr) (width stride frequency count : ℕ)
    (input : ℕ → List Bool) (hw : 1≤width) (hb : Sized width base)
    (hi : ∀ j<count,(input j).length≤width) :
    Sized width (dotExpr base stride frequency input count) := by
  induction count with
  | zero => exact Nat.zero_le _
  | succ count ih =>
    exact ⟨ih (fun j hj => hi j (by omega)),hi count (by omega),powerExpr_sized _ _ _ hw hb⟩

/-- Fixed constants in the actual root expression respect the physical word width. -/
theorem rootExpr_sized (p : Config) (tr : Transform) : Sized (p.r*p.t+1) (rootExpr p tr) := by
  have hn := (config_size p).2
  have hf : Sized (p.r*p.t+1) fourExpr := by simp only [Sized,fourExpr,List.length_cons,List.length_nil]; omega
  cases tr with
  | inl side => exact hf
  | inr marker => exact powerExpr_sized _ _ _ (by omega) hf

/-- Normalizer literals respect the same physical word width. -/
theorem normalizationExpr_sized (p : Config) (tr : Transform) :
    Sized (p.r*p.t+1) (normalizationExpr p tr) := by
  have hn := (config_size p).2
  cases tr with
  | inl side => simp [normalizationExpr,oneExpr,Sized]
  | inr marker =>
    refine ⟨Nat.zero_le _,powerExpr_sized _ _ _ (by omega) ?_⟩
    simp only [twoExpr,Sized,List.length_cons,List.length_nil]
    omega

/-- A simple expanded polynomial envelope for one DFT output's syntax. -/
theorem transformNodes_polynomial (n : ℕ) : transformNodes n≤16*(n+2)^5 := by
  unfold transformNodes
  ring_nf
  omega

/-- Source-dependent input-word gathers made by the literal vertex generator.
The DFT branch includes both canonical arrays and every output's entire dot sum. -/
def gatherBound (p : Config) : Vertex p.r p.t p.digits → ℕ
  | .input _ _ => 1
  | .first _ _ => p.t^2+3*p.t
  | .scale _ _ _ => 3
  | .second _ _ => p.r^2+3*p.r
  | .product _ => 6
  | .carryInitial => 1
  | .carry _ => 3
  | .carryTerminal => 1
  | .orGate _ _ => 0
  | .inputCheck _ => 0

/-- Uniform preparation-read envelope for the actual vertex generators. -/
theorem gatherBound_polynomial (p : Config) (v : Vertex p.r p.t p.digits) :
    gatherBound p v≤4*(p.r*p.t+2)^2 := by
  have ha := config_axes p
  have hn := (config_size p).2
  cases v <;> simp only [gatherBound] <;> nlinarith

/-- At most n compiled output expressions, each with the charged syntax budget. -/
theorem allOutputSyntax_polynomial (n : ℕ) : n*transformNodes n≤32*(n+2)^6 := by
  have h := Nat.mul_le_mul_left n (transformNodes_polynomial n)
  have hm : n*(16*(n+2)^5)≤32*(n+2)^6 := by nlinarith [Nat.zero_le ((n+2)^5)]
  exact h.trans hm

end RiemannGaussian.SemiprimeMacroEntryBitCheck
