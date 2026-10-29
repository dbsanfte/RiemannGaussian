/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceArrayProgramCompiler
import RiemannGaussian.SemiprimeMaterializedPacking

/-! # Executed finite generation of cached source instruction blocks
Cached size metadata and fixed-shape output-ID arithmetic avoid a functional
register oracle. Literal scans and every code append copy retain their work.
The ledger is scalar/list metadata work, not a complete primitive-bit compiler.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace RiemannGaussian.SemiprimeSourceArrayProgramGeneration
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation
open SemiprimeMaterializedSourceUniversal
open SemiprimeSourceArrayProgramIR SemiprimeSourceArrayProgramBlocks
open SemiprimeSourceArrayProgramCompiler

/-- Actual recursive append, with each copied cons cell paid. -/
def append {α : Type*} : List α → List α → Run (List α)
  | [],ys => ⟨ys,1⟩
  | x::xs,ys => let tail := append xs ys; ⟨x::tail.value,tail.work+2⟩

/-- Exact copied list and code generation stages. -/
theorem append_value_work {α : Type*} (xs ys : List α) :
    (append xs ys).value=xs++ys ∧ (append xs ys).work=2*xs.length+1 := by
  induction xs with
  | nil => simp [append]
  | cons x xs ih =>
    simp only [append,ih.1,ih.2,List.cons_append,List.length_cons]
    constructor
    · trivial
    · omega

/-- Cached output-ID formula of one actual compiler node. -/
inductive Shape where
  | constant (value zeroId : ℕ)
  | variable (oneId zeroId : ℕ)
  | addition (start : ℕ)
  | multiplication (start : ℕ)

/-- The original simple arithmetic formula behind the output lookup. -/
def Shape.value : Shape → ℕ → ℕ
  | .constant value zeroId,k => if k=0 then value else zeroId
  | .variable oneId zeroId,k => if k=1 then oneId else zeroId
  | .addition start,k => start+k
  | .multiplication start,k => mulResult start k

/-- Actual scalar metadata lookup, with every bounded arithmetic/branch stage retained. -/
def Shape.read (s : Shape) (k : ℕ) : Run ℕ :=
  match s with
  | .constant value zeroId => ⟨if k=0 then value else zeroId,2⟩
  | .variable oneId zeroId => ⟨if k=1 then oneId else zeroId,2⟩
  | .addition start => ⟨start+k,2⟩
  | .multiplication start => ⟨start+(k+1)*(k+2)-1,6⟩

/-- Every produced register map is computed, never queried as an arbitrary function. -/
theorem Shape.read_value (s : Shape) (k : ℕ) : (s.read k).value=s.value k := by cases s <;> rfl

/-- Uniform original scalar-ID lookup cost. -/
theorem Shape.read_work (s : Shape) (k : ℕ) : (s.read k).work ≤ 6 := by cases s <;> simp [Shape.read]

/-- Actual generated code, cached length, and retained generation work. -/
structure CodeRun where
  /-- Constructed instruction list. -/
  code : List Instruction
  /-- Acquired length metadata. -/
  size : ℕ
  /-- Scalar/read/cons/copy generation stages. -/
  work : ℕ
  /-- Cached length is always the actual output length. -/
  size_eq : size=code.length

/-- Empty code still retains original leaf-lookup/control work. -/
def emptyCode (work : ℕ) : CodeRun := ⟨[],0,work,rfl⟩

/-- Copy the actual first code list and retain both already acquired child reports. -/
def join (a b : CodeRun) : CodeRun :=
  let out := append a.code b.code
  ⟨out.value,a.size+b.size,a.work+b.work+out.work+3,by rw [(append_value_work _ _).1,List.length_append,← a.size_eq,← b.size_eq]⟩

/-- Exact code and cached metadata from executed joining. -/
theorem join_code_size_work (a b : CodeRun) :
    (join a b).code=a.code++b.code ∧ (join a b).size=a.size+b.size ∧
      (join a b).work=a.work+b.work+2*a.size+4 := by
  refine ⟨(append_value_work a.code b.code).1,rfl,?_⟩
  simp only [join,(append_value_work _ _).2]
  rw [← a.size_eq]
  omega

/-- Execute all coefficient-addition code generation, including both output-ID reads. -/
def addRun (a b : Shape) : ℕ → CodeRun
  | 0 => emptyCode 1
  | J+1 =>
      let previous := addRun a b J
      let left := a.read J
      let right := b.read J
      let one : CodeRun := ⟨[⟨.add,left.value,right.value⟩],1,left.work+right.work+10,rfl⟩
      join previous one

/-- The actual add generator emits precisely the compiler's coefficient block. -/
theorem addRun_code (a b : Shape) (J : ℕ) : (addRun a b J).code=addCode J a.value b.value := by
  induction J with
  | zero => rfl
  | succ J ih =>
    simp only [addRun,(join_code_size_work _ _).1,ih,Shape.read_value,addCode,List.range_succ,List.map_append,List.map_singleton]

/-- Add generator length metadata is exact. -/
theorem addRun_size (a b : Shape) (J : ℕ) : (addRun a b J).size=J := by
  rw [(addRun a b J).size_eq,addRun_code,addCode_length]

/-- Actual addition-code generation has quadratic scalar/list work. -/
theorem addRun_work (a b : Shape) (J : ℕ) : (addRun a b J).work ≤ 60*(J+1)^2 := by
  induction J with
  | zero => norm_num [addRun,emptyCode]
  | succ J ih =>
    have hl := a.read_work J
    have hr := b.read_work J
    simp only [addRun,(join_code_size_work _ _).2.2,addRun_size]
    nlinarith

/-- Generate both operations per actual dot prefix, with paid cached-ID arithmetic. -/
def dotRun (zeroId start k : ℕ) (a b : Shape) : ℕ → CodeRun
  | 0 => emptyCode 1
  | len+1 =>
      let previous := dotRun zeroId start k a b len
      let left := a.read len
      let right := b.read (k-len)
      let pair : CodeRun :=
        ⟨[⟨.mul,left.value,right.value⟩,⟨.add,start+2*len,accumulator zeroId start len⟩],
          2,left.work+right.work+20,rfl⟩
      join previous pair

/-- The generated scalar dot code is exactly the original stable-ID block. -/
theorem dotRun_code (zeroId start k : ℕ) (a b : Shape) (len : ℕ) :
    (dotRun zeroId start k a b len).code=dotCode zeroId start k a.value b.value len := by
  induction len with
  | zero => rfl
  | succ len ih => simp only [dotRun,(join_code_size_work _ _).1,ih,Shape.read_value,dotCode]

/-- Dot generation caches its exact size. -/
theorem dotRun_size (zeroId start k : ℕ) (a b : Shape) (len : ℕ) :
    (dotRun zeroId start k a b len).size=2*len := by
  rw [(dotRun zeroId start k a b len).size_eq,dotRun_code,dotCode_length]

/-- Paid dot-code generation has quadratic work, including append traversal. -/
theorem dotRun_work (zeroId start k : ℕ) (a b : Shape) (len : ℕ) :
    (dotRun zeroId start k a b len).work ≤ 80*(len+1)^2 := by
  induction len with
  | zero => norm_num [dotRun,emptyCode]
  | succ len ih =>
    have hl := a.read_work len
    have hr := b.read_work (k-len)
    simp only [dotRun,(join_code_size_work _ _).2.2,dotRun_size]
    nlinarith

/-- Generate cached full-array convolution once, not a per-coefficient source-AST expansion. -/
def mulRun (zeroId start : ℕ) (a b : Shape) : ℕ → CodeRun
  | 0 => emptyCode 1
  | J+1 =>
      let previous := mulRun zeroId start a b J
      let dot := dotRun zeroId (start+previous.size) J a b (J+1)
      join previous dot

/-- Actual convolution generator matches its scalar instruction semantics. -/
theorem mulRun_code (zeroId start : ℕ) (a b : Shape) (J : ℕ) :
    (mulRun zeroId start a b J).code=mulCode zeroId start a.value b.value J := by
  induction J with
  | zero => rfl
  | succ J ih =>
    simp only [mulRun,(join_code_size_work _ _).1,dotRun_code,ih,mulCode]
    rw [(mulRun zeroId start a b J).size_eq,ih]

/-- Exact metadata length of actual convolution code. -/
theorem mulRun_size (zeroId start : ℕ) (a b : Shape) (J : ℕ) :
    (mulRun zeroId start a b J).size=J*(J+1) := by
  rw [(mulRun zeroId start a b J).size_eq,mulRun_code,mulCode_length]

/-- Full convolution-code generation has a fixed cubic list/scalar bound. -/
theorem mulRun_work (zeroId start : ℕ) (a b : Shape) (J : ℕ) :
    (mulRun zeroId start a b J).work ≤ 200*(J+1)^3 := by
  induction J with
  | zero => norm_num [mulRun,emptyCode]
  | succ J ih =>
    have hd := dotRun_work zeroId (start+(mulRun zeroId start a b J).size) J a b (J+1)
    rw [mulRun_size] at hd
    simp only [mulRun,(join_code_size_work _ _).2.2,mulRun_size]
    nlinarith

/-- Acquired cached code and a concrete finite output-ID descriptor. -/
structure Acquired where
  /-- Actual constructed code and retained stages. -/
  compiled : CodeRun
  /-- Output IDs have one of four original compiler-node formulas. -/
  shape : Shape

/-- Mathematical block view consumed by the verified compiler/refinement. -/
def Acquired.block (a : Acquired) : Block := ⟨a.compiled.code,a.shape.value⟩

/-- Cached metadata is exactly the actual block length. -/
theorem Acquired.size_eq_block (a : Acquired) : a.compiled.size=a.block.code.length := a.compiled.size_eq

/-- Additional finite control/metadata stages, with the same acquired code. -/
def bump (n : ℕ) (a : CodeRun) : CodeRun := ⟨a.code,a.size,a.work+n,a.size_eq⟩

/-- Assemble one actual addition node after both children have been acquired. -/
def assembleAdd (J next : ℕ) (a b : Acquired) : Acquired :=
  let children := join a.compiled b.compiled
  let start := next+children.size
  let out := addRun a.shape b.shape J
  ⟨bump 10 (join children out),.addition start⟩

/-- Assemble one actual convolution node after both children have been acquired. -/
def assembleMul (J zeroId next : ℕ) (a b : Acquired) : Acquired :=
  let children := join a.compiled b.compiled
  let start := next+children.size
  let out := mulRun zeroId start a.shape b.shape J
  ⟨bump 10 (join children out),.multiplication start⟩

/-- Exact projection of actual cached addition assembly. -/
theorem assembleAdd_block (J next : ℕ) (a b : Acquired) :
    (assembleAdd J next a b).block=
      (let combined := a.block.code++b.block.code
       let start := next+combined.length
       (⟨combined++addCode J a.block.output b.block.output,fun k => start+k⟩ : Block)) := by
  simp only [assembleAdd,Acquired.block,bump,(join_code_size_work _ _).1,
    (join_code_size_work _ _).2.1,addRun_code]
  rw [a.compiled.size_eq,b.compiled.size_eq,List.length_append]
  rfl

/-- Exact projection of actual cached convolution assembly. -/
theorem assembleMul_block (J zeroId next : ℕ) (a b : Acquired) :
    (assembleMul J zeroId next a b).block=
      (let combined := a.block.code++b.block.code
       let start := next+combined.length
       (⟨combined++mulCode zeroId start a.block.output b.block.output J,fun k => mulResult start k⟩ : Block)) := by
  simp only [assembleMul,Acquired.block,bump,(join_code_size_work _ _).1,
    (join_code_size_work _ _).2.1,mulRun_code]
  rw [a.compiled.size_eq,b.compiled.size_eq,List.length_append]
  rfl

/-- Actual AST traversal, using a cached original literal menu and paid finite scans. -/
def acquire (J zeroId oneId next : ℕ) (cache : List ℚ) : PolynomialCode ℚ → Acquired
  | .constant c =>
      let found := SemiprimeMaterializedPacking.position c cache
      ⟨emptyCode (found.work+5),.constant (found.value+2) zeroId⟩
  | .indeterminate => ⟨emptyCode 3,.variable oneId zeroId⟩
  | .add p q =>
      let left := acquire J zeroId oneId next cache p
      let right := acquire J zeroId oneId (next+left.compiled.size) cache q
      assembleAdd J next left right
  | .mul p q =>
      let left := acquire J zeroId oneId next cache p
      let right := acquire J zeroId oneId (next+left.compiled.size) cache q
      assembleMul J zeroId next left right

/-- The actual generator computes the SAME code and registers, never a supplied program. -/
theorem acquire_block (J zeroId oneId next : ℕ) (cache : List ℚ) (p : PolynomialCode ℚ) :
    (acquire J zeroId oneId next cache p).block=
      compile J zeroId oneId next (fun c => 2+cache.idxOf c) p := by
  induction p generalizing next with
  | constant c =>
    simp only [acquire,Acquired.block,emptyCode,
      SemiprimeMaterializedPacking.position_value,compile]
    congr 1
    funext k
    change (if k=0 then cache.idxOf c+2 else zeroId)=(if k=0 then 2+cache.idxOf c else zeroId)
    split_ifs <;> omega
  | indeterminate => rfl
  | add p q hp hq =>
    rw [acquire,assembleAdd_block,Acquired.size_eq_block,hp,hq]
    rfl
  | mul p q hp hq =>
    rw [acquire,assembleMul_block,Acquired.size_eq_block,hp,hq]
    rfl

/-- Actual syntax-leaf collection, paying every append traversal and cons. -/
def constantsRun : PolynomialCode ℚ → Run (List ℚ)
  | .constant c => ⟨[c],2⟩
  | .indeterminate => ⟨[],1⟩
  | .add p q =>
      let a := constantsRun p
      let b := constantsRun q
      let out := append a.value b.value
      ⟨out.value,a.work+b.work+out.work+2⟩
  | .mul p q =>
      let a := constantsRun p
      let b := constantsRun q
      let out := append a.value b.value
      ⟨out.value,a.work+b.work+out.work+2⟩

/-- The acquired literal cache is exactly the original traversal order. -/
theorem constantsRun_value (p : PolynomialCode ℚ) : (constantsRun p).value=constants p := by
  induction p with
  | constant c => rfl
  | indeterminate => rfl
  | add p q hp hq => simp only [constantsRun,(append_value_work _ _).1,hp,hq,constants]
  | mul p q hp hq => simp only [constantsRun,(append_value_work _ _).1,hp,hq,constants]

/-- Returned generator record, with original constants and every construction report retained. -/
structure Generated where
  /-- Actual acquired original bank. -/
  bank : List ℚ
  /-- Actual acquired generated code and cached output-ID descriptor. -/
  result : Acquired
  /-- Complete bank/code generation ledger. -/
  work : ℕ

/-- Actual generated block view. -/
def Generated.block (g : Generated) : Block := g.result.block

/-- Acquire the original literal cache ONCE, then generate the cached AST code. -/
def generate (J : ℕ) (p : PolynomialCode ℚ) : Generated :=
  let literals := constantsRun p
  let inputs := 0::1::literals.value
  let result := acquire J 0 1 (literals.value.length+2) literals.value p
  ⟨inputs,result,literals.work+result.compiled.work+literals.value.length+7⟩

/-- The actual generator exposes the original input bank, not external constant advice. -/
theorem generate_bank (J : ℕ) (p : PolynomialCode ℚ) : (generate J p).bank=bank p := by
  simp only [generate,constantsRun_value,bank]

/-- The actual generated code/registers equal the fully initialized original compiler. -/
theorem generate_block (J : ℕ) (p : PolynomialCode ℚ) : (generate J p).block=program J p := by
  simp only [generate,Generated.block,acquire_block,constantsRun_value,program]
  rw [bank_length]
  congr 1
  omega

/-- Exact scalar/list stage split of actual addition assembly. -/
theorem assembleAdd_work (J next : ℕ) (a b : Acquired) :
    (assembleAdd J next a b).compiled.work=
      a.compiled.work+b.compiled.work+(addRun a.shape b.shape J).work+
        4*a.compiled.size+2*b.compiled.size+18 := by
  simp only [assembleAdd,bump,(join_code_size_work _ _).2.2,(join_code_size_work _ _).2.1]
  ring

/-- Exact scalar/list stage split of actual convolution assembly. -/
theorem assembleMul_work (J zeroId next : ℕ) (a b : Acquired) :
    (assembleMul J zeroId next a b).compiled.work=
      a.compiled.work+b.compiled.work+
        (mulRun zeroId (next+(a.compiled.size+b.compiled.size)) a.shape b.shape J).work+
        4*a.compiled.size+2*b.compiled.size+18 := by
  simp only [assembleMul,bump,(join_code_size_work _ _).2.2,(join_code_size_work _ _).2.1]
  ring

/-- Actual generated lengths are bounded by original syntax, independent of register values. -/
theorem acquire_size_bound (J zeroId oneId next : ℕ) (cache : List ℚ) (p : PolynomialCode ℚ) :
    (acquire J zeroId oneId next cache p).compiled.size ≤
      SemiprimeSourceCodeArrays.nodes p*(J*(J+1)+J) := by
  rw [Acquired.size_eq_block,acquire_block]
  exact compile_code_length _ _ _ _ _ _

/-- Collecting the original constant cache has a quadratic actual traversal/copy budget. -/
theorem constantsRun_work (p : PolynomialCode ℚ) :
    (constantsRun p).work ≤ 5*(SemiprimeSourceCodeArrays.nodes p)^2 := by
  induction p with
  | constant c => norm_num [constantsRun,SemiprimeSourceCodeArrays.nodes]
  | indeterminate => norm_num [constantsRun,SemiprimeSourceCodeArrays.nodes]
  | add p q hp hq =>
    have hl := constants_length_le p
    simp only [constantsRun,(append_value_work _ _).2,constantsRun_value,SemiprimeSourceCodeArrays.nodes]
    nlinarith [Nat.zero_le (SemiprimeSourceCodeArrays.nodes p*SemiprimeSourceCodeArrays.nodes q)]
  | mul p q hp hq =>
    have hl := constants_length_le p
    simp only [constantsRun,(append_value_work _ _).2,constantsRun_value,SemiprimeSourceCodeArrays.nodes]
    nlinarith [Nat.zero_le (SemiprimeSourceCodeArrays.nodes p*SemiprimeSourceCodeArrays.nodes q)]

/-- One original-size allowance for all node-local scans, copies and scalar code construction. -/
def unitWork (J L N : ℕ) : ℕ :=
  3*L+6+6*N*(J*(J+1)+J)+300*(J+1)^3+50

/-- Actual compiler construction has a fixed polynomial bound with no instruction-answer advice. -/
theorem acquire_work (J zeroId oneId next : ℕ) (cache : List ℚ) (p : PolynomialCode ℚ)
    (N : ℕ) (hN : SemiprimeSourceCodeArrays.nodes p ≤ N) :
    (acquire J zeroId oneId next cache p).compiled.work ≤
      SemiprimeSourceCodeArrays.nodes p*unitWork J cache.length N := by
  induction p generalizing next with
  | constant c =>
    have h := SemiprimeMaterializedPacking.position_work c cache
    simp only [acquire,emptyCode,SemiprimeSourceCodeArrays.nodes]
    unfold unitWork
    omega
  | indeterminate =>
    simp only [acquire,emptyCode,SemiprimeSourceCodeArrays.nodes]
    unfold unitWork
    omega
  | add p q hp hq =>
    have hnP : SemiprimeSourceCodeArrays.nodes p ≤ N := by simp only [SemiprimeSourceCodeArrays.nodes] at hN;omega
    have hnQ : SemiprimeSourceCodeArrays.nodes q ≤ N := by simp only [SemiprimeSourceCodeArrays.nodes] at hN;omega
    let a := acquire J zeroId oneId next cache p
    let b := acquire J zeroId oneId (next+a.compiled.size) cache q
    have hl := hp next hnP
    have hr := hq (next+a.compiled.size) hnQ
    have hls : a.compiled.size ≤ N*(J*(J+1)+J) :=
      (acquire_size_bound J zeroId oneId next cache p).trans (Nat.mul_le_mul_right _ hnP)
    have hrs : b.compiled.size ≤ N*(J*(J+1)+J) :=
      (acquire_size_bound J zeroId oneId (next+a.compiled.size) cache q).trans (Nat.mul_le_mul_right _ hnQ)
    have ho := addRun_work a.shape b.shape J
    have hpow : (J+1)^2 ≤ (J+1)^3 := Nat.pow_le_pow_right (by omega) (by decide)
    have hunit : (addRun a.shape b.shape J).work+4*a.compiled.size+2*b.compiled.size+18 ≤ unitWork J cache.length N := by
      unfold unitWork
      nlinarith
    change (assembleAdd J next a b).compiled.work ≤ _
    rw [assembleAdd_work]
    simp only [SemiprimeSourceCodeArrays.nodes]
    change a.compiled.work ≤ _ at hl
    change b.compiled.work ≤ _ at hr
    nlinarith
  | mul p q hp hq =>
    have hnP : SemiprimeSourceCodeArrays.nodes p ≤ N := by simp only [SemiprimeSourceCodeArrays.nodes] at hN;omega
    have hnQ : SemiprimeSourceCodeArrays.nodes q ≤ N := by simp only [SemiprimeSourceCodeArrays.nodes] at hN;omega
    let a := acquire J zeroId oneId next cache p
    let b := acquire J zeroId oneId (next+a.compiled.size) cache q
    have hl := hp next hnP
    have hr := hq (next+a.compiled.size) hnQ
    have hls : a.compiled.size ≤ N*(J*(J+1)+J) :=
      (acquire_size_bound J zeroId oneId next cache p).trans (Nat.mul_le_mul_right _ hnP)
    have hrs : b.compiled.size ≤ N*(J*(J+1)+J) :=
      (acquire_size_bound J zeroId oneId (next+a.compiled.size) cache q).trans (Nat.mul_le_mul_right _ hnQ)
    have ho := mulRun_work zeroId (next+(a.compiled.size+b.compiled.size)) a.shape b.shape J
    have hunit : (mulRun zeroId (next+(a.compiled.size+b.compiled.size)) a.shape b.shape J).work+
        4*a.compiled.size+2*b.compiled.size+18 ≤ unitWork J cache.length N := by
      unfold unitWork
      nlinarith
    change (assembleMul J zeroId next a b).compiled.work ≤ _
    rw [assembleMul_work]
    simp only [SemiprimeSourceCodeArrays.nodes]
    change a.compiled.work ≤ _ at hl
    change b.compiled.work ≤ _ at hr
    nlinarith

/-- A literal fixed polynomial for complete original syntax/bank/code acquisition. -/
def generationBudget (J N : ℕ) : ℕ := 5*N^2+N*unitWork J N N+N+7

/-- The actual original-only generator includes all constant scans and cached-code construction. -/
theorem generate_work (J : ℕ) (p : PolynomialCode ℚ) :
    (generate J p).work ≤ generationBudget J (SemiprimeSourceCodeArrays.nodes p) := by
  have hc := constantsRun_work p
  have hl := constants_length_le p
  have ha := acquire_work J 0 1 ((constants p).length+2) (constants p) p
    (SemiprimeSourceCodeArrays.nodes p) le_rfl
  have hu : unitWork J (constants p).length (SemiprimeSourceCodeArrays.nodes p) ≤
      unitWork J (SemiprimeSourceCodeArrays.nodes p) (SemiprimeSourceCodeArrays.nodes p) := by
    unfold unitWork
    omega
  have ha' := ha.trans (Nat.mul_le_mul_left _ hu)
  simp only [generate,constantsRun_value]
  unfold generationBudget
  omega

end RiemannGaussian.SemiprimeSourceArrayProgramGeneration
