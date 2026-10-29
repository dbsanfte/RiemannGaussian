import RiemannGaussian.SemiprimeD1BoundaryLeaf
import RiemannGaussian.SemiprimeD1HybridRecursiveCounter

/-! Executable comparisons of the NEW Lean sequential-record implementation
against the frozen eager leaf. These are finite tests, not a cost/rate proof. -/
set_option autoImplicit false
open RiemannGaussian
open SemiprimeD1JetAxes (Context)

private def coefficient (p n : Nat) : List Bool :=
  (SemiprimeSourceCompactBits.trim ((List.range p).map (fun i => n.testBit i))).bits

private def table (ctx : Context) (salt arity : Nat) : SemiprimeD1TensorTables.Table arity :=
  (SemiprimeD1TensorTables.build arity (fun bits =>
    ⟨(List.range ctx.rank).map (fun j => coefficient ctx.precision
      ((salt+1)*(SemiprimeBitArithmetic.bitValue bits+2)*(j+1)+salt+j)),0⟩)).table

private def network (ctx : Context) (n : Nat) (rows : SemiprimeD1TensorNetwork.Rows n) :
    SemiprimeD1TensorNetwork.Network :=
  ⟨n,rows,
    Vector.ofFn (fun v =>
      let ports:=SemiprimeD1TensorNetwork.leftPorts rows v
      ⟨ports,table ctx v.val ports.length⟩),
    Vector.ofFn (fun e =>
      let ports:=SemiprimeD1TensorNetwork.rightPorts rows e
      ⟨ports,table ctx (n+e.val) ports.length⟩)⟩

private def check (label : String) (ctx : Context) (n : Nat)
    (rows : SemiprimeD1TensorNetwork.Rows n) : IO Unit := do
  let net:=network ctx n rows
  unless (SemiprimeD1BoundaryLeaf.validate ctx net).value do
    throw (IO.userError s!"{label}: acquired literal inputs rejected")
  let fast:=SemiprimeD1BoundaryLeaf.acquire ctx net
  let old:=SemiprimeD1TensorTapeLeaf.leaf ctx net
  unless fast.result.words==old.words do
    throw (IO.userError s!"{label}: exact coefficient bytes differ")
  unless fast.tensor.ports.isEmpty && fast.tensor.entries.length==1 do
    throw (IO.userError s!"{label}: final boundary/scalar shape differs")
  let checked:=SemiprimeD1BoundaryLeaf.checked ctx net
  let exhausted:=SemiprimeD1HybridRecursiveCounter.run 64 0 0 ctx net
  unless exhausted.words==old.words && exhausted.clock==checked.clock+5 do
    throw (IO.userError s!"{label}: exhausted-fuel hybrid caller differs")
  let lam:=SemiprimeD1PackingReady.logarithm 64
  let depth:=lam+1
  unless !(SemiprimeD1RecursiveCounter.activeTest 64 lam depth
      (SemiprimeD1TensorNetwork.edgeCount net)) do
    throw (IO.userError s!"{label}: test expected an inactive caller")
  let inactive:=SemiprimeD1HybridRecursiveCounter.run 64 1 depth ctx net
  unless inactive.words==old.words &&
      inactive.clock==checked.clock+64+lam+depth+SemiprimeD1TensorNetwork.edgeCount net+8 do
    throw (IO.userError s!"{label}: inactive hybrid caller differs")
  IO.println s!"PASS {label}: M={SemiprimeD1TensorNetwork.edgeCount net}, K={fast.plan.k}, W={fast.plan.width}, newReport={fast.result.clock}, oldReport={old.clock}"

def main : IO Unit := do
  check "empty scalar" ⟨[],4⟩ 0 []
  check "isolated scalar vertices" ⟨[],4⟩ 3 [[],[]]
  check "parallel occurrences" ⟨[],5⟩ 2 [[0,0],[1]]
  check "cycle and zero-port factor" ⟨[],5⟩ 2 [[0,1],[0,1],[]]
  check "whole mixed jet" ⟨[2,3],3⟩ 2 [[0,1],[0]]
  check "zero precision scalar" ⟨[],0⟩ 2 [[0,0],[1],[]]
  check "zero precision mixed jet" ⟨[2,3],0⟩ 2 [[0,1]]
  let malformed:SemiprimeD1TensorNetwork.Network:=
    ⟨1,[],Vector.ofFn (fun _ => ⟨[0],.fork (.leaf [[true]]) (.leaf [[]])⟩),Vector.ofFn Fin.elim0⟩
  unless !(SemiprimeD1BoundaryLeaf.validate ⟨[],2⟩ malformed).value do
    throw (IO.userError "malformed ordered ports accepted")
  unless (SemiprimeD1BoundaryLeaf.checked ⟨[],2⟩ malformed).words==
      (SemiprimeD1TensorTapeLeaf.leaf ⟨[],2⟩ malformed).words do
    throw (IO.userError "paid malformed fallback differs")
  IO.println "PASS malformed paid fallback"
