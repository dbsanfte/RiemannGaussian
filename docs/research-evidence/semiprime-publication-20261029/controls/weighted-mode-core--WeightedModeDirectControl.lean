import RiemannGaussian.SemiprimeD1StackWeightedMode
import RiemannGaussian.SemiprimeD1TensorTapeCodec
set_option autoImplicit false
set_option Elab.async false
open RiemannGaussian
open SemiprimeD1StackWeightedMode
private def fields : Array Stack :=#[.catalogue,.width,.weights,.budget,.path,.weight,.exponent,.frames,.tuple,.pathReader,
  .fieldScratch,.valid,.copyScratch,.frameScratch,.subTodo,.history,.output]
private def drive :Nat→C.State Stack Label→Nat→Nat→Option (C.State Stack Label×Nat×Nat)
  | 0,_,_,_=>none
  | n+1,s,visits,peak=>
    match s.pc with
    | none=>some (s,visits,peak)
    | some pc=>
      let visits:=match pc with | .inl .visit=>visits+1 | _=>visits
      match SemiprimeD1StackCalls.step program s with
      | none=>none
      | some q=>drive n q visits (max peak q.frames.length)
private def check (ws:List Nat) (precision:Nat) :Bool:=
  let unary:=fun n=>List.replicate n true
  let encode:=SemiprimeD1TensorTapeCodec.vectorBits
  let cat:=encode (ws.map unary)
  let out:=encode ((SemiprimeD1WeightedTuples.tuples ws (precision-1)).map (fun es=>encode (es.map unary)))
  match drive 20000 (initial cat (unary precision)) 0 0 with
  | none=>false
  | some (s,visits,peak)=>
    s.flag.isNone && s.returned.isNone && s.frames.isEmpty &&
    (s.data .output==out) && (visits==SemiprimeD1WeightedTuples.visits ws (precision-1)) &&
    (fields.all fun k=>s.data k==(if k=.catalogue then cat else if k=.width then unary precision else if k=.output then out else [])) &&
    decide (peak ≤ ws.length+2)
#eval [check [] 0,check [] 1,check [1] 1,check [1] 3,check [1,1] 3,check [1,2] 4,check [2,5] 2]
