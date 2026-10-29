import RiemannGaussian.SemiprimeD1StackJetFold
import RiemannGaussian.SemiprimeD1RecursiveCounter
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 65536
set_option maxRecDepth 32768
open RiemannGaussian
open SemiprimeD1StackJetFold
private def drive :Nat→C.State Stack Label→Nat→Nat→Option (C.State Stack Label×Nat×Nat)
  | 0,_,_,_=>none
  | n+1,s,products,sums=>
    match s.pc with
    | none=>some (s,products,sums)
    | some pc=>
      let products:=match pc with | .local .productVisit=>products+1 | _=>products
      let sums:=match pc with | .local .sumVisit=>sums+1 | _=>sums
      match SemiprimeD1StackCalls.step program s with
      | none=>none
      | some q=>drive n q products sums
private def check (axisValues:List Nat) (precision:List Bool) (modes:List (List (List (List Bool)))) :Bool:=
  let enc:=SemiprimeD1TensorTapeCodec.vectorBits
  let axisTape:=enc (axisValues.map (fun n=>List.replicate n true))
  let childTape:=enc (modes.map fun group=>enc (group.map enc))
  let ctx:SemiprimeD1JetAxes.Context:=⟨axisValues,SemiprimeBitArithmetic.bitValue precision⟩
  let terms:=modes.map fun group=>SemiprimeD1RecursiveCounter.product ctx (group.map fun words=>⟨words,0⟩)
  let answer:=(SemiprimeD1JetAffineCoefficient.sumRuns ctx terms).words
  match drive 50000 (initial axisTape precision childTape) 0 0 with
  | none=>false
  | some (s,products,sums)=>s.flag.isNone && s.returned.isNone && s.frames.isEmpty &&
    s.data output==enc answer && s.data axes==axisTape && s.data (aux .precision)==precision &&
    s.data (aux .children)==childTape && s.data rank==List.replicate axisValues.prod true &&
    s.data width==List.replicate ctx.precision true &&
    products==(modes.map fun row=>row.length+1).sum && sums==modes.length+1
#eval [check [] [] [],check [] [true] [[]],check [] [false,true] [[[[true,false]],[[false,true]]]],
  check [] [true] [[[[true]]],[[[false,true,false]],[[true,true]]]],
  check [2] [true] [[[[true],[false,true]],[[true,false],[true]]]]]
