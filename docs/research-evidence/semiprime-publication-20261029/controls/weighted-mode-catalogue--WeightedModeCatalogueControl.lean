import RiemannGaussian.SemiprimeD1StackWeightedModeCatalogue
set_option autoImplicit false
set_option Elab.async false
open RiemannGaussian
open SemiprimeD1StackWeightedModeCatalogue
private def drive :Nat→C.State Stack Label→Nat→Option (C.State Stack Label×Nat)
  | 0,_,_=>none
  | n+1,s,v=>
    match s.pc with
    | none=>some (s,v)
    | some pc=>
      let v:=match pc with | .inr (.inl (.inl .visit))=>v+1 | _=>v
      match SemiprimeD1StackCalls.step program s with
      | none=>none
      | some q=>drive n q v
private def check (p t width:Nat) :Bool:=
  let u:=fun n=>List.replicate n true
  let enc:=SemiprimeD1TensorTapeCodec.vectorBits
  let P:=width-1
  let ws:=SemiprimeD1ModeCatalog.weights (p*t) P
  let modes:=SemiprimeD1ModeCatalog.catalog (p*t) P
  let labels:=enc (modes.map fun m=>SemiprimeSourceHistogramKeyBits.frame (u m.slot) (SemiprimeSourceHistogramKeyBits.frame (u m.order) []))
  let output:=enc ((SemiprimeD1WeightedTuples.tuples ws P).map fun es=>enc (es.map u))
  match drive 20000 (initial (u p) (u t) (u width)) 0 with
  | none=>false
  | some (s,v)=>s.flag.isNone && s.returned.isNone && s.frames.isEmpty &&
    s.data (weighted .catalogue)==enc (ws.map u) && s.data (weighted .output)==output &&
    s.data (weighted .width)==u width && s.data (aux .labels)==labels &&
    s.data (multiply (.inl .a))==u p && s.data (multiply (.inl .b))==u t &&
    s.data (multiply (.inr .output))==u (p*t) &&
    v==SemiprimeD1WeightedTuples.visits ws P
#eval [check 0 0 0,check 1 1 0,check 1 1 1,check 0 2 3,check 2 0 3,check 1 1 3,check 2 1 3]
