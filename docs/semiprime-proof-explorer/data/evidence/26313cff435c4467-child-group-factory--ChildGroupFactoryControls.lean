import RiemannGaussian
import RiemannGaussian.SemiprimeD1StackChildGroupFactory
import RiemannGaussian.SemiprimeD1StackSourceEnvironmentEncoding
import RiemannGaussian.SemiprimeD1StackPacketInventoryEncoding
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace ChildGroupFactoryControls
open RiemannGaussian SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)
def keys:List Stack:=roles
def index:Stack→Nat
  | .inl (.inl .left)=>0
  | .inl (.inl .right)=>1
  | .inl (.inl .scratch)=>2
  | .inl (.inl .output)=>3
  | .inl (.inr .query)=>4
  | .inl (.inr .reader)=>5
  | .inl (.inr .fieldScratch)=>6
  | .inl (.inr .valid)=>7
  | .inl (.inr .copyScratch)=>8
  | .inl (.inr .discard)=>9
  | .inl (.inr .output)=>10
  | .inr (.inl (.inl (.inl .left)))=>11
  | .inr (.inl (.inl (.inl .right)))=>12
  | .inr (.inl (.inl (.inl .scratch)))=>13
  | .inr (.inl (.inl (.inl .output)))=>14
  | .inr (.inl (.inl (.inr .query)))=>15
  | .inr (.inl (.inl (.inr .reader)))=>16
  | .inr (.inl (.inl (.inr .fieldScratch)))=>17
  | .inr (.inl (.inl (.inr .valid)))=>18
  | .inr (.inl (.inl (.inr .copyScratch)))=>19
  | .inr (.inl (.inl (.inr .discard)))=>20
  | .inr (.inl (.inl (.inr .output)))=>21
  | .inr (.inl (.inr .key))=>22
  | .inr (.inl (.inr .catalogue))=>23
  | .inr (.inl (.inr .keyReader))=>24
  | .inr (.inl (.inr .leftBytes))=>25
  | .inr (.inl (.inr .leftHistory))=>26
  | .inr (.inl (.inr .rightHistory))=>27
  | .inr (.inl (.inr .leftOutput))=>28
  | .inr (.inl (.inr .rightOutput))=>29
  | .inr (.inr (.inl .left))=>30
  | .inr (.inr (.inl .right))=>31
  | .inr (.inr (.inl .scratch))=>32
  | .inr (.inr (.inl .output))=>33
  | .inr (.inr (.inr (.inl (.inl .input))))=>34
  | .inr (.inr (.inr (.inl (.inl .scratch))))=>35
  | .inr (.inr (.inr (.inl (.inl .output))))=>36
  | .inr (.inr (.inr (.inl (.inr ()))))=>37
  | .inr (.inr (.inr (.inr (.inl .bank))))=>38
  | .inr (.inr (.inr (.inr (.inl .reader))))=>39
  | .inr (.inr (.inr (.inr (.inl .word))))=>40
  | .inr (.inr (.inr (.inr (.inl .fieldScratch))))=>41
  | .inr (.inr (.inr (.inr (.inl .valid))))=>42
  | .inr (.inr (.inr (.inr (.inl .copyScratch))))=>43
  | .inr (.inr (.inr (.inr (.inl .digits))))=>44
  | .inr (.inr (.inr (.inr (.inl .unaryScratch))))=>45
  | .inr (.inr (.inr (.inr (.inl .unary))))=>46
  | .inr (.inr (.inr (.inr (.inl .logScratch))))=>47
  | .inr (.inr (.inr (.inr (.inl .history))))=>48
  | .inr (.inr (.inr (.inr (.inl .output))))=>49
  | .inr (.inr (.inr (.inr (.inr .environment))))=>50
  | .inr (.inr (.inr (.inr (.inr .catalogue))))=>51
  | .inr (.inr (.inr (.inr (.inr .owners))))=>52
  | .inr (.inr (.inr (.inr (.inr .factors))))=>53
  | .inr (.inr (.inr (.inr (.inr .occurrences))))=>54
  | .inr (.inr (.inr (.inr (.inr .placements))))=>55
  | .inr (.inr (.inr (.inr (.inr .packets))))=>56
  | .inr (.inr (.inr (.inr (.inr .colourIndex))))=>57
  | .inr (.inr (.inr (.inr (.inr .group))))=>58
  | .inr (.inr (.inr (.inr (.inr .oldAxes))))=>59
  | .inr (.inr (.inr (.inr (.inr .oldPrecision))))=>60
  | .inr (.inr (.inr (.inr (.inr .jetAxis))))=>61
  | .inr (.inr (.inr (.inr (.inr .newPrecision))))=>62
  | .inr (.inr (.inr (.inr (.inr .activation))))=>63
  | .inr (.inr (.inr (.inr (.inr .activationMap))))=>64
  | .inr (.inr (.inr (.inr (.inr .endpoints))))=>65
  | .inr (.inr (.inr (.inr (.inr .oldEndpoints))))=>66
  | .inr (.inr (.inr (.inr (.inr .buckets))))=>67
  | .inr (.inr (.inr (.inr (.inr .leftPorts))))=>68
  | .inr (.inr (.inr (.inr (.inr .orders))))=>69
  | .inr (.inr (.inr (.inr (.inr .output))))=>70
  | .inr (.inr (.inr (.inr (.inr .vertexTodo))))=>71
  | .inr (.inr (.inr (.inr (.inr .vertexKey))))=>72
  | .inr (.inr (.inr (.inr (.inr .selectedID))))=>73
  | .inr (.inr (.inr (.inr (.inr .jointKey))))=>74
  | .inr (.inr (.inr (.inr (.inr .pairReader))))=>75
  | .inr (.inr (.inr (.inr (.inr .placementReader))))=>76
  | .inr (.inr (.inr (.inr (.inr .packetReader))))=>77
  | .inr (.inr (.inr (.inr (.inr .endpointReader))))=>78
  | .inr (.inr (.inr (.inr (.inr .oldReader))))=>79
  | .inr (.inr (.inr (.inr (.inr .childReader))))=>80
  | .inr (.inr (.inr (.inr (.inr .outerReader))))=>81
  | .inr (.inr (.inr (.inr (.inr .ownerKey))))=>82
  | .inr (.inr (.inr (.inr (.inr .factorKey))))=>83
  | .inr (.inr (.inr (.inr (.inr .sourceKey))))=>84
  | .inr (.inr (.inr (.inr (.inr .paddingKey))))=>85
  | .inr (.inr (.inr (.inr (.inr .packetKey))))=>86
  | .inr (.inr (.inr (.inr (.inr .slotWord))))=>87
  | .inr (.inr (.inr (.inr (.inr .edgeWord))))=>88
  | .inr (.inr (.inr (.inr (.inr .sideWord))))=>89
  | .inr (.inr (.inr (.inr (.inr .validWord))))=>90
  | .inr (.inr (.inr (.inr (.inr .colourReader))))=>91
  | .inr (.inr (.inr (.inr (.inr .colourCursor))))=>92
  | .inr (.inr (.inr (.inr (.inr .colourWord))))=>93
  | .inr (.inr (.inr (.inr (.inr .activationHistory))))=>94
  | .inr (.inr (.inr (.inr (.inr .endpointHistory))))=>95
  | .inr (.inr (.inr (.inr (.inr .oldHistory))))=>96
  | .inr (.inr (.inr (.inr (.inr .bucketHistory))))=>97
  | .inr (.inr (.inr (.inr (.inr .factorHistory))))=>98
  | .inr (.inr (.inr (.inr (.inr .portHistory))))=>99
  | .inr (.inr (.inr (.inr (.inr .orderHistory))))=>100
  | .inr (.inr (.inr (.inr (.inr .vertexHistory))))=>101
  | .inr (.inr (.inr (.inr (.inr .tagWord))))=>102
  | .inr (.inr (.inr (.inr (.inr .candidateTag))))=>103
  | .inr (.inr (.inr (.inr (.inr .localPosition))))=>104
  | .inr (.inr (.inr (.inr (.inr .globalPosition))))=>105
  | .inr (.inr (.inr (.inr (.inr .answerPosition))))=>106
  | .inr (.inr (.inr (.inr (.inr .frameBuffer))))=>107
  | .inr (.inr (.inr (.inr (.inr .rowBuffer))))=>108
  | .inr (.inr (.inr (.inr (.inr .copyScratch))))=>109
  | .inr (.inr (.inr (.inr (.inr .sentinelScratch))))=>110
  | .inr (.inr (.inr (.inr (.inr .flagScratch))))=>111
  | .inr (.inr (.inr (.inr (.inr .success))))=>112
  | .inr (.inr (.inr (.inr (.inr .orderBank))))=>113
  | .inr (.inr (.inr (.inr (.inr .portBank))))=>114
theorem index_keys:∀k:Stack,keys[index k]?=some k:=by
  intro k
  rcases k with k|k|k|k|k|k
  · rcases k with k|k <;> cases k <;> rfl
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
  · cases k <;> rfl
def snapshot (d:Stack→List Bool):Stack→List Bool:=
  let values:=(keys.map d).toArray
  fun k=>(values[index k]?).getD []
theorem snapshot_eq (d:Stack→List Bool):snapshot d=d:=by
  funext k
  simp only [snapshot,List.getElem?_toArray,List.getElem?_map,index_keys,Option.map_some,Option.getD_some]
def drive:Nat→C.State Stack Label→Nat→Option (C.State Stack Label×Nat)
  | 0,_,_=>none
  | fuel+1,s,n=>match s.pc with
    | none=>some (s,n)
    | some _=>match SemiprimeD1StackCalls.step program s with
      | none=>none
      | some q=>
        let values:=(keys.map q.data).toArray
        let fresh:Stack→List Bool:=fun k=>(values[index k]?).getD []
        drive fuel {q with data:=fresh} (n+1)
def number (n:Nat):List Bool:=(SemiprimeSourceHistogramPortKeys.encodeKey n).bits
def flag (colour group:Nat):Bool:=decide (colour=group)
def endpoint (v:Nat) (packet slot edge:List Bool) (side:Bool):List Bool:=
  frame (number v) (frame packet (frame slot (frame edge (frame [side] []))))
def oldpoint (v:Nat) (edge:List Bool) (side:Bool):List Bool:=frame (number v) (frame edge (frame [side] []))
structure End where
  vertex:Nat
  packet:List Bool
  edge:List Bool
  side:Bool
  deriving DecidableEq
def endpointAt (e:End) (j:Nat):List Bool:=frame (number e.vertex)
  (frame e.packet (frame [true] (frame e.edge (frame [e.side] (frame (number j) [])))))
def portTape (ns:List Nat):List Bool:=vectorBits (ns.map (fun n=>List.replicate n true))
def outer:List Label:=[entry,abort]
def outerEq (ls:List Label):Bool:=match ls with
  | [.local 0 0,.local p o]=>p.val==15 && o.val==14
  | _=>false
-- Outer return equality is observed by its own fixed complete pair of labels.
def outerExact (ls:List Label):Bool:=match ls with
  | [a,b]=>match a,b with
    | .local p o,.local q r=>p.val==0 && o.val==0 && q.val==15 && r.val==14
    | _,_=>false
  | _=>false
def check (label:String) (n F:Nat) (owners:List Nat) (colours:List Nat)
    (packetFor:List (List Bool)) (packets:List (List Bool)) (g:Nat) (bad:Bool:=false):IO Nat:=do
  let env:=SemiprimeD1StackSourceEnvironmentEncoding.dictionary ((colours.map number).reverse)
  let catalogue:=SemiprimeD1StackOwnerLookup.records [(number 0,frame [] []),(number 1,frame [true] [])] []
  let pairRows:=owners.map (fun v=>(number v,number n))
  let occurrence:=SemiprimeD1StackOwnerLookup.records pairRows []
  let placements:=owners.zipIdx |>.map (fun (_,j)=>
    let packet:=(packetFor[j]?).getD []
    SemiprimeD1StackPacketInventoryEncoding.placementBytes ⟨[],[],packet,[true],number (j+1),true⟩)
  let placement:=if bad then vectorBits [] else vectorBits placements
  let inputs:Inputs:={environment:=env,catalogue:=catalogue,owners:=List.replicate n true, factors:=List.replicate F true,occurrences:=occurrence,placements:=placement,packets:=vectorBits packets, colourIndex:=[],group:=number g,oldAxes:=vectorBits [[true,true]],oldPrecision:=[false,true], jetAxis:=[true,true,true],newPrecision:=[true,false,true]}
  let allOld:=owners.zipIdx |>.flatMap (fun (v,j)=>
    [End.mk v ((packetFor[j]?).getD []) (number (j+1)) true,
     End.mk n ((packetFor[j]?).getD []) (number (j+1)) false])
  let acts:=colours.map (fun c=>flag c g)
  let selected:=allOld.filter (fun e=>(acts[e.vertex]?).getD false)
  let grouped:=packets.map (fun packet=>selected.filter (fun e=>e.packet==packet))
  let flat:=grouped.flatten
  let childPorts:=(List.range (n+F)).map (fun v=>portTape ((flat.zipIdx.filter (fun (e,_)=>e.vertex==v)).map Prod.snd))
  let orderTapes:=(List.range (n+F)).map (fun v=>
    let old:=allOld.filter (fun e=>e.vertex==v)
    let child:=flat.filter (fun e=>e.vertex==v)
    portTape (old.map (fun e=>child.idxOf e)))
  let rec bucketBytes (groups:List (List End)) (packets:List (List Bool)) (start:Nat):List (List Bool):=
    match groups,packets with
    | group::groups,packet::packets=>
      let payload:=vectorBits (group.zipIdx.map (fun (e,j)=>endpointAt e (start+j)))
      frame packet (frame payload (frame (portTape (List.range group.length |>.map (fun j=>start+j))) []))::
        bucketBytes groups packets (start+group.length)
    | _,_=>[]
  let oldBytes:=vectorBits (allOld.map (fun e=>oldpoint e.vertex e.edge e.side))
  let endpointBytes:=vectorBits (selected.map (fun e=>endpoint e.vertex e.packet [true] e.edge e.side))
  let bucketTape:=vectorBits (bucketBytes grouped packets 0)
  let leftTape:=vectorBits childPorts
  let ordersTape:=vectorBits orderTapes
  let finalTape:=frame acts (frame endpointBytes (frame bucketTape (frame leftTape (frame ordersTape (frame oldBytes [])))))
  let wanted:=fun k=>match k with
    | .inr (.inr (.inr (.inr (.inr .activation))))=>if bad then [] else acts
    | .inr (.inr (.inr (.inr (.inr .activationMap))))=>if bad then [] else
        SemiprimeD1StackOwnerLookup.records ((acts.zipIdx.map (fun (b,j)=>(number j,[b]))).reverse) []
    | .inr (.inr (.inr (.inr (.inr .endpoints))))=>if bad then [] else endpointBytes
    | .inr (.inr (.inr (.inr (.inr .oldEndpoints))))=>if bad then [] else oldBytes
    | .inr (.inr (.inr (.inr (.inr .buckets))))=>if bad then [] else bucketTape
    | .inr (.inr (.inr (.inr (.inr .leftPorts))))=>if bad then [] else leftTape
    | .inr (.inr (.inr (.inr (.inr .orders))))=>if bad then [] else ordersTape
    | .inr (.inr (.inr (.inr (.inr .output))))=>if bad then [] else finalTape
    | .inr (.inr (.inr (.inr (.inr .success))))=>[!bad]
    | k=>input inputs k
  let before:C.State Stack Label:=⟨some entry,some true,some abort,input inputs,outer⟩
  let some (out,steps):=drive 1000000 before 0 | throw (IO.userError s!"factory did not halt: {label}")
  let mismatches:=keys.filter (fun k=>out.data k != wanted k)
  unless mismatches.isEmpty && out.flag.isNone && out.returned.isNone && outerExact out.frames do
    for k in mismatches do IO.println s!"MISMATCH role={index k} got={out.data k} expected={wanted k}"
    throw (IO.userError s!"factory mismatch: {label}; steps={steps}; roles={mismatches.map index}")
  IO.println s!"CHILD_GROUP_FACTORY case={label} steps={steps} all115=true oldVertices={n+F} originalOccurrences={owners.length} packets={packets.length} success={!bad}"
  return steps
def run:IO Unit:=do
  let mut n:=0
  n:=n+(←check "empty" 0 0 [] [] [] [] 0)
  n:=n+(←check "isolated" 1 1 [] [0,1] [] [] 0)
  n:=n+(←check "both" 1 1 [0] [0,0] [[]] [[]] 0)
  n:=n+(←check "owner-only" 1 1 [0] [0,1] [[]] [[]] 0)
  n:=n+(←check "none-empty-packet" 1 1 [0] [0,1] [[]] [[]] 2)
  n:=n+(←check "literal-packet-order" 1 1 [0,0] [0,0] [[],[false]] [[false],[]] 0)
  n:=n+(←check "duplicate-packets" 1 1 [0] [0,0] [[]] [[],[]] 0)
  n:=n+(←check "paired-eof-reject" 1 1 [0] [0,0] [[]] [[]] 0 true)
  IO.println s!"CHILD_GROUP_FACTORY cases=8 actual_steps={n} all115=true isolated=true owner_before_factor=true empty_buckets=true literal_rawpacket=true real_unary_ports=true derived_nonidentity_order=true duplicate_packets=true headers_generic=true flags_and_two_outer_returns=true"
#eval run
end ChildGroupFactoryControls
open Lean Elab Command
run_cmd do
  let env←getEnv
  let mut checked:Nat:=0
  for (name,_) in env.constants.toList do
    unless (`ChildGroupFactoryControls).isPrefixOf name do continue
    for ax in (←Lean.collectAxioms name) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "observer axiom {name}: {ax}"
    checked:=checked+1
  logInfo m!"CHILD_GROUP_FACTORY_OBSERVER_STD3 {checked}"
