/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PortOwnerEndpointEncoding
/-! # Literal arithmetic-side endpoint recipes
This is a PROOF specification of the fixed finite routing recipes. It is not
an executable endpoint supplier; physical copies/products/divmod implement it.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000
namespace RiemannGaussian.SemiprimeD1PortOwnerArithmeticSpec
open SemiprimeD1EdgeCatalogueEncoding SemiprimeD1VertexCatalogueModes
open SemiprimeMacroGraph
/-- Actual slot counter and five descriptor counters returned by one recipe. -/
abbrev Routed := ℕ×Record
/-- The eight original equality-signal tags select literal scalar recipes.
All operands here specify physically acquired unary counters. -/
def route (r t digits:ℕ) (half:Bool) (tag a b c d:ℕ) : Routed :=
  let W:=r*t+1
  if tag=10 then
    if half then ((b/r)*W+c,fields .first a (b%r) 0 0)
    else (c,fields .input a b 0 0)
  else if tag=11 then
    if half then (d,fields .scale a b c 0)
    else ((t+c)*W+d,fields .first a b 0 0)
  else if tag=12 then
    if half then (b*W+d,fields .second a c 0 0)
    else (W+d,fields .scale a b c 0)
  else if tag=13 then
    if half then
      if a<2 then (a*W+d,fields .product (b+t*c) 0 0 0)
      else (d,fields .carry (b+t*c) 0 0 0)
    else ((r+c)*W+d,fields .second a b 0 0)
  else if tag=14 then
    if half then ((a/r)*W+b,fields .first 2 (a%r) 0 0)
    else (2*W+b,fields .product a 0 0 0)
  else if tag=15 then
    if half then
      if a<r*t then (W+b,fields .carry a 0 0 0)
      else (b,fields .carryTerminal 0 0 0 0)
    else if a=0 then (b,fields .carryInitial 0 0 0 0)
      else (2*W+b,fields .carry (a-1) 0 0 0)
  else if tag=16 then
    if half then
      if b=0 then
        if digits=1 then (0,fields .inputCheck a 0 0 0)
        else (0,fields .orGate a 0 0 0)
      else (1,fields .orGate a (b-1) 0 0)
    else (W,fields .input a b 0 0)
  else if tag=17 then
    if half then
      if b+1<digits-1 then (0,fields .orGate a (b+1) 0 0)
      else (0,fields .inputCheck a 0 0 0)
    else (2,fields .orGate a b 0 0)
  else (0,fields .carryInitial 0 0 0 0)
/-- The exact six framed fields and compact sentinel required by the router. -/
def routeKey (p:Routed) : List Bool :=
  SemiprimeSourceHistogramKeyBits.frame (List.replicate p.1 true) (record p.2 [true])
/-- The equality signal fields already physically present in an Edge13 record. -/
def originalRecipe {r t digits:ℕ} (e:Edge r t digits) : Routed :=
  route r t digits e.2 ((bit e.1 0).length) ((bit e.1 1).length)
    ((bit e.1 2).length) ((bit e.1 3).length) ((bit e.1 4).length)
/-- Proof-side scalar projection of the literal ordered local-slot code. -/
def slotValue {r t digits:ℕ} : (v:Vertex r t digits)→LocalSlot v→ℕ
  | .input _ _,.inl bit=>bit.val
  | .input _ _,.inr _=>r*t+1
  | .first _ _,.inl p=>p.2.val+(r*t+1)*p.1.val
  | .first _ _,.inr p=>t*(r*t+1)+(p.2.val+(r*t+1)*p.1.val)
  | .scale _ _ _,.inl bit=>bit.val
  | .scale _ _ _,.inr bit=>(r*t+1)+bit.val
  | .second _ _,.inl p=>p.2.val+(r*t+1)*p.1.val
  | .second _ _,.inr p=>r*(r*t+1)+(p.2.val+(r*t+1)*p.1.val)
  | .product _,.inl p=>p.2.val+(r*t+1)*p.1.val
  | .product _,.inr bit=>2*(r*t+1)+bit.val
  | .carryInitial,bit=>bit.val
  | .carry _,.inl p=>p.2.val+(r*t+1)*p.1.val
  | .carry _,.inr bit=>2*(r*t+1)+bit.val
  | .carryTerminal,bit=>bit.val
  | .orGate _ _,bit=>bit.val
  | .inputCheck _,bit=>bit.val
/-- This avoids simplifying an equivalence inside an unreduced dependent match. -/
theorem slot_value {r t digits:ℕ} (v:Vertex r t digits) (slot:LocalSlot v) :
    ((localSlotFinEquiv v) slot).val=slotValue v slot := by
  cases v <;> cases slot <;> rfl
/-- Match the structured pair as a whole to preserve dependent simplification. -/
def portValue {r t digits:ℕ} : ((v:Vertex r t digits)×LocalSlot v)→ℕ
  | ⟨v,slot⟩=>slotValue v slot
/-- Reduce the actual arithmetic side before unfolding dependent slot equivalences. -/
theorem arithmetic_key {r t digits:ℕ} (hd:0<digits) (hc:digits≤r*t)
    (e:Edge r t digits) :
    SemiprimeD1PortOwnerKeys.key (SemiprimeD1PortOwnerKeys.endpoint hd hc e false)=
      SemiprimeSourceHistogramKeyBits.frame
        (SemiprimeD1StackUnaryDivmod.unary
          (portValue (structuredPort hc (bitEndpoint hd e))))
        (record (vertex (.inl (structuredPort hc (bitEndpoint hd e)).1)) [true]) := by
  change SemiprimeSourceHistogramKeyBits.frame _ _=_
  congr 2
  exact slot_value _ _
local macro "route_simp" : tactic => `(tactic|
  (simp_all only [bitEndpoint,endpoint,producer,consumer,flagEndpoint,flagProducer,flagConsumer]
   simp_all [originalRecipe,route,routeKey,bit,fields,code,bitEndpoint,
    structuredPort,endpoint,producer,consumer,slotValue,portValue,vertex,arithmetic,
    inputIndex,outputIndex,SemiprimeD1VertexCatalogueEncoding.transformCode,
    finProdFinEquiv,SemiprimeD1StackUnaryDivmod.unary,Equiv.trans_apply,Equiv.coe_fn_mk,
    flagEndpoint,flagProducer,flagConsumer,
    Nat.mul_comm,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,Nat.mul_add,Nat.add_mul]))
/-- All actual original arithmetic endpoint keys obey these literal recipes.
No arbitrary finite-fibre ordering enters the local slot. -/
theorem original_recipe_key {r t digits:ℕ} (hd:0<digits) (hc:digits≤r*t)
    (e:Edge r t digits) :
    routeKey (originalRecipe e)=SemiprimeD1PortOwnerKeys.key
      (SemiprimeD1PortOwnerKeys.endpoint hd hc e false) := by
  have hrt:0<r*t:=lt_of_lt_of_le hd hc
  rw [arithmetic_key]
  rcases e with ⟨signal,half⟩
  rcases signal with ⟨w,b⟩|flag
  · cases w with
    | input side i=>cases half <;> route_simp
    | first tr j k=>cases half <;> route_simp
    | twiddle tr j k=>cases half <;> route_simp
    | second tr k j=>
      cases tr with
      | inl side=>fin_cases side <;> cases half <;> route_simp
      | inr u=>cases u;cases half <;> route_simp
    | product i=>cases half <;> route_simp
    | carry i=>
      by_cases hz:i.val=0
      · have hi:i=0:=Fin.ext hz
        subst i
        cases half <;> route_simp
      · by_cases hl:i.val<r*t <;> cases half <;> route_simp
  · cases flag with
    | digit side i=>
      by_cases hz:i.val=0 <;> by_cases hone:digits=1 <;> cases half <;> route_simp
    | orOut side i=>
      by_cases hl:i.val+1<digits-1 <;> cases half <;> route_simp
end RiemannGaussian.SemiprimeD1PortOwnerArithmeticSpec
