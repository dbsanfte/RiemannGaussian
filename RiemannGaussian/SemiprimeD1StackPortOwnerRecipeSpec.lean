/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRecipe
/-! # Proof-only scalar invariants of actual endpoint recipe acquisition
No definition here supplies a runtime evaluator, prepared cache or key operand.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRecipeSpec
open SemiprimeD1StackPortOwnerRecipe
open SemiprimeD1StackUnaryDivmod (unary)
/-- Proof-only names of the nine acquired counters/half marker. -/
structure Counters where
  /-- Acquired first-axis unary counter. -/
  r:ℕ
  /-- Acquired second-axis unary counter. -/
  t:ℕ
  /-- Acquired original digit-count unary counter. -/
  digits:ℕ
  /-- Actual original edge half marker. -/
  half:Bool
  /-- Actual original signal tag counter. -/
  tag:ℕ
  /-- First physically parsed scalar coordinate. -/
  a:ℕ
  /-- Second physically parsed scalar coordinate. -/
  b:ℕ
  /-- Third physically parsed scalar coordinate. -/
  c:ℕ
  /-- Fourth physically parsed scalar coordinate. -/
  d:ℕ
/-- Literal actual input-word interpretation, not a runtime parser/evaluator. -/
def words (p:Counters) : Input→List Bool
  | .r=>unary p.r | .t=>unary p.t | .digits=>unary p.digits
  | .half=>if p.half then [true] else []
  | .tag=>unary p.tag | .a=>unary p.a | .b=>unary p.b | .c=>unary p.c | .d=>unary p.d
/-- Proof-only exact intermediate cache at each of the41 real preparation boundaries. -/
def cached (p:Counters) (stage:ℕ) : Register→List Bool :=
  let W:=p.r*p.t+1
  fun k=>match k with
  | .mode j=>unary j.val
  | .rt=>if 1 ≤ stage then unary (p.r*p.t) else []
  | .width=>if 3 ≤ stage then unary W else if 2 ≤ stage then unary (p.r*p.t) else []
  | .qa=>if 5 ≤ stage then unary (p.a/p.r) else []
  | .ma=>if 5 ≤ stage then unary (p.a%p.r) else []
  | .qb=>if 7 ≤ stage then unary (p.b/p.r) else []
  | .mb=>if 7 ≤ stage then unary (p.b%p.r) else []
  | .tc=>if 9 ≤ stage then unary (p.c+p.t) else if 8 ≤ stage then unary p.t else []
  | .rc=>if 11 ≤ stage then unary (p.c+p.r) else if 10 ≤ stage then unary p.r else []
  | .pbc=>if 12 ≤ stage then unary (p.t*p.c+p.b) else []
  | .aminus=>if 14 ≤ stage then unary (p.a-1) else if 13 ≤ stage then unary p.a else []
  | .bminus=>if 16 ≤ stage then unary (p.b-1) else if 15 ≤ stage then unary p.b else []
  | .dminus=>if 18 ≤ stage then unary (p.digits-1) else if 17 ≤ stage then unary p.digits else []
  | .bplus=>if 20 ≤ stage then unary (p.b+1) else if 19 ≤ stage then unary p.b else []
  | .slot10=>if 21 ≤ stage then unary ((p.b/p.r)*W+p.c) else []
  | .slot11=>if 22 ≤ stage then unary ((p.c+p.t)*W+p.d) else []
  | .slot12=>if 23 ≤ stage then unary (p.b*W+p.d) else []
  | .wd=>if 25 ≤ stage then unary (p.d+W) else if 24 ≤ stage then unary W else []
  | .slot13f=>if 26 ≤ stage then unary ((p.c+p.r)*W+p.d) else []
  | .slot13t=>if 27 ≤ stage then unary (p.a*W+p.d) else []
  | .slot14t=>if 28 ≤ stage then unary ((p.a/p.r)*W+p.b) else []
  | .slot14f=>if 29 ≤ stage then unary (2*W+p.b) else []
  | .wb=>if 31 ≤ stage then unary (p.b+W) else if 30 ≤ stage then unary W else []
  | .divInput=>if stage=4 then unary p.a else if stage=6 then unary p.b else []
  | .testLeft=>if stage=32 ∨ stage=33 ∨ stage=35 ∨ stage=36 then unary p.a
      else if stage=38 ∨ stage=39 then unary (p.b+1) else []
  | .testLimit=>if stage=33 then unary 2 else if stage=36 then unary (p.r*p.t)
      else if stage=39 then unary (p.digits-1) else []
  | .smallA=>if 34 ≤ stage then [decide (p.a<2)] else []
  | .ltArt=>if 37 ≤ stage then [decide (p.a<p.r*p.t)] else []
  | .ltNext=>if 40 ≤ stage then [decide (p.b+1<p.digits-1)] else []
  | .tagReader=>if 41 ≤ stage then unary p.tag else []
/-- All physical roles at one preparation boundary; real primitive work is empty. -/
def atStage (p:Counters) (stage:ℕ) : Stack→List Bool :=
  Sum.elim (words p) (Sum.elim (cached p stage) (fun _=>[]))
/-- Actual cache after the complete primitive preparation stage. -/
def prepared (p:Counters) : Stack→List Bool := atStage p 41
/-- Exact store during the physical literal mode-word construction. -/
def atMode (p:Counters) (count:ℕ) : Stack→List Bool :=
  Sum.elim (words p) (Sum.elim (fun k=>match k with
    | .mode j=>if j.val ≤ count then unary j.val else []
    | _=>[]) (fun _=>[]))
/-- Original signal's acquired scalar words and the actual original half marker. -/
def original {r t digits:ℕ} (e:SemiprimeMacroGraph.Edge r t digits) : Counters :=
  ⟨r,t,digits,e.2,(SemiprimeD1EdgeCatalogueEncoding.bit e.1 0).length,
    (SemiprimeD1EdgeCatalogueEncoding.bit e.1 1).length,
    (SemiprimeD1EdgeCatalogueEncoding.bit e.1 2).length,
    (SemiprimeD1EdgeCatalogueEncoding.bit e.1 3).length,
    (SemiprimeD1EdgeCatalogueEncoding.bit e.1 4).length⟩
/-- The exact key specified by the acquired counters, used only in output proofs. -/
def expected (p:Counters) : List Bool :=
  SemiprimeD1PortOwnerArithmeticSpec.routeKey
    (SemiprimeD1PortOwnerArithmeticSpec.route p.r p.t p.digits p.half p.tag p.a p.b p.c p.d)
/-- Repaired literal recipes license the actual full original endpoint family. -/
theorem expected_original {r t digits:ℕ} (hd:0<digits) (hc:digits≤r*t)
    (e:SemiprimeMacroGraph.Edge r t digits) : expected (original e)=
      SemiprimeD1PortOwnerKeys.key (SemiprimeD1PortOwnerKeys.endpoint hd hc e false) :=
  SemiprimeD1PortOwnerArithmeticSpec.original_recipe_key hd hc e
end RiemannGaussian.SemiprimeD1StackPortOwnerRecipeSpec
