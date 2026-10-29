/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinishPrimitives
/-! # Actual consuming transfers and retained finite sign/loss tests
A transfer executes the real preserving copy and then drains its actual source.
Its real nested call and return are included in the closed byte clock.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishMoves
open SemiprimeD1StackRecoveryFinish SemiprimeD1StackRecoveryFinishState
open SemiprimeD1StackRecoveryFinishPrimitives SemiprimeD1StackProcedureTrace
/-- Real finite Boolean peek retains every physical word. -/
theorem peek_view (pc empty low high:Label) (s:Slot) (v:Values)
    (hc:program pc=.base (.peek (address s) empty low high)):
    Runs program 1 pc (data v) (SemiprimeD1StackBytecode.choose empty low high (v s).head?) (data v):=by
  apply one_base program _ _ _ _ _ hc
  · simp only [SemiprimeD1StackBytecode.execute,data_get]
  · rfl
/-- Real consuming-transfer source is its actual named live role. -/
theorem move_source (site:MoveSite):moveSource site=address (moveFrom site):=by cases site <;> rfl
/-- Real consuming-transfer target is its actual named live role. -/
theorem move_target (site:MoveSite):moveTarget site=address (moveTo site):=by cases site <;> rfl
/-- Every consuming transfer has distinct actual source and destination words. -/
theorem move_ne (site:MoveSite):moveFrom site≠moveTo site:=by cases site <;> decide
/-- Exact resulting bank of one actual source-consuming transfer. -/
def moved (v:Values) (site:MoveSite):Values:=
  Function.update (Function.update v (moveTo site) (v (moveFrom site)++v (moveTo site))) (moveFrom site) []
/-- Exact real move procedure before its actual return: copy, then complete physical source drain. -/
theorem move_trace (site:MoveSite) (v:Values) (hs:v (.aux .copyScratch)=[]):
    Runs program (6*(v (moveFrom site)).length+5) (.move site false) (data v)
      (.local .returning) (data (moved v site)):=by
  have h0:=copy_view (.move site) (.move site false) (.move site true) v rfl hs
  change Runs program (5*(v (moveFrom site)).length+4) (.move site false) (data v) (.move site true)
    (data (Function.update v (moveTo site) (v (moveFrom site)++v (moveTo site)))) at h0
  let after:=Function.update v (moveTo site) (v (moveFrom site)++v (moveTo site))
  have hc:program (.move site true)=.base (.pop (address (moveFrom site)) (.local .returning)
      (.move site true) (.move site true)):=by simp only [program,move_source]
  have h1:=drain_view (.move site true) (.local .returning) (moveFrom site) after hc
  have hv:after (moveFrom site)=v (moveFrom site):=Function.update_of_ne (move_ne site) _ _
  rw [hv] at h1
  have h:=join h0 h1
  change Runs program _ _ _ _ (data (moved v site)) at h
  convert h using 1
  omega
/-- One actual nested move call includes the real call/return, every copy cell and every source drain cell. -/
theorem move_call (site:MoveSite) (pc next:Label) (v:Values)
    (hc:program pc=.call (.move site false) next) (hs:v (.aux .copyScratch)=[]):
    Runs program (6*(v (moveFrom site)).length+7) pc (data v) next (data (moved v site)):=by
  have h:=returning_call pc (.move site false) next _ _ _ hc (move_trace site v hs)
  simpa only [Nat.add_assoc] using h
/-- Transfers into an actual empty word copy exactly the existing source bytes, then empty the source. -/
theorem moved_empty (v:Values) (site:MoveSite) (ht:v (moveTo site)=[]):
    moved v site=Function.update (Function.update v (moveTo site) (v (moveFrom site))) (moveFrom site) []:=by
  simp only [moved,ht,List.append_nil]
end RiemannGaussian.SemiprimeD1StackRecoveryFinishMoves
