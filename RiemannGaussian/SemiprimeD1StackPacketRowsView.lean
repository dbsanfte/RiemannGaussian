/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketRowsPrimitives
/-! # Complete nineteen-role physical row-reader banks between actual calls
These functions are proof notation for fixed physical tape banks. They never
inhabit runtime control, encode a row answer or supply a coordinate count.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketRowsView
open SemiprimeD1StackPacketRows
/-- All nineteen actual roles, including the reused lookup comparison/parser/logger work. -/
def view (key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer
    leftHistory rightHistory leftOutput rightOutput:List Bool) :Stack→List Bool :=
  Sum.elim (SemiprimeD1StackOwnerLookup.data queryWord reader leftWord rightWord flag valid buffer rightRow)
    (fun k=>match k with
      | .key=>key
      | .catalogue=>catalogue
      | .keyReader=>keyReader
      | .leftBytes=>leftBytes
      | .leftHistory=>leftHistory
      | .rightHistory=>rightHistory
      | .leftOutput=>leftOutput
      | .rightOutput=>rightOutput)
/-- One actual keyReader update retains every other physical word. -/
theorem update_keyReader (key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput word:List Bool) :
    Function.update (view key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput) (aux .keyReader) word=view key catalogue word leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One actual leftBytes update retains every other physical word. -/
theorem update_leftBytes (key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput word:List Bool) :
    Function.update (view key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput) (aux .leftBytes) word=view key catalogue keyReader word rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One actual rightRow update retains every other physical word. -/
theorem update_rightRow (key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput word:List Bool) :
    Function.update (view key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput) (rightBytes) word=view key catalogue keyReader leftBytes word queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One actual queryWord update retains every other physical word. -/
theorem update_queryWord (key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput word:List Bool) :
    Function.update (view key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput) (query) word=view key catalogue keyReader leftBytes rightRow word leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One actual leftWord update retains every other physical word. -/
theorem update_leftWord (key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput word:List Bool) :
    Function.update (view key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput) (colourWord false) word=view key catalogue keyReader leftBytes rightRow queryWord word rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One actual rightWord update retains every other physical word. -/
theorem update_rightWord (key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput word:List Bool) :
    Function.update (view key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput) (colourWord true) word=view key catalogue keyReader leftBytes rightRow queryWord leftWord word flag reader valid buffer leftHistory rightHistory leftOutput rightOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One actual flag update retains every other physical word. -/
theorem update_flag (key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput word:List Bool) :
    Function.update (view key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput) (success) word=view key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord word reader valid buffer leftHistory rightHistory leftOutput rightOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One actual reader update retains every other physical word. -/
theorem update_reader (key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput word:List Bool) :
    Function.update (view key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput) (lookupReader) word=view key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag word valid buffer leftHistory rightHistory leftOutput rightOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One actual valid update retains every other physical word. -/
theorem update_valid (key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput word:List Bool) :
    Function.update (view key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput) (parserValid) word=view key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader word buffer leftHistory rightHistory leftOutput rightOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One actual buffer update retains every other physical word. -/
theorem update_buffer (key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput word:List Bool) :
    Function.update (view key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput) (frameBuffer) word=view key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid word leftHistory rightHistory leftOutput rightOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One actual leftHistory update retains every other physical word. -/
theorem update_leftHistory (key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput word:List Bool) :
    Function.update (view key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput) (history false) word=view key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer word rightHistory leftOutput rightOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One actual rightHistory update retains every other physical word. -/
theorem update_rightHistory (key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput word:List Bool) :
    Function.update (view key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput) (history true) word=view key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory word leftOutput rightOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One actual leftOutput update retains every other physical word. -/
theorem update_leftOutput (key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput word:List Bool) :
    Function.update (view key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput) (output false) word=view key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory word rightOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One actual rightOutput update retains every other physical word. -/
theorem update_rightOutput (key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput word:List Bool) :
    Function.update (view key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput rightOutput) (output true) word=view key catalogue keyReader leftBytes rightRow queryWord leftWord rightWord flag reader valid buffer leftHistory rightHistory leftOutput word :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackPacketRowsView
