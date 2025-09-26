/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual
import Manual.Meta.Figure
import Lean.Elab.InfoTree.Types

open Verso Doc Elab
open Verso.Genre Manual
open Verso.ArgParse

open Lean Elab

namespace Manual

def Block.noVale : Block where
  name := `Manual.Block.noVale

@[block_extension Block.noVale]
def Block.noVale.descr : BlockDescr where
  traverse _ _ _ := pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ _ content => do
      pure {{<div class="no-vale">{{← content.mapM goB}}</div>}}

@[part_command Lean.Doc.Syntax.codeblock]
def markdown : PartCommand
  | `(Lean.Doc.Syntax.codeblock| ``` markdown | $txt ``` ) => do
     let some ast := MD4Lean.parse txt.getString
       | throwError "Failed to parse body of markdown code block"
     let mut currentHeaderLevels : List (Nat × Nat) := []
     for block in ast.blocks do
       currentHeaderLevels ← Markdown.addPartFromMarkdown block currentHeaderLevels
  | _ => Elab.throwUnsupportedSyntax

namespace debug
def mdexample := r#"
# header1
## header2-a
### header3-aa
### header3-ab
### header3-ac
## header2-b
### header3-ba
### header3-bb
## header2-c
### header3-ca
### header3-cb
"#

def debug : Verso.Doc.Elab.FinishedPart → String
  | .mk _ _ title _ _ subParts _ =>
       let partsStr : String := subParts.map debug |>.toList |> " ".intercalate
       s!"({title} {partsStr})"
  | .included name => s!"included {name}"


elab "#doctest" "(" genre:term ")" : command => open Lean Elab Command PartElabM DocElabM in do
  Concrete.findGenreCmd genre

  let g ← runTermElabM fun _ => Lean.Elab.Term.elabTerm genre (some (.const ``Doc.Genre []))

  let some ast := MD4Lean.parse mdexample
    | panic! "unit test failure"

  let ((), _dst, pst) ← liftTermElabM <| PartElabM.run genre g {} (.init (.node .none nullKind #[])) <| do
    let mut currentHeaderLevels : List (Nat × Nat) := []
    for block in ast.blocks do
      IO.println currentHeaderLevels
      currentHeaderLevels ← Markdown.addPartFromMarkdown block currentHeaderLevels
    closePartsUntil 0 0

  IO.println (repr <| pst.partContext.priorParts.map debug)


#doctest (Manual)

end debug
