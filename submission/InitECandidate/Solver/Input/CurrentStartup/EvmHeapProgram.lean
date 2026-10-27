import InitECandidate.Solver.Input.CurrentStartup.Code
import InitECandidate.Solver.Input.CallPrefixKey

namespace InitECandidate.Solver.Input.CurrentStartup.EvmHeap
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

/-- Keep the actual mark/s lexical scopes and all33literal byte stores. -/
def actions : List CallPrefix.Action := (CallPrefix.cutAt 35 (Code.body .evm_init)).1
def tail : ProgHOL 64 := (CallPrefix.cutAt 35 (Code.body .evm_init)).2
def restActions : List CallPrefix.Action := actions.drop 1

def release : ProgHOL 64 := .call (some (none, none)) (Code.name .heap_release) [.var .local (ofString "mark")]
def afterRelease : ProgHOL 64 := match tail with | .seq _ rest => rest | _ => .skip

theorem source_shape : Code.body .evm_init = CallPrefix.program actions tail :=
  (CallPrefix.reconstructAt 35 (Code.body .evm_init)).symm

set_option maxRecDepth 100000 in
theorem head_shape : actions = .scoped (ofString "mark") .one (Code.name .heap_mark) [] :: restActions := by
  simp only [actions, restActions, CallPrefix.cutAt, Code.body, Code.entry, Code.declaration,
    GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Guest.Software.guestFn_evm_init,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none, List.drop_succ_cons, List.drop_zero, Code.name]

set_option maxRecDepth 100000 in
theorem tail_shape : tail = .seq release afterRelease := by
  simp only [tail, release, afterRelease, CallPrefix.cutAt, Code.body, Code.entry, Code.declaration,
    GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Guest.Software.guestFn_evm_init,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none, Code.name]

set_option maxRecDepth 100000 in
open scoped InitE.MetadataComputation InitE.NameComputation in
theorem actions_safe : actions.all (fun action => action.keeps (ofString "unused")) = true := by
  simp only [actions, restActions, CallPrefix.cutAt, Code.body, Code.entry, Code.declaration,
    GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL,
    Guest.Software.guestFn_evm_init, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_some, Option.map_none, List.drop_succ_cons, List.drop_zero]
  decide

set_option maxRecDepth 100000 in
open scoped InitE.MetadataComputation InitE.NameComputation in
theorem mark_kept : restActions.all (fun action => action.keeps (ofString "mark")) = true := by
  simp only [actions, restActions, CallPrefix.cutAt, Code.body, Code.entry, Code.declaration,
    GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL,
    Guest.Software.guestFn_evm_init, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_some, Option.map_none, List.drop_succ_cons, List.drop_zero]
  decide

end InitECandidate.Solver.Input.CurrentStartup.EvmHeap

#print axioms InitECandidate.Solver.Input.CurrentStartup.EvmHeap.source_shape
#print axioms InitECandidate.Solver.Input.CurrentStartup.EvmHeap.head_shape
#print axioms InitECandidate.Solver.Input.CurrentStartup.EvmHeap.tail_shape
#print axioms InitECandidate.Solver.Input.CurrentStartup.EvmHeap.actions_safe
#print axioms InitECandidate.Solver.Input.CurrentStartup.EvmHeap.mark_kept
