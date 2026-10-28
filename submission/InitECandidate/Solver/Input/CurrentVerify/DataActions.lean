import InitECandidate.Solver.Input.CurrentVerify.DataGlobals
import InitECandidate.Solver.Input.CurrentVerify.GasFrame
import InitECandidate.Solver.Input.CallPrefixExecution

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual lexical actions before the node database which keep the whole
physical verification input. Every helper's effects are checked on the
same reached callee execution. -/
inductive DataAction : CallPrefix.Action→Prop where
  | declare (name : MlS) (shape : ShapeHOL) (expression : ExpHOL 64) (different : name≠ofString "si") :
      DataAction (.declare name shape expression)
  | decision (program : ProgHOL 64) (pure : PureDecision program) : DataAction (.command program)
  | global (key : MlS) (expression : ExpHOL 64) (unrelated : key∉dataGlobals) :
      DataAction (.command (.assign .global key expression))
  | gas (name : MlS) (arguments : List (ExpHOL 64)) (different : name≠ofString "si") :
      DataAction (.scoped name .one (ofString "check_gas_limit") arguments)

theorem DataAction.reached {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} {action : CallPrefix.Action}
    (safe : DataAction action) (data : Data input source pointer si record gasWord boundary)
    (actual : CallPrefix.Reaches source action target) : Data input target pointer si record gasWord boundary := by
  cases safe with
  | declare name shape expression different=>
    cases actual with
    | declare name shape expression value read checked=>
      apply data.of_frame (post:=setVarHOLFinite name value source) rfl
      exact (by simpa [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different] using data.siLocal)
  | decision program pure=>
    cases actual with
    | command target command run=>
      have summary:=pure.summary source
      rw [run] at summary
      have same:=summary.1 rfl
      dsimp only at same
      rw [same]
      exact data
  | global key expression unrelated=>
    cases actual with
    | command target command run=>exact data.global_assign key expression unrelated run
  | gas name arguments different=>
    cases actual with
    | «scoped» name shape function arguments values actualBody callee actualShape value target args called funded run checked=>
      have sameBody:=LocalEffects.lookup_body source.code (ofString "check_gas_limit") GasLimit.formals GasLimit.body .one
        (GasLimit.original_code source.code data.arena.code) values actualBody callee actualShape called
      subst actualBody
      have frame:=GasLimit.readonly source.code data.arena.code (callEntryStateHOLFinite source callee) rfl
      rw [run] at frame
      apply data.of_frame (post:=setVarHOLFinite name value {target with locals:=source.locals}) frame
      simpa [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different] using data.siLocal

theorem Data.actions {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} {actions : List CallPrefix.Action}
    (data : Data input source pointer si record gasWord boundary)
    (safe : ∀ action∈actions,DataAction action) (actual : CallPrefix.Execution source actions target) :
    Data input target pointer si record gasWord boundary := by
  induction actual with
  | done source=>exact data
  | @step source middle target action rest first next ih=>
    exact ih (DataAction.reached (safe action (by simp)) data first) (fun child member=>safe child (List.mem_cons_of_mem _ member))

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.DataAction.reached
#print axioms InitECandidate.Solver.Input.CurrentVerify.Data.actions
