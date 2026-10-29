import InitECandidate.Solver.Input.CurrentVerify.RunInputs
import InitECandidate.Solver.Input.CurrentVerify.GasFrame
import InitECandidate.Solver.Input.CallPrefixExecution

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- These are exactly the global cells used by the current verification
input contract. Block-hash and EVM globals may change independently. -/
def dataGlobals : List MlS := [ofString "scratch_ptr",ofString "frame_mem_ptr",ofString "heap_ptr",ofString "keccak_st",ofString "keccak_pad",ofString "mpt_hash_scratch",ofString "mpt_key_scratch",ofString "empty_trie_root",ofString "sha_st",ofString "sha_pad",ofString "u256_ws"]

theorem Data.with_globals {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (globals : HolFiniteMapExact MlS (ValueHOL 64))
    (kept : ∀ key∈dataGlobals,globals.lookup key=source.globals.lookup key) :
    Data input {source with globals:=globals} pointer si record gasWord boundary := by
  have arena : CurrentStartup.ArenaState {source with globals:=globals} :=
    ⟨(kept _ (by simp [dataGlobals])).trans data.arena.scratch,
      (kept _ (by simp [dataGlobals])).trans data.arena.frame,data.arena.domain,data.arena.code⟩
  have environment : CurrentKeccak.Hash.Environment {source with globals:=globals} 2701132160#64 2701132360#64 :=
    ⟨data.arena.code,data.keccak.domain,(kept _ (by simp [dataGlobals])).trans data.keccak.stateGlobal,
      (kept _ (by simp [dataGlobals])).trans data.keccak.padGlobal,
      data.keccak.stateArena,data.keccak.padArena,data.keccak.stateAligned,data.keccak.padAligned⟩
  obtain ⟨heap,cell,lower,upper,aligned⟩:=data.heap
  have nextHeap : NormalHeapEffects.AtLeast (boundary+32) {source with globals:=globals} :=
    ⟨heap,(kept _ (by simp [dataGlobals])).trans cell,lower,upper,aligned⟩
  exact data.of_interval arena data.little environment (kept _ (by simp [dataGlobals]) |>.trans data.mptHash) (kept _ (by simp [dataGlobals]) |>.trans data.mptKey) (kept _ (by simp [dataGlobals]) |>.trans data.mptEmpty)
    (kept _ (by simp [dataGlobals]) |>.trans data.shaState) (kept _ (by simp [dataGlobals]) |>.trans data.shaPad) (kept _ (by simp [dataGlobals]) |>.trans data.u256) nextHeap data.siLocal
    (by intros; rfl)

/-- An observed normal assignment to an unrelated global preserves the
complete physical input contract and the original SI binding. -/
theorem Data.global_assign {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary) (key : MlS) (expression : ExpHOL 64)
    (unrelated : key∉dataGlobals)
    (normal : evaluateHOLFiniteState source (.assign .global key expression)=(none,target)) :
    Data input target pointer si record gasWord boundary := by
  rw [evaluateHOLFiniteState_assign] at normal
  split at normal
  · cases normal
  · split at normal
    · have endpoint:=congrArg Prod.snd normal
      dsimp only at endpoint
      rw [←endpoint]
      apply data.with_globals
      intro protectedKey member
      have different : key≠protectedKey := by intro equal; apply unrelated; rw [equal]; exact member
      simp [HolFiniteMapExact.update,FUPDATE,different]
    · cases normal

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.Data.with_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.Data.global_assign

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
