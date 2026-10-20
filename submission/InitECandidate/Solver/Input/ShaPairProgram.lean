import InitECandidate.Solver.Input.ShaGlobals
import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Input.ShaPair
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open ShaFixedCost
set_option maxHeartbeats 2000000

def global (name : String) : ExpHOL 64 := .var .global (ofString name)
def offset (name : String) (bytes : Nat) : ExpHOL 64 := .op .add [global name,.const (BitVec.ofNat 64 bytes)]
def copyArguments (name : String) (bytes : Nat) : List (ExpHOL 64) := [offset "sha_accel" bytes,localVar name,.const 32#64]
def blockArguments : List (ExpHOL 64) := [global "sha_st",offset "sha_accel" 32]

/-- Proof stages are matched to the literal original pair body below. -/
inductive Stage where | initialize | copyA | copyB | firstBlock | clear | padding | length | secondBlock | finish
  deriving DecidableEq

def Stage.program : Stage→ProgHOL 64
  | .initialize=>.call (some (none,none)) (ofString "sha256_state_init") [global "sha_st"]
  | .copyA=>.call (some (none,none)) (ofString "memcpy") (copyArguments "input_a" 32)
  | .copyB=>.call (some (none,none)) (ofString "memcpy") (copyArguments "input_b" 64)
  | .firstBlock | .secondBlock=>.call (some (none,none)) (ofString "sha256_block") blockArguments
  | .clear=>.call (some (none,none)) (ofString "memzero") [offset "sha_accel" 32,.const 64#64]
  | .padding=>.storeByte (offset "sha_accel" 32) (.const 128#64)
  | .length=>.call (some (none,none)) (ofString "st_be64") [offset "sha_accel" 88,.const 512#64]
  | .finish=>.call (some (none,none)) (ofString "sha256_finish") [global "sha_st",localVar "out"]

def Stage.price : Stage→Nat
  | .initialize=>1 | .copyA | .copyB=>5 | .firstBlock | .secondBlock=>9 | .clear | .length=>3 | .padding=>0 | .finish=>17

def program : List Stage→ProgHOL 64
  | []=>.return (.const 0#64)
  | stage::rest=>.seq stage.program (program rest)
def price : List Stage→Nat
  | []=>0
  | stage::rest=>stage.price+price rest

def stages : List Stage := [.initialize,.copyA,.copyB,.firstBlock,.clear,.padding,.length,.secondBlock,.finish]

theorem original_shape : pairBody=program stages := by
  simp only [pairBody,Guest.guestFn_sha256_pair,progToHOL,expToHOL,List.map_cons,List.map_nil,Option.map_none,
    program,stages,Stage.program,global,offset,copyArguments,blockArguments,localVar]

theorem total_price : price stages=52 := by decide

/-- Current original workspace globals and the two real caller inputs.
Memory contents and future execution outcomes remain unrestricted. -/
structure Ready (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b stp accel : BitVec 64) : Prop where
  installed : OriginalCode.Installed source.code
  domain : source.memaddrs=InitE.ordinaryDomain
  inputA : source.locals.lookup (ofString "input_a")=some (.val (.word a))
  inputB : source.locals.lookup (ofString "input_b")=some (.val (.word b))
  state : source.globals.lookup (ofString "sha_st")=some (.val (.word stp))
  accelerator : source.globals.lookup (ofString "sha_accel")=some (.val (.word accel))

theorem Stage.globals (stage : Stage) (key : MlS) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves key code stage.program := by
  cases stage <;> simp only [Stage.program]
  all_goals first
    | exact GlobalEffects.store_byte key code _ _
    | exact GlobalEffects.call_body key code (some none) (ofString "sha256_state_init") _ _ _ _ (initialize_code code installed) (initialize_globals key code)
    | exact GlobalEffects.call_body key code (some none) (ofString "memcpy") _ _ _ _ (CopyGeneral.original_code code installed) (Copy32.globals key code)
    | exact GlobalEffects.call_body key code (some none) (ofString "sha256_block") _ _ _ _ (block_code code installed) (block_globals key code installed)
    | exact GlobalEffects.call_body key code (some none) (ofString "memzero") _ _ _ _ (Zero.original_code code installed) (Zero.globals key code)
    | exact GlobalEffects.call_body key code (some none) (ofString "st_be64") _ _ _ _ (GasBudget.MemoryWriter.original_code .be64 code installed) (be64_globals key code installed)
    | exact GlobalEffects.call_body key code (some none) (ofString "sha256_finish") _ _ _ _ (finish_code code installed) (finish_globals key code installed)

private theorem ignored_locals (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (key function : MlS) (arguments : List (ExpHOL 64))
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) function arguments)=(none,post)) :
    post.locals.lookup key=source.locals.lookup key := by
  have safe : LocalPrefix key (.call (some (none,none)) function arguments) := .call none function arguments (by intro name impossible; cases impossible)
  have summary := safe.summary_full source
  unfold LocalSummary at summary
  rw [normal] at summary
  exact summary.1 rfl

theorem Stage.locals (stage : Stage) (key : MlS) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (normal : evaluateHOLFiniteState source stage.program=(none,post)) : post.locals.lookup key=source.locals.lookup key := by
  cases stage <;> simp only [Stage.program] at normal
  all_goals first
    | exact ignored_locals source post key _ _ normal
    | rw [evaluateHOLFiniteState_storeByte] at normal
      repeat' first | rfl | split at normal | cases normal | exact congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.locals.lookup key) (congrArg Prod.snd normal).symm

theorem Stage.ready (stage : Stage) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (a b stp accel : BitVec 64)
    (actual : Ready source a b stp accel) (normal : evaluateHOLFiniteState source stage.program=(none,post)) : Ready post a b stp accel := by
  have fields := evaluation_fields source post stage.program none normal
  have globals (key : MlS) : post.globals.lookup key=source.globals.lookup key := by
    have same := stage.globals key source.code actual.installed source rfl
    rw [normal] at same
    exact congrArg Prod.snd same
  exact ⟨fields.2.2.2.symm ▸ actual.installed,fields.1.trans actual.domain,
    (stage.locals _ source post normal).trans actual.inputA,(stage.locals _ source post normal).trans actual.inputB,
    (globals _).trans actual.state,(globals _).trans actual.accelerator⟩

end InitECandidate.Solver.Input.ShaPair

#print axioms InitECandidate.Solver.Input.ShaPair.original_shape
#print axioms InitECandidate.Solver.Input.ShaPair.total_price
#print axioms InitECandidate.Solver.Input.ShaPair.Stage.globals
#print axioms InitECandidate.Solver.Input.ShaPair.Stage.locals
#print axioms InitECandidate.Solver.Input.ShaPair.Stage.ready
