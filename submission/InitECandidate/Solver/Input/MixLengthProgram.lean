import InitECandidate.Solver.Input.ShaWorkspace
import InitECandidate.Solver.Input.LittleEndianEffects

namespace InitECandidate.Solver.Input.MixLength
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_mix_in_length with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "root",.one),(ofString "len",.one),(ofString "out",.one)]
def chunkExpression : ExpHOL 64 := .var .global (ofString "ssz_len_chunk")
def zeroArguments : List (ExpHOL 64) := [chunkExpression,.const 32#64]
def writeArguments : List (ExpHOL 64) := [chunkExpression,localVar "len"]
def pairArguments : List (ExpHOL 64) := [localVar "root",chunkExpression,localVar "out"]
def afterWriter : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "sha256_pair") pairArguments) (.return (.const 0#64))
def afterZero : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "st_le64") writeArguments) afterWriter

theorem body_shape : body=.seq (.call (some (none,none)) (ofString "memzero") zeroArguments) afterZero := by
  simp only [body,Guest.guestFn_mix_in_length,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    afterZero,afterWriter,zeroArguments,writeArguments,pairArguments,chunkExpression,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "mix_in_length")=some (formals,body,.one) := by
  have checked := OriginalCode.indexed code installed 176 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_mix_in_length) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn_mix_in_length,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

structure Ready (source : PanSemStateFiniteExact 64 Guest.HostMemory) (root out chunk stp accel : BitVec 64) : Prop where
  rootLocal : source.locals.lookup (ofString "root")=some (.val (.word root))
  output : source.locals.lookup (ofString "out")=some (.val (.word out))
  chunk : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk))
  workspace : ShaPair.Workspace source stp accel

/-- Retain the actual caller root/output and initialized chunk/workspace
through a real normal ignored helper call with checked global effects. -/
theorem Ready.after_call (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root out chunk stp accel : BitVec 64)
    (ready : Ready source root out chunk stp accel) (function : MlS) (arguments : List (ExpHOL 64))
    (pure : ∀ key,GlobalEffects.Preserves key source.code (.call (some (none,none)) function arguments))
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) function arguments)=(none,post)) : Ready post root out chunk stp accel := by
  have other (name : String) : post.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    have safe : LocalPrefix (ofString name) (.call (some (none,none)) function arguments) := .call none _ _ (by intro key impossible; cases impossible)
    have summary := safe.summary_full source
    unfold LocalSummary at summary
    rw [normal] at summary
    exact summary.1 rfl
  have frame := pure (ofString "ssz_len_chunk") source rfl
  rw [normal] at frame
  exact ⟨(other "root").trans ready.rootLocal,(other "out").trans ready.output,(congrArg Prod.snd frame).trans ready.chunk,
    ShaPair.Workspace.after source post stp accel ready.workspace _ none normal (pure (ofString "sha_st")) (pure (ofString "sha_accel"))⟩

/-- Original length mixing preserves every selected global on every outcome,
including its actual heap pointer and the SHA workspace pointers. -/
theorem globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code body := by
  rw [body_shape]
  unfold afterZero afterWriter
  exact GlobalEffects.sequence key code _ _
    (GlobalEffects.call_body key code (some none) (ofString "memzero") zeroArguments Zero.formals Zero.body .one (Zero.original_code code installed) (Zero.globals key code))
    (GlobalEffects.sequence key code _ _
      (GlobalEffects.call_body key code (some none) (ofString "st_le64") writeArguments MemoryWordCalls.formals MemoryWordCalls.le64Body .one (MemoryWordCalls.le64_code code installed) (MemoryWordCalls.le64_globals key code installed))
      (GlobalEffects.sequence key code _ _
        (GlobalEffects.call_body key code (some none) (ofString "sha256_pair") pairArguments ShaFixedCost.pairFormals ShaFixedCost.pairBody .one (ShaFixedCost.pair_code code installed) (ShaFixedCost.pair_globals key code installed))
        (GlobalEffects.returned key code _)))

end InitECandidate.Solver.Input.MixLength

#print axioms InitECandidate.Solver.Input.MixLength.body_shape
#print axioms InitECandidate.Solver.Input.MixLength.original_code
#print axioms InitECandidate.Solver.Input.MixLength.Ready.after_call
#print axioms InitECandidate.Solver.Input.MixLength.globals
