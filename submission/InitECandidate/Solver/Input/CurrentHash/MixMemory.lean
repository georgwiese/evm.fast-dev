import InitECandidate.Solver.Input.CurrentHash.WordStoreMemory
import InitECandidate.Solver.Input.CurrentHash.Sha256Memory
import InitECandidate.Solver.Input.CurrentHash.PureGlobals
import InitECandidate.Solver.Input.CopyZeroMemoryNormal
import InitECandidate.Solver.Input.WordTripleEnvironment

namespace InitECandidate.Solver.Input.CurrentHash.MixMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def chunkExpression : ExpHOL 64 := .var .global (ofString "ssz_len_chunk")
def zeroArguments : List (ExpHOL 64) := [chunkExpression,.const 32#64]
def writeArguments : List (ExpHOL 64) := [chunkExpression,localVar "len"]
def pairArguments : List (ExpHOL 64) := [localVar "root",chunkExpression,localVar "out"]
def afterWrite : ProgHOL 64 := .seq (.call (some (none,none)) (Code.name .sha256_pair) pairArguments) (.return (.const 0#64))
def afterZero : ProgHOL 64 := .seq (.call (some (none,none)) (Code.name .st_le64) writeArguments) afterWrite

theorem source_shape : Code.body .mix_in_length = .seq (.call (some (none,none)) (Code.name .memzero) zeroArguments) afterZero := by
  simp only [Code.body,Code.entry,Code.declaration,Code.name,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_mix_in_length,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    zeroArguments,afterZero,writeArguments,afterWrite,pairArguments,chunkExpression,localVar]

structure Params (source : PanSemStateFiniteExact 64 Guest.HostMemory) (chunk out : BitVec 64) : Prop where
  installed : OriginalCode.Installed source.code
  domain : source.memaddrs=InitE.ordinaryDomain
  chunkCell : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk))
  output : source.locals.lookup (ofString "out")=some (.val (.word out))

theorem Params.after_call {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {chunk out : BitVec 64}
    (data : Params source chunk out) (function : MlS) (arguments : List (ExpHOL 64))
    (pure : GlobalEffects.Preserves (ofString "ssz_len_chunk") source.code (.call (some (none,none)) function arguments))
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) function arguments)=(none,post)) : Params post chunk out := by
  have fields := evaluation_fields source post _ none actual
  have installed : OriginalCode.Installed post.code := by rw [fields.2.2.2]; exact data.installed
  have frame := pure source rfl
  rw [actual] at frame
  exact ⟨installed,fields.1.trans data.domain,(congrArg Prod.snd frame).trans data.chunkCell,
    (CallNormal.ignored_lookup source post (ofString "out") function arguments actual).trans data.output⟩

theorem after_write_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (chunk out query : BitVec 64)
    (data : Params source chunk out) (outAway : CopyGeneral.Away out query 32) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source afterWrite=(some (.returned value),post)) : post.memory query=source.memory query := by
  have safe : LocalPrefix (ofString "out") (.call (some (none,none)) (Code.name .sha256_pair) pairArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,returned⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have read : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) (localVar "out")=some (.val (.word out)) := by
    simpa [evalHOLFinite,evalHOLExact,toExact,localVar] using data.output
  have hashed := Sha256Memory.call_output_memory source middle (localVar "root") chunkExpression (localVar "out") out query data.installed read
    (by intro offset inside; exact (outAway offset inside).2) normal
  have tail := MemoryAt.return_current middle (.const 0#64) query
  rw [returned] at tail
  exact tail.trans hashed

theorem after_zero_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (chunk out query : BitVec 64)
    (data : Params source chunk out) (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterZero=(some (.returned value),post)) : post.memory query=source.memory query := by
  have safe : LocalPrefix (ofString "out") (.call (some (none,none)) (Code.name .st_le64) writeArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have read : eval source chunkExpression=some (.val (.word chunk)) := by simpa [eval,evalHOLExact,toExact,chunkExpression] using data.chunkCell
  have written := WordStoreMemory.le64_call source middle chunkExpression (localVar "len") chunk query data.installed read
    (by intro offset inside; exact chunkAway offset (by omega)) normal
  have next := data.after_call _ _ (PureGlobals.le64_call _ source.code data.installed (some none) _) normal
  exact (after_write_memory middle post chunk out query next outAway value remaining).trans written

/-- Actual current length mixing preserves metadata outside the real32-byte
length chunk and output. Root/length contents and SHA input mapping are not
premises; both continuing helper returns come from this same execution. -/
theorem body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (chunk out query : BitVec 64)
    (data : Params source chunk out) (chunkArena : AllocatedBytes.Arena chunk 32) (aligned : chunk.toNat%8=0)
    (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source (Code.body .mix_in_length)=(some (.returned value),post)) :
    post.memory query=source.memory query := by
  rw [source_shape] at actual
  have safe : LocalPrefix (ofString "out") (.call (some (none,none)) (Code.name .memzero) zeroArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) zeroArguments=some (Zero.values chunk 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,zeroArguments,chunkExpression,data.chunkCell,Zero.values]
  have cleared := MemoryAt.zero_normal source middle zeroArguments chunk query 32 args data.installed data.domain chunkArena aligned (by decide)
    (by intro offset inside; exact (chunkAway offset inside).1) normal
  have next := data.after_call _ _ (MemoryGlobals.call .zero _ source.code data.installed (some none) _) normal
  exact (after_zero_memory middle post chunk out query next chunkAway outAway value remaining).trans cleared

theorem call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root len chunk out query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (chunkCell : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)))
    (chunkArena : AllocatedBytes.Arena chunk 32) (aligned : chunk.toNat%8=0)
    (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments =
      some [.val (.word root),.val (.word len),.val (.word out)])
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (Code.name .mix_in_length) arguments)=(none,post)) :
    post.memory query=source.memory query := by
  have entry : source.code.lookup (Code.name .mix_in_length)=some ([(ofString "root",.one),(ofString "len",.one),(ofString "out",.one)],Code.body .mix_in_length,.one) := by
    simpa only [Code.formals,Code.shape,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
      declToHOL,funDeclToHOL,Guest.Software.guestFn_mix_in_length,paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
      using Code.installed source.code installed .mix_in_length
  obtain ⟨callee,called,rootLocal,lenLocal,output⟩ := word_triple_environment source.code.lookup (Code.name .mix_in_length)
    (ofString "root") (ofString "len") (ofString "out") (Code.body .mix_in_length) .one root len out (by decide) (by decide) (by decide) entry
  exact MemoryAt.call_normal source post (Code.name .mix_in_length) arguments _ (Code.body .mix_in_length) callee .one query args called
    (fun target value evaluated => body_memory (callEntryStateHOLFinite source callee) target chunk out query ⟨installed,domain,chunkCell,output⟩
      chunkArena aligned chunkAway outAway value evaluated) actual

end InitECandidate.Solver.Input.CurrentHash.MixMemory

#print axioms InitECandidate.Solver.Input.CurrentHash.MixMemory.source_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.MixMemory.Params.after_call
#print axioms InitECandidate.Solver.Input.CurrentHash.MixMemory.after_write_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.MixMemory.after_zero_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.MixMemory.body_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.MixMemory.call_memory
