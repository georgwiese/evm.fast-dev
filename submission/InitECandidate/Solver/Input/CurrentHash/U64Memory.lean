import InitECandidate.Solver.Input.CurrentHash.Code
import InitECandidate.Solver.Input.CopyZeroMemoryNormal
import InitECandidate.Solver.Input.MemoryContinue
import InitECandidate.Solver.Input.WordPairEnvironment
import InitECandidate.Solver.Input.IgnoredCallLookup

namespace InitECandidate.Solver.Input.CurrentHash.U64Memory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body := Code.body .htr_u64_at
def zeroArguments : List (ExpHOL 64) := [localVar "out",.const 32#64]
def copyArguments : List (ExpHOL 64) := [localVar "out",localVar "p",.const 8#64]
def afterZero : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "memcpy") copyArguments) (.return (.const 0#64))

theorem source_shape : body = .seq (.call (some (none,none)) (ofString "memzero") zeroArguments) afterZero := by
  simp only [body,Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_htr_u64_at,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_none,zeroArguments,afterZero,copyArguments,localVar]

structure Params (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p out : BitVec 64) : Prop where
  installed : OriginalCode.Installed source.code
  domain : source.memaddrs = InitE.ordinaryDomain
  pointer : source.locals.lookup (ofString "p") = some (.val (.word p))
  output : source.locals.lookup (ofString "out") = some (.val (.word out))

theorem Params.after_call {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {p out : BitVec 64}
    (data : Params source p out) (function : MlS) (arguments : List (ExpHOL 64))
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) function arguments) = (none,post)) : Params post p out := by
  have fields := evaluation_fields source post _ none actual
  have code : OriginalCode.Installed post.code := by rw [fields.2.2.2]; exact data.installed
  have kept (key : MlS) := CallNormal.ignored_lookup source post key function arguments actual
  exact ⟨code,fields.1.trans data.domain,(kept _).trans data.pointer,(kept _).trans data.output⟩

theorem after_zero_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p out query : BitVec 64)
    (data : Params source p out) (inputArena : AllocatedBytes.Arena p 8) (outArena : AllocatedBytes.Arena out 32)
    (away : CopyGeneral.Away out query 32) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source afterZero = (some (.returned value),post)) : post.memory query = source.memory query := by
  have safe : LocalPrefix (ofString "p") (.call (some (none,none)) (ofString "memcpy") copyArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,returned⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) copyArguments =
      some (CopyGeneral.values out p 8) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,copyArguments,localVar,data.pointer,data.output,CopyGeneral.values]
  have copied := MemoryAt.copy_normal source middle copyArguments p out query 8 args data.installed data.domain inputArena
    (AllocatedBytes.Arena.weaken out 32 8 outArena (by decide)) (by intro offset inside; exact away offset (by omega)) normal
  have tail := MemoryAt.return_current middle (.const 0#64) query
  rw [returned] at tail
  exact tail.trans copied

/-- Current scalar-root zero/copy/return preserves every word outside its
32-byte output, on the same actual normal return. -/
theorem body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p out query : BitVec 64)
    (data : Params source p out) (inputArena : AllocatedBytes.Arena p 8) (outArena : AllocatedBytes.Arena out 32)
    (aligned : out.toNat%8=0) (away : CopyGeneral.Away out query 32) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source body = (some (.returned value),post)) : post.memory query = source.memory query := by
  rw [source_shape] at actual
  have safe : LocalPrefix (ofString "p") (.call (some (none,none)) (ofString "memzero") zeroArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) zeroArguments =
      some (Zero.values out 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,zeroArguments,localVar,data.output,Zero.values]
  have cleared := MemoryAt.zero_normal source middle zeroArguments out query 32 args data.installed data.domain outArena aligned (by decide)
    (by intro offset inside; exact (away offset inside).1) normal
  exact (after_zero_memory middle post p out query (data.after_call _ _ normal) inputArena outArena away value remaining).trans cleared

def values (p out : BitVec 64) : List (ValueHOL 64) := [.val (.word p),.val (.word out)]

theorem environment (code) (installed : OriginalCode.Installed code) (p out : BitVec 64) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64), lookupCodeHOLFinite code.lookup (Code.name .htr_u64_at) (values p out) = some (body,callee,.one) ∧
      callee.lookup (ofString "p") = some (.val (.word p)) ∧ callee.lookup (ofString "out") = some (.val (.word out)) := by
  have entry : code.lookup (Code.name .htr_u64_at) = some ([(ofString "p",.one),(ofString "out",.one)],body,.one) := by
    simpa only [Code.formals,Code.body,Code.shape,Code.entry,Code.declaration,body,GasBudget.OriginalCodeEnvironment.originalEntry,
      declToHOL,funDeclToHOL,Guest.Software.guestFn_htr_u64_at,paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
      using Code.installed code installed .htr_u64_at
  exact word_pair_environment code.lookup (Code.name .htr_u64_at) (ofString "p") (ofString "out") body .one p out (by decide) entry

theorem call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p out query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs = InitE.ordinaryDomain)
    (inputArena : AllocatedBytes.Arena p 8) (outArena : AllocatedBytes.Arena out 32)
    (aligned : out.toNat%8=0) (away : CopyGeneral.Away out query 32) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values p out))
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (Code.name .htr_u64_at) arguments) = (none,post)) :
    post.memory query = source.memory query := by
  obtain ⟨callee,called,pointer,output⟩ := environment source.code installed p out
  exact MemoryAt.call_normal source post (Code.name .htr_u64_at) arguments (values p out) body callee .one query args called
    (fun target value evaluated => body_memory (callEntryStateHOLFinite source callee) target p out query
      ⟨installed,domain,pointer,output⟩ inputArena outArena aligned away value evaluated) actual

end InitECandidate.Solver.Input.CurrentHash.U64Memory

#print axioms InitECandidate.Solver.Input.CurrentHash.U64Memory.source_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.U64Memory.Params.after_call
#print axioms InitECandidate.Solver.Input.CurrentHash.U64Memory.after_zero_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.U64Memory.body_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.U64Memory.environment
#print axioms InitECandidate.Solver.Input.CurrentHash.U64Memory.call_memory
