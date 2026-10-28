import InitECandidate.Solver.Input.CurrentHash.Code
import InitECandidate.Solver.Input.ByteOutputFrame
import InitECandidate.Solver.Input.WordPairLookup
import InitECandidate.Solver.Input.CopyAwaySubrange
import InitECandidate.Solver.Input.MemoryContinue
import InitECandidate.Solver.Input.IgnoredCallLookup

namespace InitECandidate.Solver.Input.CurrentHash.WordStoreMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem le32_supported : ByteOutputFrame.accepts (ofString "p") 4 (Code.body .st_le32)=true := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_st_le32,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  rfl

theorem le32_body (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64)
    (binding : source.locals.lookup (ofString "p")=some (.val (.word pointer))) (away : CopyGeneral.Away pointer query 4) :
    (evaluateHOLFiniteState source (Code.body .st_le32)).2.memory query=source.memory query :=
  (ByteOutputFrame.sound (ofString "p") 4 (Code.body .st_le32) le32_supported pointer query
    (by intro offset inside; exact (away offset inside).2) source binding).1

theorem call_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (routine : Code.Routine)
    (pointerExpression valueExpression : ExpHOL 64) (pointer query : BitVec 64)
    (entry : source.code.lookup (Code.name routine)=some ([(ofString "p",.one),(ofString "v",.one)],Code.body routine,.one))
    (read : eval source pointerExpression=some (.val (.word pointer)))
    (bodyFrame : ∀ current target : PanSemStateFiniteExact 64 Guest.HostMemory, current.code=source.code →
      current.locals.lookup (ofString "p")=some (.val (.word pointer)) → ∀ value,
      evaluateHOLFiniteState current (Code.body routine)=(some (.returned value),target) → target.memory query=current.memory query)
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (Code.name routine) [pointerExpression,valueExpression])=(none,post)) :
    post.memory query=source.memory query := by
  classical
  obtain ⟨positive,args,actualBody,callee,shape,target,value,arguments,called,bodyRun,checked,endpoint,fields⟩ :=
    CallNormal.ignored_data source post (Code.name routine) [pointerExpression,valueExpression] actual
  have argsEq : ∃ stored, args=[.val (.word pointer),stored] := by
    simp only [eval] at read
    change evalListHOLExact source.toExact [pointerExpression,valueExpression]=some args at arguments
    cases valueRead : evalHOLExact source.toExact valueExpression with
    | none => simp [evalListHOLExact,read,valueRead] at arguments
    | some stored => exact ⟨stored,Option.some.inj (by simpa [evalListHOLExact,read,valueRead] using arguments.symm)⟩
  obtain ⟨stored,rfl⟩ := argsEq
  obtain ⟨bodyEq,binding⟩ := checked_pair_left source.code.lookup (Code.name routine) (ofString "p") (ofString "v") (Code.body routine) .one
    pointer stored (by decide) entry actualBody callee shape called
  rw [bodyEq] at bodyRun
  have frame := bodyFrame (callEntryStateHOLFinite source callee) target rfl binding value bodyRun
  rw [endpoint]
  exact frame

theorem entry (routine : Code.Routine) (member : routine ∈ [.st_le32,.st_le64]) (code) (installed : OriginalCode.Installed code) :
    code.lookup (Code.name routine)=some ([(ofString "p",.one),(ofString "v",.one)],Code.body routine,.one) := by
  have checked := Code.installed code installed routine
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  all_goals simpa only [Code.formals,Code.shape,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_st_le32,Guest.Software.guestFn_st_le64,paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
    using checked

theorem le32_call (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointerExpression valueExpression : ExpHOL 64) (pointer query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (read : eval source pointerExpression=some (.val (.word pointer)))
    (away : CopyGeneral.Away pointer query 4)
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (Code.name .st_le32) [pointerExpression,valueExpression])=(none,post)) :
    post.memory query=source.memory query :=
  call_frame source post .st_le32 pointerExpression valueExpression pointer query (entry .st_le32 (by simp) source.code installed) read
    (by intro current target codeEq binding value normal
        have frame := le32_body current pointer query binding away
        rw [normal] at frame
        exact frame) actual

def lowerArguments : List (ExpHOL 64) := [localVar "p",localVar "v"]
def upperPointer : ExpHOL 64 := .op .add [localVar "p",.const 4#64]
def upperValue : ExpHOL 64 := .shift .lsr (localVar "v") (.const 32#64)
def afterLower : ProgHOL 64 := .seq (.call (some (none,none)) (Code.name .st_le32) [upperPointer,upperValue]) (.return (.const 0#64))

theorem le64_shape : Code.body .st_le64 = .seq (.call (some (none,none)) (Code.name .st_le32) lowerArguments) afterLower := by
  simp only [Code.body,Code.entry,Code.declaration,Code.name,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_st_le64,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    lowerArguments,afterLower,upperPointer,upperValue,localVar]

theorem le64_body (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (binding : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (away : CopyGeneral.Away pointer query 8) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source (Code.body .st_le64)=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [le64_shape] at actual
  have safe : LocalPrefix (ofString "p") (.call (some (none,none)) (Code.name .st_le32) lowerArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have read : eval source (localVar "p")=some (.val (.word pointer)) := by simpa [eval,evalHOLExact,toExact,localVar] using binding
  have low := le32_call source middle (localVar "p") (localVar "v") pointer query installed read (by intro offset inside; exact away offset (by omega)) normal
  have nextPointer := (CallNormal.ignored_lookup source middle (ofString "p") (Code.name .st_le32) lowerArguments normal).trans binding
  have nextCode : OriginalCode.Installed middle.code := by rw [(evaluation_fields source middle _ none normal).2.2.2]; exact installed
  unfold afterLower at remaining
  obtain ⟨final,upperRun,returned⟩ := Input.sequence_returned middle post _ _ value
    ((show LocalPrefix (ofString "p") (.call (some (none,none)) (Code.name .st_le32) [upperPointer,upperValue]) from .call none _ _ (by intro name impossible; cases impossible)).summary_full middle).2.1 remaining
  have upperRead : eval middle upperPointer=some (.val (.word (pointer+4#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,upperPointer,localVar,nextPointer,valueIsWord,valueWord,wordOpHOL,wordOp]
  have high := le32_call middle final upperPointer upperValue (pointer+4#64) query nextCode upperRead
    (CopyGeneral.Away.subrange pointer query 8 4 4 away (by decide)) upperRun
  have tail := MemoryAt.return_current final (.const 0#64) query
  rw [returned] at tail
  exact tail.trans (high.trans low)

theorem le64_call (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointerExpression valueExpression : ExpHOL 64) (pointer query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (read : eval source pointerExpression=some (.val (.word pointer)))
    (away : CopyGeneral.Away pointer query 8)
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (Code.name .st_le64) [pointerExpression,valueExpression])=(none,post)) :
    post.memory query=source.memory query :=
  call_frame source post .st_le64 pointerExpression valueExpression pointer query (entry .st_le64 (by simp) source.code installed) read
    (by intro current target codeEq binding value normal
        have currentCode : OriginalCode.Installed current.code := by rw [codeEq]; exact installed
        exact le64_body current target pointer query currentCode binding away value normal) actual

end InitECandidate.Solver.Input.CurrentHash.WordStoreMemory

#print axioms InitECandidate.Solver.Input.CurrentHash.WordStoreMemory.le32_supported
#print axioms InitECandidate.Solver.Input.CurrentHash.WordStoreMemory.le32_body
#print axioms InitECandidate.Solver.Input.CurrentHash.WordStoreMemory.call_frame
#print axioms InitECandidate.Solver.Input.CurrentHash.WordStoreMemory.entry
#print axioms InitECandidate.Solver.Input.CurrentHash.WordStoreMemory.le32_call
#print axioms InitECandidate.Solver.Input.CurrentHash.WordStoreMemory.le64_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.WordStoreMemory.le64_body
#print axioms InitECandidate.Solver.Input.CurrentHash.WordStoreMemory.le64_call
