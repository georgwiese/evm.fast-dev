import InitECandidate.Solver.Input.ByteWriterMemory
import InitECandidate.Solver.Input.LittleEndianEffects
import InitECandidate.Solver.Input.CopyAwaySubrange
import InitECandidate.Solver.Input.IgnoredCallLookup

namespace InitECandidate.Solver.Input.MemoryWordCalls
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem le32_body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64)
    (cell : source.locals.lookup (ofString "p")=some (.val (.word pointer))) (away : CopyGeneral.Away pointer query 4)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source le32Body=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [le32_shape] at run
  exact stores_memory leClauses source post pointer query cell (by
    intro clause member
    have inside : clause.1<4 := by
      simp only [leClauses,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl <;> decide
    exact (away clause.1 inside).2) value run

theorem le32_call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (first second : ExpHOL 64) (pointer query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (firstRead : eval source first=some (.val (.word pointer)))
    (away : CopyGeneral.Away pointer query 4)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "st_le32") [first,second])=(none,post)) : post.memory query=source.memory query := by
  have code := le32_code source.code installed
  obtain ⟨word,args⟩ := normal_arguments source post (ofString "st_le32") le32Body first second pointer code firstRead run
  obtain ⟨callee,called,pLocal,vLocal⟩ := environment source.code.lookup (ofString "st_le32") le32Body pointer word code
  exact MemoryAt.call_normal source post (ofString "st_le32") [first,second] [.val (.word pointer),.val (.word word)] le32Body callee .one query args called
    (fun target value evaluated=>le32_body_memory (callEntryStateHOLFinite source callee) target pointer query pLocal away value evaluated) run

/-- Original two-call little-endian writer preserves words outside its
actual eight-byte destination. Stored values remain completely unrestricted. -/
theorem le64_body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (cell : source.locals.lookup (ofString "p")=some (.val (.word pointer))) (away : CopyGeneral.Away pointer query 8)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source le64Body=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [le64_shape] at run
  have safe : LocalPrefix (ofString "p") (.call (some (none,none)) (ofString "st_le32") le64FirstArgs) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,firstRun,remaining⟩ := Input.sequence_returned source post _ le64Tail value (safe.summary_full source).2.1 run
  have first := le32_call_memory source middle (localVar "p") (localVar "v") pointer query installed
    (by simpa [eval,evalHOLExact,toExact,localVar] using cell) (by intro offset inside; exact away offset (by omega)) firstRun
  have nextCell := (CallNormal.ignored_lookup source middle (ofString "p") (ofString "st_le32") le64FirstArgs firstRun).trans cell
  have fields := evaluation_fields source middle _ none firstRun
  unfold le64Tail at remaining
  have tailSafe : LocalPrefix (ofString "p") (.call (some (none,none)) (ofString "st_le32") le64SecondArgs) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨final,secondRun,returned⟩ := Input.sequence_returned middle post _ _ value (tailSafe.summary_full middle).2.1 remaining
  have read : eval middle (.op .add [localVar "p",.const 4#64])=some (.val (.word (pointer+4#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,nextCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have second := le32_call_memory middle final (.op .add [localVar "p",.const 4#64]) (.shift .lsr (localVar "v") (.const 32#64)) (pointer+4#64) query
    (fields.2.2.2.symm ▸ installed) read (CopyGeneral.Away.subrange pointer query 8 4 4 away (by decide)) secondRun
  have tail := MemoryAt.return_current final (.const 0#64) query
  rw [returned] at tail
  exact tail.trans (second.trans first)

theorem le64_call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (first second : ExpHOL 64) (pointer query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (firstRead : eval source first=some (.val (.word pointer)))
    (away : CopyGeneral.Away pointer query 8)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "st_le64") [first,second])=(none,post)) : post.memory query=source.memory query := by
  have code := le64_code source.code installed
  obtain ⟨word,args⟩ := normal_arguments source post (ofString "st_le64") le64Body first second pointer code firstRead run
  obtain ⟨callee,called,pLocal,vLocal⟩ := environment source.code.lookup (ofString "st_le64") le64Body pointer word code
  exact MemoryAt.call_normal source post (ofString "st_le64") [first,second] [.val (.word pointer),.val (.word word)] le64Body callee .one query args called
    (fun target value evaluated=>le64_body_memory (callEntryStateHOLFinite source callee) target pointer query installed pLocal away value evaluated) run

end InitECandidate.Solver.Input.MemoryWordCalls

#print axioms InitECandidate.Solver.Input.MemoryWordCalls.le32_body_memory
#print axioms InitECandidate.Solver.Input.MemoryWordCalls.le32_call_memory
#print axioms InitECandidate.Solver.Input.MemoryWordCalls.le64_body_memory
#print axioms InitECandidate.Solver.Input.MemoryWordCalls.le64_call_memory
