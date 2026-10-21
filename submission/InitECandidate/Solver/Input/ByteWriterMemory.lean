import InitECandidate.Solver.Input.TwoWordNormalArguments
import InitECandidate.Solver.Input.StoreMemoryAway
import InitECandidate.Solver.Input.ByteStoreLocal
import InitECandidate.Solver.Input.MemoryContinue

namespace InitECandidate.Solver.Input.MemoryWordCalls
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Real normal byte-writer store lists preserve every other backing word,
without assuming any stored scalar value or successful future byte write. -/
theorem stores_memory (clauses : List (Nat×Nat)) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64)
    (cell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (away : ∀ clause∈clauses,query≠panByteAlignHOL (width:=64) (pointer+BitVec.ofNat 64 clause.1))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source (GasBudget.Be32Stores.stores clauses)=(some (.returned value),post)) : post.memory query=source.memory query := by
  induction clauses generalizing source post with
  | nil=>
    have frame := MemoryAt.return_current source (.const 0#64) query
    change evaluateHOLFiniteState source (.return (.const 0#64))=(some (.returned value),post) at run
    rw [run] at frame
    exact frame
  | cons clause rest ih=>
    have safe := byte_store_local (ofString "p") (GasBudget.Be32Stores.address clause.1) (GasBudget.Be32Stores.byteValue clause.2) source
    obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ (GasBudget.Be32Stores.stores rest) value safe.2.1 run
    have localFrame := safe
    unfold LocalSummary at localFrame
    rw [normal] at localFrame
    have nextCell := (localFrame.1 rfl).trans cell
    have first := MemoryAt.byte_store_current source (GasBudget.Be32Stores.address clause.1) (GasBudget.Be32Stores.byteValue clause.2) (pointer+BitVec.ofNat 64 clause.1) query
      (GasBudget.Be32Stores.read_address source pointer clause.1 cell) (away clause (by simp))
    rw [normal] at first
    exact (ih middle post nextCell (by intro next member; exact away next (by simp [member])) remaining).trans first

/-- Actual original st_be32 body writes only its four declared bytes. -/
theorem be32_body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64)
    (cell : source.locals.lookup (ofString "p")=some (.val (.word pointer))) (away : CopyGeneral.Away pointer query 4)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source GasBudget.MemoryWriter.Kind.be32.body=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [GasBudget.Be32Stores.original_body] at run
  apply stores_memory GasBudget.Be32Stores.clauses source post pointer query cell _ value run
  intro clause member
  have offset : clause.1<4 := by
    simp only [GasBudget.Be32Stores.clauses,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;> decide
  exact (away clause.1 offset).2

/-- Genuine normal original BE32 caller, with scalar value derived from the
real caller's ABI even when its value expression reads current hash memory. -/
theorem be32_call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (first second : ExpHOL 64) (pointer query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (firstRead : eval source first=some (.val (.word pointer)))
    (away : CopyGeneral.Away pointer query 4)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "st_be32") [first,second])=(none,post)) : post.memory query=source.memory query := by
  have code := GasBudget.Be32Stores.original_code source.code installed
  obtain ⟨word,args⟩ := normal_arguments source post (ofString "st_be32") GasBudget.MemoryWriter.Kind.be32.body first second pointer code firstRead run
  obtain ⟨callee,called,pLocal,vLocal⟩ := environment source.code.lookup (ofString "st_be32") GasBudget.MemoryWriter.Kind.be32.body pointer word code
  exact MemoryAt.call_normal source post (ofString "st_be32") [first,second] [.val (.word pointer),.val (.word word)] GasBudget.MemoryWriter.Kind.be32.body callee .one query args called
    (fun target value evaluated=>be32_body_memory (callEntryStateHOLFinite source callee) target pointer query pLocal away value evaluated) run

end InitECandidate.Solver.Input.MemoryWordCalls

#print axioms InitECandidate.Solver.Input.MemoryWordCalls.stores_memory
#print axioms InitECandidate.Solver.Input.MemoryWordCalls.be32_body_memory
#print axioms InitECandidate.Solver.Input.MemoryWordCalls.be32_call_memory
