import InitECandidate.Solver.Input.ZeroShortLoops
import InitECandidate.Solver.WitnessRadix.CopyGeneralMemory
import InitECandidate.Solver.Input.StoreMemoryAway
import InitECandidate.Solver.Input.MemoryContinue
import InitECandidate.Solver.Input.MemoryBoundedLoop

namespace InitECandidate.Solver.Input.ZeroByteFlow
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual ordinary zero byte-store lists preserve every other backing
word. The original counter increment itself changes no memory. -/
theorem stores_memory (offsets : List Nat) (stride length index : Nat)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (dst query : BitVec 64)
    (pointer : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (position : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (active : index+stride≤length) (within : ∀ offset∈offsets,offset<stride)
    (away : CopyGeneral.Away dst query length)
    (run : evaluateHOLFiniteState source (stores offsets (Zero.increment (BitVec.ofNat 64 stride)))=(none,post)) : post.memory query=source.memory query := by
  induction offsets generalizing source post with
  | nil=>
    have frame := MemoryAt.assign_current source .local (ofString "i") (addConst (localVar "i") (BitVec.ofNat 64 stride)) query
    change evaluateHOLFiniteState source (Zero.increment (BitVec.ofNat 64 stride))=(none,post) at run
    change (evaluateHOLFiniteState source (Zero.increment (BitVec.ofNat 64 stride))).2.memory query=source.memory query at frame
    rw [run] at frame
    exact frame
  | cons offset rest ih=>
    change evaluateHOLFiniteState source (.seq (byteStore offset) (stores rest (Zero.increment (BitVec.ofNat 64 stride))))=(none,post) at run
    obtain ⟨middle,normal,remaining⟩ := sequence_none source post _ _ run
    have localFrame (key : MlS) : middle.locals.lookup key=source.locals.lookup key := by
      have safe := byte_store_local key (.op .add (if offset=0 then [localVar "dst",localVar "i"] else [localVar "dst",localVar "i",.const (BitVec.ofNat 64 offset)])) (.const 0#64) source
      change LocalSummary key (byteStore offset) source at safe
      unfold LocalSummary at safe
      rw [normal] at safe
      exact safe.1 rfl
    have read : eval source (.op .add (if offset=0 then [localVar "dst",localVar "i"] else [localVar "dst",localVar "i",.const (BitVec.ofNat 64 offset)]))=
        some (.val (.word (dst+BitVec.ofNat 64 (index+offset)))) := by
      by_cases zero : offset=0
      · subst offset
        simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,pointer,position,valueIsWord,valueWord,wordOpHOL,wordOp]
      · simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,pointer,position,valueIsWord,valueWord,wordOpHOL,wordOp,zero,BitVec.ofNat_add,BitVec.add_assoc]
    have bounded : index+offset<length := by have h:=within offset (by simp); omega
    have first := MemoryAt.byte_store_current source _ (.const 0#64) (dst+BitVec.ofNat 64 (index+offset)) query read (away (index+offset) bounded).2
    change (evaluateHOLFiniteState source (byteStore offset)).2.memory query=source.memory query at first
    rw [normal] at first
    exact (ih middle post ((localFrame (ofString "dst")).trans pointer) ((localFrame (ofString "i")).trans position)
      (by intro next member; exact within next (by simp [member])) remaining).trans first

/-- Original byte8 zeroing body writes only the eight bytes at its real
current bounded counter. -/
theorem byte_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (dst query : BitVec 64) (length index : Nat)
    (pointer : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (position : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (active : index+8≤length) (away : CopyGeneral.Away dst query length)
    (run : evaluateHOLFiniteState source Zero.byteBody=(none,post)) : post.memory query=source.memory query := by
  rw [byte_shape] at run
  exact stores_memory [0,1,2,3,4,5,6,7] 8 length index source post dst query pointer position active (by intro offset member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member; rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide) away run

/-- Original tail byte store has the same precise backing-word frame. -/
theorem tail_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (dst query : BitVec 64) (length index : Nat)
    (pointer : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (position : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (active : index+1≤length) (away : CopyGeneral.Away dst query length)
    (run : evaluateHOLFiniteState source Zero.tailBody=(none,post)) : post.memory query=source.memory query := by
  rw [Zero.tail_body_shape] at run
  change evaluateHOLFiniteState source (stores [0] (Zero.increment 1#64))=(none,post) at run
  exact stores_memory [0] 1 length index source post dst query pointer position active (by simp) away run

end InitECandidate.Solver.Input.ZeroByteFlow

#print axioms InitECandidate.Solver.Input.ZeroByteFlow.stores_memory
#print axioms InitECandidate.Solver.Input.ZeroByteFlow.byte_memory
#print axioms InitECandidate.Solver.Input.ZeroByteFlow.tail_memory
