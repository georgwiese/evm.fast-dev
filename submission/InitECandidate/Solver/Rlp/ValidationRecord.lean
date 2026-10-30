import InitECandidate.Solver.Rlp.ValidationProgram
import InitECandidate.Solver.Rlp.ValidationMemory
import InitECandidate.Solver.PanFieldStores

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def recordWrites (pointer resume parent previous : BitVec 64) : List (BitVec 64 × BitVec 64) :=
  [(pointer,resume),(pointer+8#64,parent),(pointer+16#64,previous)]
def recordPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer resume parent previous : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  {source with memory := WordWrites.write source.memory (recordWrites pointer resume parent previous)}

/-- Exact original three-store record prefix. Its first destination is the
literal local rec; later stores use rec+8 and rec+16. -/
theorem record_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer resume parent previous : BitVec 64)
    (recordCell : source.locals.lookup (ofString "rec")=some (.val (.word pointer)))
    (resumeCell : source.locals.lookup (ofString "after")=some (.val (.word resume)))
    (parentCell : source.locals.lookup (ofString "end")=some (.val (.word parent)))
    (previousCell : source.locals.lookup (ofString "top")=some (.val (.word previous)))
    (mapped0 : source.memaddrs pointer) (mapped8 : source.memaddrs (pointer+8#64)) (mapped16 : source.memaddrs (pointer+16#64)) :
    evaluateHOLFiniteState source pushStores=evaluateHOLFiniteState (recordPost source pointer resume parent previous) pushMoves := by
  let middle := {source with memory := StoreWord.put source.memory pointer resume}
  have addressRead : eval source (localVar "rec")=some (.val (.word pointer)) := by simp [eval,localVar,evalHOLExact,toExact,recordCell]
  have valueRead : eval source (localVar "after")=some (.val (.word resume)) := by simp [eval,localVar,evalHOLExact,toExact,resumeCell]
  have firstRun := StoreWord.execute source _ _ pointer resume addressRead valueRead mapped0
  let fields : List FieldStores.Field := [⟨8,.saved "end" parent⟩,⟨16,.saved "top" previous⟩]
  have ready : ∀ field∈fields,field.value.Ready middle "unused" 0#64 := by
    intro field member
    rcases List.mem_cons.mp member with same | rest
    · subst field; exact parentCell
    · have same := List.mem_singleton.mp rest
      subst field; exact previousCell
  have mapped : ∀ field∈fields,middle.memaddrs (pointer+BitVec.ofNat 64 field.offset) := by
    intro field member
    rcases List.mem_cons.mp member with same | rest
    · subst field; exact mapped8
    · have same := List.mem_singleton.mp rest
      subst field; exact mapped16
  have separate : ∀ reader∈fields,∀ writer∈fields,reader.value.Avoid 0#64 (pointer+BitVec.ofNat 64 writer.offset) := by
    intro reader readerIn writer writerIn
    rcases List.mem_cons.mp readerIn with same | rest
    · subst reader; trivial
    · have same := List.mem_singleton.mp rest
      subst reader; trivial
  have stores := FieldStores.execute middle "rec" "unused" pointer 0#64 fields recordCell ready mapped separate pushMoves
  have shape : pushStores=.seq (.store (localVar "rec") (localVar "after")) (FieldStores.program "rec" "unused" fields pushMoves) := rfl
  rw [shape,StateSteps.next_sequence source middle _ _ firstRun (Nat.le_refl _),stores]
  rfl

theorem record_distinct (pointer resume parent previous : BitVec 64) (fits : pointer.toNat+24<2^64) :
    ((recordWrites pointer resume parent previous).map Prod.fst).Nodup := by
  have n8 : (pointer+8#64).toNat=pointer.toNat+8 := by rw [BitVec.toNat_add_of_lt (by change pointer.toNat+8<2^64; omega)]; rfl
  have n16 : (pointer+16#64).toNat=pointer.toNat+16 := by rw [BitVec.toNat_add_of_lt (by change pointer.toNat+16<2^64; omega)]; rfl
  have a : pointer≠pointer+8#64 := by intro same; have h := congrArg BitVec.toNat same; rw [n8] at h; omega
  have b : pointer≠pointer+16#64 := by intro same; have h := congrArg BitVec.toNat same; rw [n16] at h; omega
  have c : pointer+8#64≠pointer+16#64 := by intro same; have h := congrArg BitVec.toNat same; rw [n8,n16] at h; omega
  simp [recordWrites,a,b,c]

theorem record_words (memory : WordWrites.Memory) (pointer resume parent previous : BitVec 64) (fits : pointer.toNat+24<2^64) :
    WordWrites.write memory (recordWrites pointer resume parent previous) pointer=.word resume ∧
      WordWrites.write memory (recordWrites pointer resume parent previous) (pointer+8#64)=.word parent ∧
      WordWrites.write memory (recordWrites pointer resume parent previous) (pointer+16#64)=.word previous := by
  have distinct := record_distinct pointer resume parent previous fits
  exact ⟨WordWrites.write_unique memory _ (pointer,resume) distinct (by simp [recordWrites]),
    WordWrites.write_unique memory _ (pointer+8#64,parent) distinct (by simp [recordWrites]),
    WordWrites.write_unique memory _ (pointer+16#64,previous) distinct (by simp [recordWrites])⟩

theorem record_upper_agreement (memory : WordWrites.Memory) (pointer resume parent previous : BitVec 64) (cursor : Nat)
    (fits : pointer.toNat+24<2^64) (below : pointer.toNat+24≤cursor) (query : BitVec 64) (upper : cursor≤query.toNat) :
    WordWrites.write memory (recordWrites pointer resume parent previous) query=memory query := by
  have n8 : (pointer+8#64).toNat=pointer.toNat+8 := by rw [BitVec.toNat_add_of_lt (by change pointer.toNat+8<2^64; omega)]; rfl
  have n16 : (pointer+16#64).toNat=pointer.toNat+16 := by rw [BitVec.toNat_add_of_lt (by change pointer.toNat+16<2^64; omega)]; rfl
  apply WordWrites.write_away
  simp only [recordWrites,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,not_or,not_false_eq_true,and_true]
  constructor
  · intro same; have h := congrArg BitVec.toNat same; omega
  constructor
  · intro same; have h := congrArg BitVec.toNat same; rw [n8] at h; omega
  · intro same; have h := congrArg BitVec.toNat same; rw [n16] at h; omega

/-- Actual linked-stack record stores cannot affect an earlier word. -/
theorem record_lower_agreement (memory : WordWrites.Memory) (pointer resume parent previous : BitVec 64)
    (fits : pointer.toNat+24<2^64) (query : BitVec 64) (before : query.toNat < pointer.toNat) :
    WordWrites.write memory (recordWrites pointer resume parent previous) query=memory query := by
  have n8 : (pointer+8#64).toNat=pointer.toNat+8 := by
    rw [BitVec.toNat_add_of_lt (by change pointer.toNat+8<2^64; omega)]; rfl
  have n16 : (pointer+16#64).toNat=pointer.toNat+16 := by
    rw [BitVec.toNat_add_of_lt (by change pointer.toNat+16<2^64; omega)]; rfl
  apply WordWrites.write_away
  simp only [recordWrites,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,not_or,not_false_eq_true,and_true]
  constructor
  · intro same; have h := congrArg BitVec.toNat same; omega
  constructor
  · intro same; have h := congrArg BitVec.toNat same; rw [n8] at h; omega
  · intro same; have h := congrArg BitVec.toNat same; rw [n16] at h; omega

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.record_execute
#print axioms InitECandidate.Solver.Rlp.Validation.record_distinct
#print axioms InitECandidate.Solver.Rlp.Validation.record_words
#print axioms InitECandidate.Solver.Rlp.Validation.record_upper_agreement

#print axioms InitECandidate.Solver.Rlp.Validation.record_lower_agreement
