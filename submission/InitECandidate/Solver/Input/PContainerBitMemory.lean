import InitECandidate.Solver.Input.PContainerBitLoop
import InitECandidate.Solver.Input.MemoryBoundedLoop
import InitECandidate.Solver.Input.StoreMemoryAway
import InitECandidate.Solver.Input.MemoryContinue
import InitECandidate.Solver.Input.CopyAwaySubrange

namespace InitECandidate.Solver.Input.PContainer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The original activity-bit store changes only its real accumulator's
backing word, irrespective of the previous mask or stored value. -/
theorem bit_step_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (act query : BitVec 64) (index : Nat)
    (inside : index<32) (activity : source.locals.lookup (ofString "act")=some (.val (.word act)))
    (position : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (away : CopyGeneral.Away act query 32)
    (run : evaluateHOLFiniteState source bitStep=(none,post)) : post.memory query=source.memory query := by
  have shifted : (BitVec.ofNat 64 index >>> (3:Nat))=BitVec.ofNat 64 (index/8) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show index<2^64 from by omega),Nat.shiftRight_eq_div_pow]
    omega
  have read : eval source bitAddress=some (.val (.word (act+BitVec.ofNat 64 (index/8)))) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,bitAddress,localVar,activity,position,valueIsWord,valueWord,wordOpHOL,wordOp,wordShiftHOL,shifted]
  rw [body_shape.2.2.2.2.2.2.2.2.1] at run
  obtain ⟨middle,stored,advanced⟩ := sequence_none source post _ _ run
  have front := MemoryAt.byte_store_current source bitAddress bitValue (act+BitVec.ofNat 64 (index/8)) query read (away (index/8) (by omega)).2
  rw [stored] at front
  have tail := MemoryAt.assign_current middle .local (ofString "i") (.op .add [localVar "i",.const 1#64]) query
  rw [advanced] at tail
  exact tail.trans front

/-- Actual bounded original activity-mask loop preserves every word outside
its real 32-byte destination; next counter bounds come from that execution. -/
theorem bit_loop_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (act query : BitVec 64) (n index : Nat)
    (short : n<32) (inside : index≤n)
    (activity : source.locals.lookup (ofString "act")=some (.val (.word act)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (position : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (away : CopyGeneral.Away act query 32)
    (run : evaluateHOLFiniteState source bitLoop=(none,post)) : post.memory query=source.memory query := by
  let invariant := fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>
    current.locals.lookup (ofString "act")=some (.val (.word act)) ∧ current.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n)))
  have model := bit_model source.code n short
  rw [body_shape.2.2.2.2.2.2.2.1] at run
  have final := MemoryAt.bounded_counter_loop_normal source.code (ofString "i") (ofString "n") test bitStep 1 n query model.summary model.advance invariant
    (by intro current ready; exact ready)
    (by intro current ready currentIndex bounded cell; exact model.read current currentIndex bounded cell ready.2)
    (by intro current codeEq ready currentIndex active cell target bodyRun
        have as:=bit_step_summary (ofString "act") (by decide) current
        have ns:=model.summary current
        unfold LocalSummary at as ns
        rw [bodyRun] at as ns
        exact ⟨⟨(as.1 rfl).trans ready.1,(ns.1 rfl).trans ready.2⟩,bit_step_memory current target act query currentIndex (by omega) ready.1 cell away bodyRun⟩)
    source post index rfl ⟨activity,count⟩ inside position run
  exact final.2.2

end InitECandidate.Solver.Input.PContainer

#print axioms InitECandidate.Solver.Input.PContainer.bit_step_memory
#print axioms InitECandidate.Solver.Input.PContainer.bit_loop_memory
