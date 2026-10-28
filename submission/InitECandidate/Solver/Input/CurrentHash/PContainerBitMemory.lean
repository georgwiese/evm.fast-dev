import InitECandidate.Solver.Input.CurrentHash.PContainerBitLoop
import InitECandidate.Solver.Input.MemoryBoundedLoop
import InitECandidate.Solver.Input.StoreMemoryAway
import InitECandidate.Solver.Input.MemoryContinue
import InitECandidate.Solver.Input.CopyAwaySubrange

namespace InitECandidate.Solver.Input.CurrentHash.PContainer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The current activity-bit store changes only its real accumulator's
backing word, irrespective of the previous mask or stored value. -/
theorem bit_step_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (act query : BitVec 64) (index : Nat)
    (inside : index<256) (activity : source.locals.lookup (ofString "act")=some (.val (.word act)))
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

/-- Actual bounded current activity-mask loop preserves every word outside
its real 32-byte destination; next counter bounds come from that execution. -/
theorem bit_loop_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (act query : BitVec 64) (n index : Nat)
    (short : n≤256) (inside : index≤n)
    (activity : source.locals.lookup (ofString "act")=some (.val (.word act)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (position : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (away : CopyGeneral.Away act query 32)
    (run : evaluateHOLFiniteState source bitLoop=(none,post)) : post.memory query=source.memory query := by
  let invariant := fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>
    current.locals.lookup (ofString "act")=some (.val (.word act)) ∧ current.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n)))
  have readTest (current : PanSemStateFiniteExact 64 Guest.HostMemory) (currentIndex : Nat) (bounded : currentIndex≤n)
      (indexLocal : current.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 currentIndex))))
      (lengthLocal : current.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n)))) :
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) test=some (.val (.word (if currentIndex+1≤n then 1#64 else 0#64))) := by
    have iNumber : (BitVec.ofNat 64 currentIndex).toNat=currentIndex := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have nNumber : (BitVec.ofNat 64 n).toNat=n := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have relation : (currentIndex<n)=(currentIndex+1≤n) := propext (by omega)
    simp [evalHOLFinite,evalHOLExact,toExact,test,localVar,indexLocal,lengthLocal,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,iNumber,nNumber,
      show currentIndex<9223372036854775808 from by omega,show n<9223372036854775808 from by omega,relation]
  rw [body_shape.2.2.2.2.2.2.2.1] at run
  have final := MemoryAt.bounded_counter_loop_normal source.code (ofString "i") (ofString "n") test bitStep 1 n query
    (fun current=>(bit_step_other (ofString "n") (by decide)).summary_full current) bit_step_advances invariant
    (by intro current ready; exact ready)
    (by intro current ready currentIndex bounded cell; exact readTest current currentIndex bounded cell ready.2)
    (by intro current codeEq ready currentIndex active cell target bodyRun
        have actSummary := (bit_step_other (ofString "act") (by decide)).summary_full current
        have nSummary := (bit_step_other (ofString "n") (by decide)).summary_full current
        unfold LocalSummary at actSummary nSummary
        rw [bodyRun] at actSummary nSummary
        exact ⟨⟨(actSummary.1 rfl).trans ready.1,(nSummary.1 rfl).trans ready.2⟩,
          bit_step_memory current target act query currentIndex (by omega) ready.1 cell away bodyRun⟩)
    source post index rfl ⟨activity,count⟩ inside position run
  exact final.2.2

end InitECandidate.Solver.Input.CurrentHash.PContainer

#print axioms InitECandidate.Solver.Input.CurrentHash.PContainer.bit_step_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.PContainer.bit_loop_memory
