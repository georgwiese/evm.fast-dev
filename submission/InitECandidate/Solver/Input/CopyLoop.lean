import InitECandidate.Solver.Input.CopyState

namespace InitECandidate.Solver.Input.Blob
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual input loop, including every shared read and ordinary store,
uses exactly one source clock per copied word and returns normally. -/
theorem copy_loop (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer old : BitVec 64)
    (index length rounds : Nat) (small : length+8<2^64)
    (lower : length≤index+8*rounds) (upper : index+8*rounds<length+8)
    (aligned : index%8=0)
    (pointerLocal : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (indexLocal : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (lengthLocal : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))))
    (wordLocal : source.locals.lookup (ofString "w")=some (.val (.word old)))
    (oracleEq : source.ffi.oracle=InitE.sourceOracle)
    (sharedMapped : ∀ offset,index≤offset→offset<length→offset%8=0→source.shMemaddrs (Guest.inputDataAddr+BitVec.ofNat 64 offset))
    (ordinaryMapped : ∀ offset,index≤offset→offset<length→offset%8=0→source.memaddrs (pointer+BitVec.ofNat 64 offset))
    (present : ∀ offset,index≤offset→offset<length→offset%8=0→∀ byte<8,
      (source.ffi.ffiState (Guest.inputDataAddr+BitVec.ofNat 64 offset+BitVec.ofNat 64 byte)).isSome=true)
    (enough : rounds≤source.clock) :
    evaluateHOLFiniteState source copyLoop=(none,walk source pointer index rounds) := by
  classical
  induction rounds generalizing source index old with
  | zero =>
    have testRun:=copy_test source index length (by omega) (by omega) indexLocal lengthLocal
    have inactive : ¬index<length := by omega
    simp only [if_neg inactive] at testRun
    change @evalHOLFinite 64 Guest.HostMemory _ source (fun address=>Classical.propDecidable (source.memaddrs address)) copyCondition=some (.val (.word 0#64)) at testRun
    rw [copyLoop,evaluateHOLFiniteState_while_total,testRun]
    simp [walk]
  | succ rounds ih =>
    simp only [Nat.mul_succ] at lower upper
    have active : index<length := by omega
    have nonzero : source.clock≠0 := by omega
    let entry:=decClockHOLFinite source
    let next:=wordPost entry pointer (BitVec.ofNat 64 index)
    let value:=Guest.wordOfLeBytes (SharedRead.bytes entry.ffi.ffiState (Guest.inputDataAddr+BitVec.ofNat 64 index))
    have bodyRun:=copy_step entry pointer (BitVec.ofNat 64 index) old pointerLocal indexLocal wordLocal oracleEq
      (sharedMapped index (Nat.le_refl _) active aligned)
      (ordinaryMapped index (Nat.le_refl _) active aligned)
      (present index (Nat.le_refl _) active aligned)
    have fields:=wordPost_frame entry pointer (BitVec.ofNat 64 index)
    have nextClock : next.clock=source.clock-1 := fields.1
    have nextP : next.locals.lookup (ofString "p")=some (.val (.word pointer)) := by
      rw [wordPost_other entry pointer (BitVec.ofNat 64 index) _ (by decide) (by decide)]
      exact pointerLocal
    have nextI : next.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (index+8)))) := by
      simpa only [BitVec.ofNat_add] using wordPost_index entry pointer (BitVec.ofNat 64 index)
    have nextL : next.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))) := by
      rw [wordPost_other entry pointer (BitVec.ofNat 64 index) _ (by decide) (by decide)]
      exact lengthLocal
    have tailRun:=ih next value (index+8) (by omega) (by omega) (by omega)
      nextP nextI nextL (wordPost_word entry pointer (BitVec.ofNat 64 index)) (fields.2.2.2.2.trans oracleEq)
      (by intro offset lo hi a; exact sharedMapped offset (by omega) hi a)
      (by intro offset lo hi a; exact ordinaryMapped offset (by omega) hi a)
      (by intro offset lo hi a; exact present offset (by omega) hi a)
      (by rw [nextClock]; omega)
    have testRun:=copy_test source index length (by omega) (by omega) indexLocal lengthLocal
    simp only [if_pos active] at testRun
    change @evalHOLFinite 64 Guest.HostMemory _ source (fun address=>Classical.propDecidable (source.memaddrs address)) copyCondition=some (.val (.word 1#64)) at testRun
    rw [copyLoop,evaluateHOLFiniteState_while_total,testRun]
    simp only []
    simp only [show (1#64 : BitVec 64)≠0 from by decide,↓reduceIte,if_neg nonzero]
    rw [bodyRun,WitnessRadix.StateSteps.fixed_clock entry next none (Nat.le_refl _)]
    exact tailRun

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.copy_loop
