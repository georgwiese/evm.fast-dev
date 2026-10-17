import InitECandidate.Solver.Input.CopyWalk
import InitECandidate.Solver.Input.CopyDomain

namespace InitECandidate.Solver.Input.Blob
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def returnPair : ProgHOL 64 := .return (.rstruct [localVar "p",localVar "len"])
def pair (pointer : BitVec 64) (length : Nat) : ValueHOL 64 :=
  .rStruct [.val (.word pointer),.val (.word (BitVec.ofNat 64 length))]

/-- The complete actual input-copy loop and return, with all mapped host and
heap accesses derived from the challenge domains and one allocation extent. -/
theorem copy_return (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer old : BitVec 64) (length : Nat) (bounded : length≤Guest.maxInputBytes)
    (lower : 2701131776≤pointer.toNat) (upper : pointer.toNat+length+8≤33806089496)
    (aligned : pointer.toNat%8=0)
    (pointerLocal : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (indexLocal : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (lengthLocal : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))))
    (wordLocal : source.locals.lookup (ofString "w")=some (.val (.word old)))
    (oracleEq : source.ffi.oracle=InitE.sourceOracle) (host : source.ffi.ffiState=Guest.guestHostMemory input)
    (ordinary : source.memaddrs=InitE.ordinaryDomain) (shared : source.shMemaddrs=InitE.sharedDomain)
    (enough : copyRounds length≤source.clock) :
    evaluateHOLFiniteState source (.seq copyLoop returnPair)=
      (some (.returned (pair pointer length)),emptyLocalsHOLFinite (walk source pointer 0 (copyRounds length))) := by
  classical
  have fit:=copyRounds_fit length bounded
  have small : length+8<2^64 := by change length≤134217712 at bounded; omega
  have loopRun:=copy_loop source pointer old 0 length (copyRounds length) small
    (by simpa using fit.1) (by simpa using fit.2.1) (by decide)
    pointerLocal indexLocal lengthLocal wordLocal oracleEq
    (by intro offset lo hi a; rw [shared]; exact data_mapped offset (by omega) a)
    (by intro offset lo hi a; rw [ordinary]; exact heap_copy_mapped pointer length offset lower upper aligned hi a)
    (by
      intro offset lo hi a byte b
      rw [host]
      exact HostWords.present input offset (HostWords.final_word_visible length offset bounded hi a) byte b)
    enough
  let target:=walk source pointer 0 (copyRounds length)
  have pointerAfter : target.locals.lookup (ofString "p")=some (.val (.word pointer)) := by
    rw [walk_other _ _ _ _ _ (by decide) (by decide)]
    exact pointerLocal
  have lengthAfter : target.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))) := by
    rw [walk_other _ _ _ _ _ (by decide) (by decide)]
    exact lengthLocal
  have returned : evaluateHOLFiniteState target returnPair=(some (.returned (pair pointer length)),emptyLocalsHOLFinite target) := by
    simp [returnPair,pair,evaluateHOLFiniteState_return,localVar,evalHOLExact,evalListHOLExact,toExact,
      pointerAfter,lengthAfter,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  rw [WitnessRadix.StateSteps.next_sequence source target _ _ loopRun (by rw [walk_clock]; omega)]
  exact returned

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.copy_return
