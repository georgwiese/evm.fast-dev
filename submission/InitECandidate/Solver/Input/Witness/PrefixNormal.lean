import InitECandidate.Solver.Input.Witness.OffsetProgram
import InitECandidate.Solver.Input.HeaderGuard
import InitECandidate.Solver.WitnessRadix.ProgramPrefix

namespace InitECandidate.Solver.Input.Witness
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
open WitnessRadix.ProgramPrefix
set_option maxRecDepth 10000

def pointerPrepared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset : Nat):=
  bind source "wp" (pointer+BitVec.ofNat 64 (2+offset))
def prefixPrepared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer : BitVec 64) (offset : Nat):=
  bind (pointerPrepared source pointer offset) "wlen" (BitVec.ofNat 64 (input.length%2^64-2-offset))

/-- Actual witness pointer/length declarations and the short-input guard.
Normal execution proves the twelve-byte minimum before reaching offsetBody. -/
theorem prefix_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer : BitVec 64) (offset : Nat) (heap : Blob.HeapInput source input pointer)
    (extent : 2≤input.length%2^64) (offsetUpper : offset≤input.length%2^64-2)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+2#64))))
    (n : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 (input.length%2^64-2)))))
    (o : source.locals.lookup (ofString "o_wit")=some (.val (.word (BitVec.ofNat 64 offset))))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 1≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source prefixBody=(some (.returned value),post)) :
    12≤input.length%2^64-2-offset ∧
      (prefixPrepared source input pointer offset).locals.lookup (ofString "wp")=
        some (.val (.word (pointer+BitVec.ofNat 64 (2+offset)))) ∧
      (prefixPrepared source input pointer offset).locals.lookup (ofString "wlen")=
        some (.val (.word (BitVec.ofNat 64 (input.length%2^64-2-offset)))) ∧
      Blob.HeapInput (prefixPrepared source input pointer offset) input pointer ∧
      ∃ innerPost,evaluateHOLFiniteState (prefixPrepared source input pointer offset) offsetBody=(some (.returned value),innerPost) ∧
        post=restore source "wp" (restore (pointerPrepared source pointer offset) "wlen" innerPost) := by
  classical
  have bytesSmall : input.length%2^64<2^64:=Nat.mod_lt _ (by decide)
  have pointerRead : eval source witnessPointer=some (.val (.word (pointer+BitVec.ofNat 64 (2+offset)))) := by
    simp [eval,witnessPointer,localVar,evalHOLExact,evalListHOLExact,toExact,p,o,valueIsWord,valueWord,
      wordOpHOL,wordOp,BitVec.add_assoc,BitVec.ofNat_add]
  have n' : (pointerPrepared source pointer offset).locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 (input.length%2^64-2)))):=
    (bind_lookup_other source "wp" "len" _ (by decide)).trans n
  have o' : (pointerPrepared source pointer offset).locals.lookup (ofString "o_wit")=some (.val (.word (BitVec.ofNat 64 offset))):=
    (bind_lookup_other source "wp" "o_wit" _ (by decide)).trans o
  have difference : BitVec.ofNat 64 (input.length%2^64-2)-BitVec.ofNat 64 offset=
      BitVec.ofNat 64 (input.length%2^64-2-offset):=BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) offsetUpper
  have lengthRead : eval (pointerPrepared source pointer offset) witnessLength=
      some (.val (.word (BitVec.ofNat 64 (input.length%2^64-2-offset)))) := by
    simp [eval,witnessLength,localVar,evalHOLExact,evalListHOLExact,toExact,n',o',valueIsWord,valueWord,wordOpHOL,wordOp]
    exact difference
  have setup : Executes source [.declare "wp" witnessPointer,.declare "wlen" witnessLength]
      (prefixPrepared source input pointer offset) (fun target=>restore source "wp" (restore (pointerPrepared source pointer offset) "wlen" target)) := by
    refine Executes.declare (restoreRest:=fun target=>restore (pointerPrepared source pointer offset) "wlen" target) _ pointerRead ?_
    exact Executes.declare (restoreRest:=id) _ lengthRead (Executes.done _)
  have actual:=WitnessRadix.ProgramPrefix.execute setup (.seq shortGuard offsetBody)
  rw [offset_shapes.1] at run
  have normal:=actual.symm.trans run
  let ready:=prefixPrepared source input pointer offset
  have result:=congrArg Prod.fst normal
  have postEq : post=restore source "wp" (restore (pointerPrepared source pointer offset) "wlen"
      (evaluateHOLFiniteState ready (.seq shortGuard offsetBody)).2):=(congrArg Prod.snd normal).symm
  have readyWp : ready.locals.lookup (ofString "wp")=some (.val (.word (pointer+BitVec.ofNat 64 (2+offset)))):=
    (bind_lookup_other _ "wlen" "wp" _ (by decide)).trans (bind_lookup_same _ _ _)
  have readyLen : ready.locals.lookup (ofString "wlen")=some (.val (.word (BitVec.ofNat 64 (input.length%2^64-2-offset)))):=bind_lookup_same _ _ _
  have lengthNumber : (BitVec.ofNat 64 (input.length%2^64-2-offset)).toNat=input.length%2^64-2-offset := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have test : eval ready (.cmp .lower (localVar "wlen") (.const 12#64))=
      some (.val (.word (if input.length%2^64-2-offset<12 then 1#64 else 0#64))) := by
    simp [eval,localVar,evalHOLExact,toExact,readyLen,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,lengthNumber]
    have lengthFits : input.length%18446744073709551616-2-offset<18446744073709551616:=by omega
    rw [Nat.mod_eq_of_lt lengthFits]
  have guard:=Header.test_guard_execute ready (.cmp .lower (localVar "wlen") (.const 12#64)) 82#64
    (input.length%2^64-2-offset<12) test failCode exceptionShape enough
  change evaluateHOLFiniteState ready shortGuard=_ at guard
  by_cases short : input.length%2^64-2-offset<12
  · simp only [if_pos short] at guard
    have stopped:=StateSteps.stopped_sequence ready _ shortGuard offsetBody (.exception (ofString "SszErr") (.val (.word 82#64))) guard
      (by change source.clock-1≤source.clock;omega)
    rw [stopped] at result
    cases result
  · simp only [if_neg short] at guard
    have continued:=StateSteps.next_sequence ready ready shortGuard offsetBody guard (Nat.le_refl _)
    rw [continued] at result
    refine ⟨by omega,readyWp,readyLen,heap,(evaluateHOLFiniteState ready offsetBody).2,Prod.ext result rfl,?_⟩
    rw [postEq,continued]

end InitECandidate.Solver.Input.Witness

#print axioms InitECandidate.Solver.Input.Witness.prefix_normal
