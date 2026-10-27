import InitECandidate.Solver.Input.HeaderGuard

namespace InitECandidate.Solver.Input.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def lengthTest (limit : Nat) : ExpHOL 64 := .cmp .lower (localVar "len") (.const (BitVec.ofNat 64 limit))
def lengthGuard (limit error : Nat) : ProgHOL 64 := .ite (lengthTest limit)
  (.call (some (none,none)) (ofString "ssz_fail") [.const (BitVec.ofNat 64 error)]) .skip
def schemaFirst : ExpHOL 64 := .cmp .notEqual (.loadByte (localVar "p")) (.const 21#64)
def schemaSecond : ExpHOL 64 := .cmp .notEqual (.loadByte (Scalar.plus (localVar "p") 1)) (.const 1#64)
def schemaTest : ExpHOL 64 := .cmp .notEqual (.const 0#64) (.op .or [schemaFirst,schemaSecond])
def schemaGuard : ProgHOL 64 := .ite schemaTest (.call (some (none,none)) (ofString "ssz_fail") [.const 2#64]) .skip
def shiftPointer : ProgHOL 64 := .assign .local (ofString "p") (Scalar.plus (localVar "p") 2)
def shiftLength : ProgHOL 64 := .assign .local (ofString "len") (.op .sub [localVar "len",.const 2#64])
def shifted (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (length : Nat) :
    PanSemStateFiniteExact 64 Guest.HostMemory :=
  WitnessRadix.QueryBranch.bind (WitnessRadix.QueryBranch.bind source "p" (pointer+2#64)) "len" (BitVec.ofNat 64 (length-2))

theorem entry_shape : body=.seq (lengthGuard 2 1) (.seq schemaGuard
    (.seq shiftPointer (.seq shiftLength (.seq (lengthGuard 16 80) afterHeader)))) := by
  simp only [body,afterHeader,Guest.Software.guestFn_decode_stateless_input,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none,lengthGuard,lengthTest,schemaGuard,schemaTest,schemaFirst,schemaSecond,
    shiftPointer,shiftLength,Scalar.plus,localVar]

theorem length_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length limit : Nat)
    (lengthSmall : length<2^64) (limitSmall : limit<2^64)
    (localPresent : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length)))) :
    eval source (lengthTest limit)=some (.val (.word (if length<limit then 1#64 else 0#64))) := by
  classical
  have encodedL : (BitVec.ofNat 64 length).toNat=length := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt lengthSmall]
  have encodedN : (BitVec.ofNat 64 limit).toNat=limit := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt limitSmall]
  simp [eval,lengthTest,localVar,evalHOLExact,toExact,localPresent,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    BitVec.lt_def,encodedL,encodedN]

/-- Both real local assignments after the schema bytes; neither changes clock,
ordinary/shared memory, global variables or any FFI field. -/
theorem shift_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (length : Nat)
    (lengthSmall : length<2^64) (large : 2≤length)
    (pointerLocal : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthLocal : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length)))) :
    evaluateHOLFiniteState source (.seq shiftPointer shiftLength)=(none,shifted source pointer length) ∧
    evaluateHOLFiniteState source shiftPointer=(none,WitnessRadix.QueryBranch.bind source "p" (pointer+2#64)) ∧
    evaluateHOLFiniteState (WitnessRadix.QueryBranch.bind source "p" (pointer+2#64)) shiftLength=(none,shifted source pointer length) := by
  classical
  have pRead : eval source (localVar "p")=some (.val (.word pointer)) := by
    simpa [eval,localVar,evalHOLExact,toExact] using pointerLocal
  have pointerRun:=WitnessRadix.StateSteps.assign_execute source "p" (Scalar.plus (localVar "p") 2)
    pointer (pointer+2#64) pointerLocal (Scalar.plus_read source (localVar "p") pointer 2 pRead)
  let next:=WitnessRadix.QueryBranch.bind source "p" (pointer+2#64)
  have n : next.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))) :=
    (bind_lookup_other source "p" "len" _ (by decide)).trans lengthLocal
  have lengthRead : eval next (.op .sub [localVar "len",.const 2#64])=some (.val (.word (BitVec.ofNat 64 (length-2)))) := by
    have subtract : BitVec.ofNat 64 length-2#64=BitVec.ofNat 64 (length-2) :=
      BitVec.ofNat_sub_ofNat_of_le length 2 (by decide) large
    simp [eval,localVar,evalHOLExact,evalListHOLExact,toExact,n,valueIsWord,valueWord,wordOpHOL,wordOp,subtract]
  have lengthRun:=WitnessRadix.StateSteps.assign_execute next "len" _ (BitVec.ofNat 64 length) (BitVec.ofNat 64 (length-2)) n lengthRead
  have pointerStep : evaluateHOLFiniteState source shiftPointer=(none,next) := pointerRun
  refine ⟨?_,pointerStep,lengthRun⟩
  rw [WitnessRadix.StateSteps.next_sequence source next _ _ pointerStep (Nat.le_refl _)]
  exact lengthRun

end InitECandidate.Solver.Input.Header

#print axioms InitECandidate.Solver.Input.Header.entry_shape
#print axioms InitECandidate.Solver.Input.Header.length_read
#print axioms InitECandidate.Solver.Input.Header.shift_execute
