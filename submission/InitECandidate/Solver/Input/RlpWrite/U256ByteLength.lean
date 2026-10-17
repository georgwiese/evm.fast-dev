import InitECandidate.Solver.Input.RlpWrite.U256Bits

namespace InitECandidate.Solver.Input.RlpWrite.U256ByteLength
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_u256_byte_length with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "a",U256Value.tupleShape)]
def returnLength : ProgHOL 64 := .return (.shift .lsr (.op .add [localVar "n",.const 7#64]) (.const 3#64))

theorem body_shape : body=.decCall (ofString "n") .one (ofString "u256_bit_length") [localVar "a"] returnLength := by
  simp only [body,Guest.guestFn_u256_byte_length,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,returnLength,localVar]

theorem rounded_word (bits : Nat) (bound : bits≤256) :
    (BitVec.ofNat 64 bits+7#64) >>> (3:Nat)=BitVec.ofNat 64 ((bits+7)/8) := by
  have number : (BitVec.ofNat 64 bits).toNat=bits := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have sumNumber : (BitVec.ofNat 64 bits+7#64).toNat=bits+7 := by
    rw [BitVec.toNat_add_of_lt (by rw [number]; change bits+7<2^64; omega),number]
    rfl
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,sumNumber,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]

/-- Whole actual U256 byte-length computation and its natural<=32 bound. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Value.Words)
    (a : source.locals.lookup (ofString "a")=some (U256Value.tuple words))
    (code : source.code.lookup (ofString "u256_bit_length")=some (U256Bits.formals,U256Bits.body,.one))
    (bitCode : source.code.lookup (ofString "bit_length64")=some (BitLength.formals,BitLength.body,.one)) (enough : 2≤source.clock) :
    ∃ target length,length≤32 ∧ evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 length)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-2} := by
  classical
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "a"]=some [U256Value.tuple words] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,a]
  obtain ⟨bits,bound,called⟩:=U256Bits.call_execute source words "n" [localVar "a"] returnLength args code bitCode enough
  let entry:=bind {source with clock:=source.clock-1-1} "n" (BitVec.ofNat 64 bits)
  have n : entry.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 bits))):=bind_lookup_same _ _ _
  have returnRun : evaluateHOLFiniteState entry returnLength=(some (.returned (.val (.word (BitVec.ofNat 64 ((bits+7)/8))))),emptyLocalsHOLFinite entry) := by
    simp [returnLength,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,localVar,n,valueIsWord,valueWord,wordOpHOL,wordOp,
      wordShiftHOL,rounded_word bits bound,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  refine ⟨restore source "n" (emptyLocalsHOLFinite entry),(bits+7)/8,by omega,?_,?_⟩
  · rw [body_shape,called,returnRun]
  · have subtract : source.clock-1-1=source.clock-2 := by omega
    change emptyLocalsHOLFinite {source with clock:=source.clock-1-1}=emptyLocalsHOLFinite {source with clock:=source.clock-2}
    rw [subtract]

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Value.Words)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [U256Value.tuple words])
    (code : source.code.lookup (ofString "u256_byte_length")=some (formals,body,.one))
    (bitsCode : source.code.lookup (ofString "u256_bit_length")=some (U256Bits.formals,U256Bits.body,.one))
    (bitCode : source.code.lookup (ofString "bit_length64")=some (BitLength.formals,BitLength.body,.one)) (enough : 3≤source.clock) :
    ∃ length,length≤32 ∧ evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "u256_byte_length") expressions continuation)=
      (let output:=evaluateHOLFiniteState (bind {source with clock:=source.clock-1-2} name (BitVec.ofNat 64 length)) continuation
      (output.1,restore source name output.2)) := by
  obtain ⟨callee,called,a⟩:=U256Value.environment source.code.lookup (ofString "u256_byte_length") body words code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,length,bound,bodyRun,frame⟩:=execute entry words a bitsCode bitCode (by change 2≤source.clock-1; omega)
  exact ⟨length,bound,CallNormal.pure_return_execute source target name (ofString "u256_byte_length") expressions [U256Value.tuple words]
    body continuation callee (BitVec.ofNat 64 length) 2 args called (by omega) bodyRun frame⟩

end InitECandidate.Solver.Input.RlpWrite.U256ByteLength

#print axioms InitECandidate.Solver.Input.RlpWrite.U256ByteLength.rounded_word
#print axioms InitECandidate.Solver.Input.RlpWrite.U256ByteLength.execute
#print axioms InitECandidate.Solver.Input.RlpWrite.U256ByteLength.call_execute
