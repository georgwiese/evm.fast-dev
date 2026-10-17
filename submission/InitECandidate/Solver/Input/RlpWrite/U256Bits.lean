import InitECandidate.Solver.Input.RlpWrite.U256BitsSegment

namespace InitECandidate.Solver.Input.RlpWrite.U256Bits
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_u256_bit_length with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "a",U256Value.tupleShape)]
def test (index : Fin 4) : ExpHOL 64 := .cmp .notEqual (U256Value.limb index) (.const 0#64)
def scan : List (Fin 4×Nat×String)→ProgHOL 64
  | []=>.call none (ofString "bit_length64") [U256Value.limb 0]
  | (index,offset,name)::rest=>.seq (.ite (test index) (segment name offset (U256Value.limb index)) .skip) (scan rest)

theorem body_shape : body=scan [(3,192,"n3"),(2,128,"n2"),(1,64,"n1")] := by
  simp only [body,Guest.guestFn_u256_bit_length,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    scan,test,segment,segmentReturn,U256Value.limb,localVar]
  rfl

theorem scan_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Value.Words) (pieces : List (Fin 4×Nat×String))
    (offsets : ∀ piece∈pieces,piece.2.1≤192)
    (a : source.locals.lookup (ofString "a")=some (U256Value.tuple words))
    (code : source.code.lookup (ofString "bit_length64")=some (BitLength.formals,BitLength.body,.one)) (enough : 1≤source.clock) :
    ∃ target bits,bits≤256 ∧ evaluateHOLFiniteState source (scan pieces)=(some (.returned (.val (.word (BitVec.ofNat 64 bits)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-1} := by
  classical
  induction pieces with
  | nil=>exact tail_execute source (words 0) (U256Value.limb 0) (U256Value.limb_read source words 0 a) code enough
  | cons piece rest ih=>
    obtain ⟨index,offset,name⟩:=piece
    have read:=U256Value.limb_read source words index a
    have testRead : eval source (test index)=some (.val (.word (if words index=0#64 then 0#64 else 1#64))) := by
      simp only [eval] at read ⊢
      rw [test,evalHOLExact,read]
      simp [evalHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    simp only [eval] at testRead
    by_cases zero : words index=0#64
    · have guardRun : evaluateHOLFiniteState source (.ite (test index) (segment name offset (U256Value.limb index)) .skip)=(none,source) := by
        rw [evaluateHOLFiniteState_ite,testRead]
        simp [zero]
      obtain ⟨target,bits,bound,run,frame⟩:=ih (by intro piece inside; exact offsets piece (List.mem_cons_of_mem _ inside))
      refine ⟨target,bits,bound,?_,frame⟩
      rw [scan,WitnessRadix.StateSteps.next_sequence source source _ _ guardRun (Nat.le_refl _)]
      exact run
    · obtain ⟨target,bits,bound,segmentRun,frame⟩:=segment_execute source (words index) name offset (U256Value.limb index)
        (offsets (index,offset,name) (by simp)) read code enough
      have guardRun : evaluateHOLFiniteState source (.ite (test index) (segment name offset (U256Value.limb index)) .skip)=
          (some (.returned (.val (.word (BitVec.ofNat 64 bits)))),target) := by
        rw [evaluateHOLFiniteState_ite,testRead]
        simpa [zero] using segmentRun
      have clock:=congrArg PanSemStateFiniteExact.clock frame
      change target.clock=source.clock-1 at clock
      refine ⟨target,bits,bound,?_,frame⟩
      rw [scan]
      exact WitnessRadix.StateSteps.stopped_sequence source target _ _ (.returned (.val (.word (BitVec.ofNat 64 bits)))) guardRun (by omega)

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Value.Words)
    (a : source.locals.lookup (ofString "a")=some (U256Value.tuple words))
    (code : source.code.lookup (ofString "bit_length64")=some (BitLength.formals,BitLength.body,.one)) (enough : 1≤source.clock) :
    ∃ target bits,bits≤256 ∧ evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 bits)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-1} := by
  rw [body_shape]
  exact scan_execute source words _ (by intro piece inside; simp at inside; rcases inside with rfl|rfl|rfl <;> decide) a code enough

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Value.Words)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [U256Value.tuple words])
    (code : source.code.lookup (ofString "u256_bit_length")=some (formals,body,.one))
    (bitCode : source.code.lookup (ofString "bit_length64")=some (BitLength.formals,BitLength.body,.one)) (enough : 2≤source.clock) :
    ∃ bits,bits≤256 ∧ evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "u256_bit_length") expressions continuation)=
      (let output:=evaluateHOLFiniteState (bind {source with clock:=source.clock-1-1} name (BitVec.ofNat 64 bits)) continuation
      (output.1,restore source name output.2)) := by
  obtain ⟨callee,called,a⟩:=U256Value.environment source.code.lookup (ofString "u256_bit_length") body words code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,bits,bound,bodyRun,frame⟩:=execute entry words a bitCode (by change 1≤source.clock-1; omega)
  exact ⟨bits,bound,CallNormal.pure_return_execute source target name (ofString "u256_bit_length") expressions [U256Value.tuple words]
    body continuation callee (BitVec.ofNat 64 bits) 1 args called (by omega) bodyRun frame⟩

end InitECandidate.Solver.Input.RlpWrite.U256Bits

#print axioms InitECandidate.Solver.Input.RlpWrite.U256Bits.scan_execute
#print axioms InitECandidate.Solver.Input.RlpWrite.U256Bits.execute
#print axioms InitECandidate.Solver.Input.RlpWrite.U256Bits.call_execute
