import InitECandidate.Solver.Input.RlpWrite.U256Value

namespace InitECandidate.Solver.Input.RlpWrite.U256Bits
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def segmentReturn (name : String) (offset : Nat) : ProgHOL 64 := .return (.op .add [.const (BitVec.ofNat 64 offset),localVar name])
def segment (name : String) (offset : Nat) (expression : ExpHOL 64) : ProgHOL 64 :=
  .decCall (ofString name) .one (ofString "bit_length64") [expression] (segmentReturn name offset)

theorem segment_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64)
    (name : String) (offset : Nat) (expression : ExpHOL 64) (small : offset≤192)
    (read : eval source expression=some (.val (.word value)))
    (code : source.code.lookup (ofString "bit_length64")=some (BitLength.formals,BitLength.body,.one)) (enough : 1≤source.clock) :
    ∃ target bits,bits≤256 ∧ evaluateHOLFiniteState source (segment name offset expression)=
      (some (.returned (.val (.word (BitVec.ofNat 64 bits)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-1} := by
  classical
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [expression]=some [.val (.word value)] := by
    simp only [eval] at read
    simpa only [evalListHOLFinite,evalListHOLExact,read] using rfl
  obtain ⟨bits,bound,called⟩:=BitLength.call_execute source value name [expression] (segmentReturn name offset) args code enough
  let entry:=bind {source with clock:=source.clock-1} name (BitVec.ofNat 64 bits)
  have n : entry.locals.lookup (ofString name)=some (.val (.word (BitVec.ofNat 64 bits))):=bind_lookup_same _ _ _
  have returnRun : evaluateHOLFiniteState entry (segmentReturn name offset)=
      (some (.returned (.val (.word (BitVec.ofNat 64 (offset+bits))))),emptyLocalsHOLFinite entry) := by
    simp [segmentReturn,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,localVar,n,valueIsWord,valueWord,wordOpHOL,wordOp,
      ←BitVec.ofNat_add,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  refine ⟨restore source name (emptyLocalsHOLFinite entry),offset+bits,by omega,?_,rfl⟩
  rw [segment,called,returnRun]

theorem tail_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64) (expression : ExpHOL 64)
    (read : eval source expression=some (.val (.word value)))
    (code : source.code.lookup (ofString "bit_length64")=some (BitLength.formals,BitLength.body,.one)) (enough : 1≤source.clock) :
    ∃ target bits,bits≤256 ∧ evaluateHOLFiniteState source (.call none (ofString "bit_length64") [expression])=
      (some (.returned (.val (.word (BitVec.ofNat 64 bits)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-1} := by
  classical
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [expression]=some [.val (.word value)] := by
    simp only [eval] at read
    simpa only [evalListHOLFinite,evalListHOLExact,read] using rfl
  obtain ⟨callee,called,x⟩:=CallNormal.unary_environment source.code.lookup (ofString "bit_length64") "x" BitLength.body value code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,bits,bound,bodyRun,frame⟩:=BitLength.execute entry value x
  have actual:=evaluateHOLFiniteState_call_return_none source (.val (.word (BitVec.ofNat 64 bits))) (ofString "bit_length64") [expression]
    [.val (.word value)] BitLength.body callee .one target args called (by omega) bodyRun (by simp [shapeOfHOLExact,shapeEqHOL])
  have outerFrame : emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-1}:=frame
  exact ⟨emptyLocalsHOLFinite target,bits,by omega,actual,by simpa only [emptyLocalsHOLFinite] using outerFrame⟩

end InitECandidate.Solver.Input.RlpWrite.U256Bits

#print axioms InitECandidate.Solver.Input.RlpWrite.U256Bits.segment_execute
#print axioms InitECandidate.Solver.Input.RlpWrite.U256Bits.tail_execute
