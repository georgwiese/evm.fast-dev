import InitECandidate.Solver.MutableTable.FindProgram
import InitECandidate.Solver.WitnessRadix.MemeqEnvironment
import InitECandidate.Solver.WitnessRadix.Bindings
import InitECandidate.Solver.Input.PureReturn

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
attribute [local instance] Classical.propDecidable

def next (p : Parameters) (index : BitVec 64) : BitVec 64:=(index+1#64) &&& (p.capacity-1#64)

theorem after_equal (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters) (index reply : BitVec 64)
    (locals : Locals source p index) (eqLocal : source.locals.lookup (ofString "eq")=some (.val (.word reply))) :
    evaluateHOLFiniteState source afterEqual=
      if reply=0#64 then (none,bind source "i" (next p index))
      else (some (.returned (.val (.word index))),emptyLocalsHOLFinite source) := by
  have read:=next_read source p index locals
  have assignRun:=WitnessRadix.StateSteps.assign_execute source "i" nextIndex index (next p index) locals.index read
  by_cases zero : reply=0#64
  · have skipRun : evaluateHOLFiniteState source (.ite equalTest (.return (localVar "i")) .skip)=(none,source) := by
      simp [evaluateHOLFiniteState_ite,equalTest,evalHOLExact,toExact,localVar,eqLocal,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero]
    rw [afterEqual,WitnessRadix.StateSteps.next_sequence source source _ _ skipRun (Nat.le_refl _),if_pos zero]
    exact assignRun
  · have returnRun : evaluateHOLFiniteState source (.ite equalTest (.return (localVar "i")) .skip)=
        (some (.returned (.val (.word index))),emptyLocalsHOLFinite source) := by
      simp [evaluateHOLFiniteState_ite,equalTest,evalHOLExact,toExact,localVar,eqLocal,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero,
        evaluateHOLFiniteState_return,locals.index,shapeOfHOLExact,sizeOfShapeWithContextHOL]
    rw [afterEqual,WitnessRadix.StateSteps.stopped_sequence source (emptyLocalsHOLFinite source) _ _ _ returnRun (Nat.le_refl _),if_neg zero]

theorem comparison_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters) (index : BitVec 64)
    (locals : Locals source p index) (keyLength : p.keyLength=32#64) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) comparisonArguments=
      some (WitnessRadix.Memeq32.values (p.keys+index*p.stride) p.key) := by
  simp [evalListHOLFinite,comparisonArguments,keyAddress,evalListHOLExact,evalHOLExact,toExact,localVar,locals.keys,locals.index,
    locals.stride,locals.key,locals.klen,keyLength,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,WitnessRadix.Memeq32.values]

/-- A real32-byte table probe, including memeq's real ABI/body/call and the
literal early-return or masked increment. Arbitrary key alignment is covered. -/
theorem step32 (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters) (index : BitVec 64)
    (locals : Locals source p index) (keyLength : p.keyLength=32#64) (left right : WitnessRadix.ByteKeys.Key)
    (leftView : WitnessRadix.MemoryBytes.ByteView source (p.keys+index*p.stride) left)
    (rightView : WitnessRadix.MemoryBytes.ByteView source p.key right)
    (leftFits : (p.keys+index*p.stride).toNat+32<2^64) (rightFits : p.key.toNat+32<2^64)
    (little : source.be=false)
    (code : source.code.lookup (ofString "memeq")=some (WitnessRadix.Memeq32.formals,WitnessRadix.Memeq32.body,.one))
    (enough : 5≤source.clock) :
    ∃ paid target,paid≤5 ∧
      evaluateHOLFiniteState source loopBody=(if left=right then some (.returned (.val (.word index))) else none,target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid} ∧
      (left≠right→target=bind {source with clock:=source.clock-paid} "i" (next p index)) := by
  classical
  let a:=p.keys+index*p.stride
  obtain ⟨callee,called,argA,argB,argN,_⟩:=WitnessRadix.Memeq32.environment source.code.lookup a p.key code
  let entry:=callEntryStateHOLFinite source callee
  have leftEntry:=WitnessRadix.MemoryBytes.byteView_of_fields source entry rfl rfl rfl a left leftView
  have rightEntry:=WitnessRadix.MemoryBytes.byteView_of_fields source entry rfl rfl rfl p.key right rightView
  obtain ⟨paid,bounded,run⟩:=WitnessRadix.Memeq32.memory_execute entry a p.key left right argA argB argN
    leftEntry rightEntry leftFits rightFits little (by change 4≤source.clock-1;omega)
  have frame : emptyLocalsHOLFinite (restore entry "i" (emptyLocalsHOLFinite {entry with clock:=entry.clock-paid}))=
      emptyLocalsHOLFinite {source with clock:=source.clock-1-paid}:=rfl
  let reply : BitVec 64:=if left=right then 1#64 else 0#64
  have caller:=Input.CallNormal.pure_return_execute source _ "eq" (ofString "memeq") comparisonArguments _ WitnessRadix.Memeq32.body afterEqual
    callee reply paid (comparison_arguments source p index locals keyLength) called (by omega) run frame
  let resumed:=bind {source with clock:=source.clock-1-paid} "eq" reply
  have inResumed : Locals resumed p index := by
    constructor
    · exact (bind_lookup_other _ "eq" "cap" _ (by decide)).trans locals.cap
    · exact (bind_lookup_other _ "eq" "klen" _ (by decide)).trans locals.klen
    · exact (bind_lookup_other _ "eq" "stride" _ (by decide)).trans locals.stride
    · exact (bind_lookup_other _ "eq" "keys" _ (by decide)).trans locals.keys
    · exact (bind_lookup_other _ "eq" "used" _ (by decide)).trans locals.used
    · exact (bind_lookup_other _ "eq" "key" _ (by decide)).trans locals.key
    · exact (bind_lookup_other _ "eq" "i" _ (by decide)).trans locals.index
  have tailRun:=after_equal resumed p index reply inResumed (bind_lookup_same _ _ _)
  change evaluateHOLFiniteState source loopBody=
    (let output:=evaluateHOLFiniteState resumed afterEqual;(output.1,restore source "eq" output.2)) at caller
  rw [tailRun] at caller
  have subtract : source.clock-1-paid=source.clock-(paid+1):=by omega
  by_cases same : left=right
  · have nonzero : reply≠0#64:=by simp [reply,same]
    rw [if_neg nonzero] at caller
    refine ⟨paid+1,restore source "eq" (emptyLocalsHOLFinite resumed),by omega,?_,?_,?_⟩
    · simpa only [if_pos same] using caller
    · dsimp [resumed]
      rw [subtract]
      rfl
    · intro different;exact False.elim (different same)
  · have zero : reply=0#64:=by simp [reply,same]
    rw [if_pos zero] at caller
    have restored : restore source "eq" (bind resumed "i" (next p index))=
        bind {source with clock:=source.clock-1-paid} "i" (next p index) := by
      rw [restore_bind_other _ _ "eq" "i" _ (by decide)]
      have back : restore source "eq" resumed={source with clock:=source.clock-1-paid}:=
        restore_bound {source with clock:=source.clock-1-paid} "eq" reply
      rw [back]
    change evaluateHOLFiniteState source loopBody=(none,restore source "eq" (bind resumed "i" (next p index))) at caller
    rw [restored,subtract] at caller
    refine ⟨paid+1,bind {source with clock:=source.clock-(paid+1)} "i" (next p index),by omega,?_,rfl,?_⟩
    · simpa only [if_neg same] using caller
    · intro _;rfl

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.after_equal
#print axioms InitECandidate.Solver.MutableTable.Find.comparison_arguments
#print axioms InitECandidate.Solver.MutableTable.Find.step32
