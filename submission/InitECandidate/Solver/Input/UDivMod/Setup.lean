import InitECandidate.Solver.Input.UDivMod.Loop

namespace InitECandidate.Solver.Input.UDivMod
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def frozen (source : PanSemStateFiniteExact 64 Guest.HostMemory) := emptyLocalsHOLFinite {source with clock:=0}
def pairValue (q r : BitVec 64) : ValueHOL 64 := .rStruct [.val (.word q),.val (.word r)]

theorem setup_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (aLocal : source.locals.lookup (ofString "a")=some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "b")=some (.val (.word b))) (enough : 64≤source.clock) :
    ∃ target q r,evaluateHOLFiniteState source setupProgram=(some (.returned (pairValue q r)),target) ∧
      target.clock=source.clock-64 ∧ frozen target=frozen source ∧
      (∀ bSmall : b.toNat≤2^63,0<b.toNat→q.toNat=a.toNat/b.toNat ∧ r.toNat=a.toNat%b.toNat) := by
  classical
  let q0:=bind source "q" 0#64
  let r0:=bind q0 "r" 0#64
  let entry:=bind r0 "i" 64#64
  have aEntry : entry.locals.lookup (ofString "a")=some (.val (.word a)) :=
    (bind_lookup_other r0 "i" "a" _ (by decide)).trans ((bind_lookup_other q0 "r" "a" _ (by decide)).trans
      ((bind_lookup_other source "q" "a" _ (by decide)).trans aLocal))
  have bEntry : entry.locals.lookup (ofString "b")=some (.val (.word b)) :=
    (bind_lookup_other r0 "i" "b" _ (by decide)).trans ((bind_lookup_other q0 "r" "b" _ (by decide)).trans
      ((bind_lookup_other source "q" "b" _ (by decide)).trans bLocal))
  have qEntry : entry.locals.lookup (ofString "q")=some (.val (.word 0#64)) :=
    (bind_lookup_other r0 "i" "q" _ (by decide)).trans ((bind_lookup_other q0 "r" "q" _ (by decide)).trans (bind_lookup_same source "q" _))
  have rEntry : entry.locals.lookup (ofString "r")=some (.val (.word 0#64)) :=
    (bind_lookup_other r0 "i" "r" _ (by decide)).trans (bind_lookup_same q0 "r" _)
  have iEntry : entry.locals.lookup (ofString "i")=some (.val (.word 64#64)) := bind_lookup_same r0 "i" _
  obtain ⟨loopPost,q,r,loopRun,loopEq,finalI,finalQ,finalR,others,arithmetic⟩:=loop_execute entry a b 0#64 0#64 64 (by decide) enough aEntry bEntry qEntry rEntry iEntry
  have loopClock : loopPost.clock=source.clock-64:=congrArg PanSemStateFiniteExact.clock loopEq
  have returnRun : evaluateHOLFiniteState loopPost returnPair=(some (.returned (pairValue q r)),emptyLocalsHOLFinite loopPost) := by
    simp [returnPair,pairValue,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,localVar,finalQ,finalR,
      shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have enteredRun : evaluateHOLFiniteState entry initializedBody=(some (.returned (pairValue q r)),emptyLocalsHOLFinite loopPost) := by
    rw [initializedBody,WitnessRadix.StateSteps.next_sequence entry loopPost _ _ loopRun (by change loopPost.clock≤source.clock; omega)]
    exact returnRun
  have iRun:=ScalarScope.declare_execute r0 (emptyLocalsHOLFinite loopPost) "i" (.const 64#64) 64#64 initializedBody
    (some (.returned (pairValue q r))) rfl enteredRun
  have rRun:=ScalarScope.declare_execute q0 (restore r0 "i" (emptyLocalsHOLFinite loopPost)) "r" (.const 0#64) 0#64
    (.dec (ofString "i") .one (.const 64#64) initializedBody) (some (.returned (pairValue q r))) rfl iRun
  have qRun:=ScalarScope.declare_execute source (restore q0 "r" (restore r0 "i" (emptyLocalsHOLFinite loopPost))) "q" (.const 0#64) 0#64
    (.dec (ofString "r") .one (.const 0#64) (.dec (ofString "i") .one (.const 64#64) initializedBody))
    (some (.returned (pairValue q r))) rfl rRun
  refine ⟨_,q,r,qRun,loopClock,?_,?_⟩
  · change frozen loopPost=frozen source
    rw [loopEq]
    rfl
  · intro bSmall positive
    exact arithmetic_finish a b q r (arithmetic bSmall (arithmetic_initial a b positive))

end InitECandidate.Solver.Input.UDivMod

#print axioms InitECandidate.Solver.Input.UDivMod.setup_execute
