import InitECandidate.Solver.Input.RlpWrite.PutBeLoop

namespace InitECandidate.Solver.Input.RlpWrite.PutBe
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Whole literal byte-writing function, with exact source clock and memory
frame. The bytes written by its real store operations remain in the result. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst value : BitVec 64) (count : Nat) (small : count<2^64)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count))))
    (v : source.locals.lookup (ofString "v")=some (.val (.word value)))
    (mapped : ∀ index<count,source.memaddrs (panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))) (enough : count≤source.clock) :
    ∃ target,evaluateHOLFiniteState source body=(some (.returned (.val (.word 0#64))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-count} ∧
      (∀ query,(∀ index<count,query≠panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))→target.memory query=source.memory query) := by
  classical
  let entry:=bind source "i" (BitVec.ofNat 64 count)
  have dEntry : entry.locals.lookup (ofString "dst")=some (.val (.word dst)):=
    (bind_lookup_other _ "i" "dst" _ (by decide)).trans d
  have vEntry : entry.locals.lookup (ofString "v")=some (.val (.word value)):=
    (bind_lookup_other _ "i" "v" _ (by decide)).trans v
  have iEntry : entry.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 count))):=bind_lookup_same _ _ _
  obtain ⟨next,loopRun,frame,finalI,others,memory⟩:=loop_execute entry dst value count small dEntry iEntry vEntry mapped enough
  have nextClock:=congrArg PanSemStateFiniteExact.clock frame
  change next.clock=source.clock-count at nextClock
  have returnRun : evaluateHOLFiniteState next (.return (.const 0#64))=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite next) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have tailRun : evaluateHOLFiniteState entry tail=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite next) := by
    rw [tail,WitnessRadix.StateSteps.next_sequence entry next _ _ loopRun (by change next.clock≤source.clock; omega)]
    exact returnRun
  have readN : eval source (localVar "n")=some (.val (.word (BitVec.ofNat 64 count))) := by
    simp [eval,localVar,evalHOLExact,toExact,n]
  have scopeRun:=ScalarScope.declare_execute source _ "i" (localVar "n") (BitVec.ofNat 64 count) tail _ readN tailRun
  let target:=restore source "i" (emptyLocalsHOLFinite next)
  refine ⟨target,?_,?_,memory⟩
  · rw [body_shape]
    exact scopeRun
  · have pureFrame:=congrArg emptyLocalsHOLFinite frame
    change emptyLocalsHOLFinite next=emptyLocalsHOLFinite {source with memory:=next.memory,clock:=source.clock-count} at pureFrame ⊢
    exact pureFrame

def rawLocals (dst value n : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "n" then some (.val (.word n)) else if name=ofString "v" then some (.val (.word value))
  else if name=ofString "dst" then some (.val (.word dst)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (dst value n : BitVec 64)
    (lookup : codeFn (ofString "rlp_put_be")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "rlp_put_be") [.val (.word dst),.val (.word value),.val (.word n)]=some (body,callee,.one) ∧
      callee.lookup (ofString "dst")=some (.val (.word dst)) ∧ callee.lookup (ofString "v")=some (.val (.word value)) ∧
      callee.lookup (ofString "n")=some (.val (.word n)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=([.val (.word dst),.val (.word value),.val (.word n)] : List (ValueHOL 64)).length ∧
      ((formals.zip [.val (.word dst),.val (.word value),.val (.word n)]).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "rlp_put_be") [.val (.word dst),.val (.word value),.val (.word n)]=some (body,rawLocals dst value n,.one) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "dst"≠ofString "n" from by decide,show ofString "dst"≠ofString "v" from by decide]
  · simp [rawLocals,show ofString "v"≠ofString "n" from by decide]
  · simp [rawLocals]

end InitECandidate.Solver.Input.RlpWrite.PutBe

#print axioms InitECandidate.Solver.Input.RlpWrite.PutBe.execute
#print axioms InitECandidate.Solver.Input.RlpWrite.PutBe.environment
