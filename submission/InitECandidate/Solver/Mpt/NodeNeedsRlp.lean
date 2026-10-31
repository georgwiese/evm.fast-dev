import InitECandidate.Solver.Mpt.Fail
import InitECandidate.Solver.Input.WordEnvironment
import InitECandidate.Solver.Input.PureDecision
import InitECandidate.Solver.Input.ReturnFacts

namespace InitECandidate.Solver.Mpt.NodeNeedsRlp
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.Software.guestFn__node_needs_rlp with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "child",.one)]
def readAt (offset : Nat) : ExpHOL 64:=.load .one (.op .add [localVar "child",.const (BitVec.ofNat 64 offset)])
def zeroReturn : ProgHOL 64:=.return (.const 0#64)

theorem body_shape : body=.seq (.ite (.cmp .equal (localVar "child") (.const 0#64)) zeroReturn .skip)
    (.seq (.ite (.cmp .equal (readAt 0) (.const 0#64)) zeroReturn .skip)
      (.seq (.ite (.cmp .notEqual (readAt 8) (.const 0#64)) zeroReturn .skip) (.return (.const 1#64)))) := by
  simp only [body,Guest.Software.guestFn__node_needs_rlp,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,zeroReturn,readAt,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "_node_needs_rlp")=some (formals,body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 257 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn__node_needs_rlp) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.Software.guestFn__node_needs_rlp,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (child : BitVec 64)
    (known : codeFn (ofString "_node_needs_rlp")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "_node_needs_rlp") [.val (.word child)]=some (body,callee,.one) ∧
      callee.lookup (ofString "child")=some (.val (.word child)) :=
  Input.word_environment codeFn (ofString "_node_needs_rlp") (ofString "child") body .one child known

theorem pure_decision : Input.PureDecision body := by
  rw [body_shape]
  exact .seq (.ite _ (.returned _) .skip) (.seq (.ite _ (.returned _) .skip) (.seq (.ite _ (.returned _) .skip) (.returned _)))

/-- All outcomes are read-only and spend no source ticks, even when a
malformed operand makes a load or condition fail. -/
theorem readonly (code) : Input.LocalEffects.Preserves code body := by
  rw [body_shape]
  repeat first
    | apply Input.LocalEffects.sequence
    | apply Input.LocalEffects.conditional
    | exact Input.LocalEffects.returned code _
    | exact Input.LocalEffects.skip code

theorem body_cost (code) : Input.ClockCost.Bound code body 0 := by
  intro source installed
  have clock:=pure_decision.quiet code source installed
  rw [clock]
  omega

/-- Every real normal result is the literal binary traversal decision;
no readable-node or future traversal hypothesis is needed for this fact. -/
theorem binary (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    Input.ReturnFacts.Returns source body (fun value=>value=.val (.word 0#64) ∨ value=.val (.word 1#64)) := by
  rw [body_shape]
  unfold zeroReturn
  repeat first
    | apply Input.ReturnFacts.sequence
    | apply Input.ReturnFacts.conditional
    | exact Input.ReturnFacts.skip _ _
    | exact Input.ReturnFacts.returned _ (.const 0#64) (.val (.word 0#64)) _ rfl (Or.inl rfl)
    | exact Input.ReturnFacts.returned _ (.const 1#64) (.val (.word 1#64)) _ rfl (Or.inr rfl)
    | intro current _run

/-- The literal helper reads only a nonnull child's tag and, for a
non-hash child, its real RLP cache pointer. Null needs no readable node. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (child tag cached : BitVec 64)
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (header : child≠0#64→source.memaddrs child ∧ source.memory child=.word tag)
    (cache : child≠0#64→tag≠0#64→source.memaddrs (child+8#64) ∧ source.memory (child+8#64)=.word cached) :
    evaluateHOLFiniteState source body=(some (.returned (.val (.word (if child=0#64 ∨ tag=0#64 ∨ cached≠0#64 then 0#64 else 1#64)))),emptyLocalsHOLFinite source) := by
  by_cases childZero : child=0#64
  · simp [body_shape,zeroReturn,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,
      localVar,childCell,childZero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  · obtain ⟨mapped,stored⟩:=header childZero
    by_cases tagZero : tag=0#64
    · simp [body_shape,zeroReturn,readAt,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_return,evaluateHOLFiniteState_skip,
        evalHOLExact,evalListHOLExact,toExact,localVar,childCell,childZero,tagZero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,mapped,stored,shapeOfHOLExact,sizeOfShapeWithContextHOL]
    · obtain ⟨cacheMapped,cacheStored⟩:=cache childZero tagZero
      by_cases cachedZero : cached=0#64 <;>
        simp [body_shape,zeroReturn,readAt,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_return,evaluateHOLFiniteState_skip,
          evalHOLExact,evalListHOLExact,toExact,localVar,childCell,childZero,tagZero,cachedZero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
          valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,mapped,stored,cacheMapped,cacheStored,shapeOfHOLExact,sizeOfShapeWithContextHOL]

end InitECandidate.Solver.Mpt.NodeNeedsRlp

#print axioms InitECandidate.Solver.Mpt.NodeNeedsRlp.body_shape
#print axioms InitECandidate.Solver.Mpt.NodeNeedsRlp.original_code
#print axioms InitECandidate.Solver.Mpt.NodeNeedsRlp.environment
#print axioms InitECandidate.Solver.Mpt.NodeNeedsRlp.pure_decision
#print axioms InitECandidate.Solver.Mpt.NodeNeedsRlp.readonly
#print axioms InitECandidate.Solver.Mpt.NodeNeedsRlp.body_cost
#print axioms InitECandidate.Solver.Mpt.NodeNeedsRlp.binary
#print axioms InitECandidate.Solver.Mpt.NodeNeedsRlp.execute
