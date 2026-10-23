import InitECandidate.Solver.Mpt.NodeRlpBeginProgram
import InitECandidate.Solver.Mpt.TrieWalkValueAgreement
import InitECandidate.Solver.Input.ClockCostSequenceReached
import InitECandidate.Solver.Input.AssignNormal

namespace InitECandidate.Solver.Mpt.NodeRlpBegin
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem leaf_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) (limit : Nat)
    (property : BitVec 64→BitVec 64→Prop) (view : TrieWalk.ValueView source.memory source.memaddrs node 48#64 56#64 limit property)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) leafArguments=some [.val (.word view.pointer),.val (.word view.length)] := by
  simp [leafArguments,nodeField,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,nodeCell,valueIsWord,valueWord,wordOpHOL,wordOp,
    memLoadHOLExact,isWfShapeExactHOL,view.pointerMapped,view.pointerStored,view.lengthMapped,view.lengthStored]

theorem leaf_value_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) (limit : Nat)
    (property : BitVec 64→BitVec 64→Prop) (view : TrieWalk.ValueView source.memory source.memaddrs node 48#64 56#64 limit property)
    (fits : limit+9<2^64) (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))) :
    source.clock-(evaluateHOLFiniteState source leafValueCall).2.clock≤12 := by
  obtain ⟨callee,called,_pointerCell,lengthCell⟩:=ValueEncodedLen.environment source.code.lookup view.pointer view.length (ValueEncodedLen.original_code source.code installed)
  exact Input.ClockCost.scoped_current source (ofString "vl") .one (ofString "rlp_value_encoded_len") leafArguments _ ValueEncodedLen.body addLeaf callee .one 11 0
    (leaf_arguments source node limit property view nodeCell) called
    (ValueEncodedLen.body_cost (callEntryStateHOLFinite source callee) view.length (by have size:=view.payload.1; omega) installed lengthCell)
    (Input.ClockCost.assign source.code _ _)

theorem after_encoded_safe (key : MlS) (different : key≠ofString "payload") (notResult : key≠ofString "vl") : Input.LocalPrefix key afterEncoded := by
  rw [after_encoded_shapes.1,after_encoded_shapes.2]
  exact .seq (.assign _ _ different) (.ite _ (.decCall _ _ _ _ notResult (.assign _ _ different)) .skip)

/-- Current encoded-path continuation: only a genuine leaf needs its
actual stored value fields. Extensions require no value-read premise. -/
theorem after_encoded_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag encoded : BitVec 64) (limit : Nat)
    (property : BitVec 64→BitVec 64→Prop)
    (view : tag=1#64→TrieWalk.ValueView source.memory source.memaddrs node 48#64 56#64 limit property)
    (fits : limit+9<2^64) (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word tag)))
    (encodedCell : source.locals.lookup (ofString "el")=some (.val (.word encoded))) :
    source.clock-(evaluateHOLFiniteState source afterEncoded).2.clock≤12 := by
  rw [after_encoded_shapes.1]
  apply Input.ClockCost.sequence_reached_current source assignPath leafChoice 0 12 (Input.ClockCost.assign source.code _ _ source rfl)
  intro current run
  have read : eval source (localVar "el")=some (.val (.word encoded)):=by simpa only [eval,evalHOLExact,toExact,localVar] using encodedCell
  have same:=Input.assign_none source current "payload" (localVar "el") encoded read run
  have currentTag : current.locals.lookup (ofString "k")=some (.val (.word tag)):=by rw [same]; exact (bind_lookup_other source "payload" "k" encoded (by decide)).trans tagCell
  have selected : evaluateHOLFiniteState current leafChoice=
      if tag=1#64 then evaluateHOLFiniteState current leafValueCall else (none,current):=by
    rw [after_encoded_shapes.2,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,currentTag,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
  rw [selected]
  by_cases leaf : tag=1#64
  · rw [if_pos leaf,same]
    exact leaf_value_cost (bind source "payload" encoded) node limit property (view leaf) fits installed
      ((bind_lookup_other source "payload" "node" encoded (by decide)).trans nodeCell)
  · rw [if_neg leaf]
    simp

end InitECandidate.Solver.Mpt.NodeRlpBegin

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.leaf_arguments
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.leaf_value_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.after_encoded_safe
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.after_encoded_cost
