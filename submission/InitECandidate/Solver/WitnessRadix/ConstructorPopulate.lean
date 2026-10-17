import InitECandidate.Solver.WitnessRadix.ConstructorRecordLoop
import InitECandidate.Solver.WitnessRadix.ConstructorFinish

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact BackingLayout
open Flapjack.Basis.Pure.MlString

def populatePrice (maximum count : Nat) : Nat := (recordPrice maximum+1)*count+1028*count+1

/-- The complete actual record loop, radix-index helper and table return,
from allocated initialized-header/decoded-record/ABI/code facts. All hash
and copy executions are derived. The final tree uses their actual digests. -/
theorem populate (source : PanSemStateFiniteExact 64 Guest.HostMemory) (layout : Layout) (valid : Valid layout)
    (sliceFor : BitVec 64 → Graph.Slice) (stp padScratch hashScratch : BitVec 64) (maximum : Nat)
    (mapped : Mapped source layout)
    (locals : Locals source layout.keys layout.vals layout.primary layout.records 0#64)
    (countLocal : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 layout.count))))
    (tableLocal : source.locals.lookup (ofString "t")=some (.val (.word layout.table)))
    (fixedData : FixedData source layout sliceFor) (context : HashContext source layout sliceFor stp padScratch hashScratch maximum)
    (helperCode : source.code.lookup (ofString "solver_radix_index")=some (BuildEntry.formals,BuildProgram.body,.one))
    (enough : populatePrice maximum layout.count≤source.clock) :
    ∃ keyFor : BitVec 64 → ByteKeys.Key,∃ target : PanSemStateFiniteExact 64 Guest.HostMemory,∃ root : BitVec 64,
      evaluateHOLFiniteState source (.seq recordLoop afterRecords)=(some (.returned (.val (.word layout.table))),target) ∧
      target.memaddrs (cell layout .header 24) ∧ target.memory (cell layout .header 24)=.word root ∧
      QueryMemory.Represents target layout.table layout.keys layout.vals root (initialTree keyFor sliceFor (ordinals layout.count)) ∧
      KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl source ∧ target.clock≤source.clock ∧
      source.clock-populatePrice maximum layout.count≤target.clock := by
  classical
  let emptyKeys : BitVec 64 → ByteKeys.Key := fun _ _ => 0#8
  obtain ⟨keys,afterLoop,loopRun,loopPrefix,loopFixed,loopMapped,loopLocals,loopControl,loopUpper,loopLower,loopOther,loopKeys⟩ :=
    record_loop source layout valid sliceFor stp padScratch hashScratch maximum 0 layout.count emptyKeys (by omega) mapped locals countLocal
      (prefix_empty source layout emptyKeys) fixedData context (by unfold populatePrice at enough; omega)
  have afterCount : afterLoop.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 layout.count))) :=
    (loopOther (ofString "n") (by decide)).trans countLocal
  have afterTable : afterLoop.locals.lookup (ofString "t")=some (.val (.word layout.table)) :=
    (loopOther (ofString "t") (by decide)).trans tableLocal
  have afterCode : afterLoop.code.lookup (ofString "solver_radix_index")=some (BuildEntry.formals,BuildProgram.body,.one) := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.code.lookup (ofString "solver_radix_index")) loopControl
    exact h.trans helperCode
  obtain ⟨target,root,finishRun,rootMapped,rootWord,represented,finishControl,finishLower,finishUpper⟩ :=
    finish afterLoop layout valid loopMapped keys sliceFor loopFixed loopPrefix afterTable afterCount afterCode
      (by unfold populatePrice at enough; omega)
  have finishHashControl := KeccakAbsorb.hashControl_of_control afterLoop target finishControl
  refine ⟨keys,target,root,?_,rootMapped,rootWord,represented,finishHashControl.trans loopControl,by omega,?_⟩
  · exact (StateSteps.next_sequence source afterLoop _ _ loopRun loopUpper).trans finishRun
  · unfold populatePrice
    omega

theorem populatePrice_nodes (count : Nat) : populatePrice 1024 count=1374*count+1 := by
  unfold populatePrice recordPrice Keccak256.price
  omega

theorem populatePrice_code (count : Nat) : populatePrice 65536 count=10854*count+1 := by
  unfold populatePrice recordPrice Keccak256.price
  omega

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.populate
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.populatePrice_nodes
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.populatePrice_code
