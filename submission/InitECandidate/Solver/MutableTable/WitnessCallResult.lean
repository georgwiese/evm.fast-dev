import InitECandidate.Solver.MutableTable.WitnessBuildRadixCallSupported
import InitECandidate.Solver.MutableTable.WitnessDictionaryPair
import InitECandidate.Solver.Input.EvaluationFields

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Both real ABI forms of the witness constructor's returned table. -/
structure ConstructorReturn (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arguments : List (ExpHOL 64)) (table : Nat) : Prop where
  ignored : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "nodedb_build") arguments)=(none,target)
  locals : target.locals=source.locals
  resume : ∀ (name : String) (continuation : ProgHOL 64),
    evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "nodedb_build") arguments continuation)=
      (let output:=evaluateHOLFiniteState (setVarHOLFinite (ofString name) (.val (.word (BitVec.ofNat 64 table))) target) continuation;
        (output.1,restore source name output.2))

/-- Code, memory-domain and endian invariants follow from the actual call
execution, including when the constructor is resumed through a declaration. -/
theorem ConstructorReturn.fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arguments : List (ExpHOL 64)) (table : Nat) (returned : ConstructorReturn source target arguments table) :
    target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.eshapes=source.eshapes ∧ target.code=source.code :=
  Input.evaluation_fields source target _ none returned.ignored

/-- One actual paired constructor result, packaged for sequential initialization.
All dictionary observations, ABI scopes and independent memory frames are retained. -/
structure ConstructorPairResult (source right leftTarget rightTarget : PanSemStateFiniteExact 64 Guest.HostMemory)
    (leftArguments rightArguments : List (ExpHOL 64)) {records table count : Nat}
    (observation : DictionaryObservation records table count) (sliceFor : BitVec 64 → Graph.Slice)
    (scratch : BitVec 64) (maximum : Nat) (region safe : BitVec 64 → Prop) : Prop where
  leftCall : ConstructorReturn source leftTarget leftArguments table
  rightCall : ConstructorReturn right rightTarget rightArguments table
  dictionary : DictionaryPair leftTarget rightTarget observation sliceFor scratch
  leftControl : KeccakAbsorb.hashControl leftTarget=KeccakAbsorb.hashControl {source with
    globals:=source.globals.update (ofString "heap_ptr",.val (.word (BitVec.ofNat 64 observation.heapEnd)))}
  rightControl : KeccakAbsorb.hashControl rightTarget=KeccakAbsorb.hashControl {right with
    globals:=right.globals.update (ofString "heap_ptr",.val (.word (BitVec.ofNat 64 observation.heapEnd)))}
  leftUpper : leftTarget.clock≤source.clock
  leftLower : source.clock-(wholePrice maximum count+1)≤leftTarget.clock
  rightUpper : rightTarget.clock≤right.clock
  rightLower : right.clock-(Constructor.wholePrice maximum count+1)≤rightTarget.clock
  globals : leftTarget.globals=rightTarget.globals
  ffi : leftTarget.ffi=rightTarget.ffi
  memory : MemoryRegion.Agree region leftTarget.memory rightTarget.memory
  leftFrame : ∀ query,safe query → leftTarget.memory query=source.memory query
  rightFrame : ∀ query,safe query → rightTarget.memory query=right.memory query

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.ConstructorReturn.fields
