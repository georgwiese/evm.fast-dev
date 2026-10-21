import InitECandidate.Solver.Headers.ValidateRound
import InitECandidate.Solver.Input.ArgumentPairReads
import InitECandidate.Solver.WitnessRadix.Keccak256CurrentCall

namespace InitECandidate.Solver.Headers.Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def digestPointer (data : Data) (index : Nat) := byteAddress data.hashes (32*index)

set_option maxRecDepth 100000 in
theorem hash_original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "keccak256")=some (Keccak256.formals,Keccak256.body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 92 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_keccak256) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Keccak256.body,Keccak256.formals,
    Guest.guestFn_keccak256,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

/-- The real original hash arguments reuse both current SSZ row loads;
the output address is the corresponding actual32-byte digest slot. -/
theorem hash_arguments_read (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (inside : index<data.count) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) hashArguments=
      some (Keccak256.values (data.pointers index) (digestPointer data index) (data.lengths index).toNat) := by
  have args:=state.rows.read source data.array data.pointers data.lengths data.count data.lower data.upper index inside state.arena.domain state.arrayCell state.indexCell
  have reads:=Input.ArgumentValues.pair_reads source (.load .one row) (.load .one rowLength) (.val (.word (data.pointers index))) (.val (.word (data.lengths index))) args
  have outputRead : eval source hashCell=some (.val (.word (digestPointer data index))) := by
    simp [hashCell,localVar,eval,evalHOLExact,evalListHOLExact,toExact,state.hashesCell,state.indexCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,
      digestPointer,byteAddress,BitVec.ofNat_mul,Nat.mul_comm]
  simp only [eval] at reads outputRead
  simp [hashArguments,Keccak256.values,evalListHOLFinite,evalListHOLExact,reads.1,reads.2,outputRead]

theorem hash_buffers (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (layout : RoundLayout data) (inside : index<data.count) :
    Keccak256.Buffers data.stp (data.pointers index) data.pad (digestPointer data index) (data.lengths index).toNat :=
  ⟨layout.state,layout.stateAligned,state.rows.inputArena index inside,layout.pad,layout.padAligned,
    AllocatedBytes.Arena.subrange data.hashes (32*data.count+32) (32*index) 32 layout.hashes (by omega)⟩

theorem hash_cost (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (layout : RoundLayout data) (inside : index<data.count) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak256") hashArguments)).2.clock≤
      Keccak256.price (data.lengths index).toNat+1 := by
  have buffers:=hash_buffers data origin source index state layout inside
  have entered:=Keccak256.allocated_entry source data.stp (data.pointers index) data.pad (digestPointer data index) (data.lengths index).toNat state.environment buffers
  exact Keccak256.call_cost source hashArguments (some none) data.stp (data.pointers index) data.pad (digestPointer data index) (data.lengths index).toNat
    (hash_arguments_read data origin source index state inside) (hash_original_code source.code state.installed) entered
    (by have h:=buffers.inputArena.upper; omega)

end InitECandidate.Solver.Headers.Validate

#print axioms InitECandidate.Solver.Headers.Validate.hash_original_code
#print axioms InitECandidate.Solver.Headers.Validate.hash_arguments_read
#print axioms InitECandidate.Solver.Headers.Validate.hash_buffers
#print axioms InitECandidate.Solver.Headers.Validate.hash_cost
