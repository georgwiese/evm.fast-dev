import InitECandidate.Solver.Headers.CurrentValidate.Round
import InitECandidate.Solver.Input.ArgumentPairReads

namespace InitECandidate.Solver.Headers.CurrentValidate
open Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

def digestPointer (data : Data) (index : Nat) := byteAddress data.hashes (32*index)

/-- The real original hash arguments reuse both current SSZ row loads;
the output address is the corresponding actual32-byte digest slot. -/
theorem hash_arguments_read (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (inside : index<data.count) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) hashArguments=
      some (CurrentKeccak.Hash.values (data.pointers index) (digestPointer data index) (data.lengths index).toNat) := by
  have args:=state.rows.read source data.array data.pointers data.lengths data.count data.lower data.upper index inside state.arena.domain state.arrayCell state.indexCell
  have reads:=Input.ArgumentValues.pair_reads source (.load .one row) (.load .one rowLength) (.val (.word (data.pointers index))) (.val (.word (data.lengths index))) args
  have outputRead : eval source hashCell=some (.val (.word (digestPointer data index))) := by
    simp [hashCell,localVar,eval,evalHOLExact,evalListHOLExact,toExact,state.hashesCell,state.indexCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,
      digestPointer,byteAddress,BitVec.ofNat_mul,Nat.mul_comm]
  simp only [eval] at reads outputRead
  simp [hashArguments,CurrentKeccak.Hash.values,evalListHOLFinite,evalListHOLExact,reads.1,reads.2,outputRead]

theorem hash_output_arena (data : Data) (layout : RoundLayout data) (index : Nat) (inside : index<data.count) :
    AllocatedBytes.Arena (digestPointer data index) 32 :=
  AllocatedBytes.Arena.subrange data.hashes (32*data.count+32) (32*index) 32 layout.hashes (by omega)

theorem hash_cost (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (layout : RoundLayout data) (inside : index<data.count) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak256") hashArguments)).2.clock≤
      44*((data.lengths index).toNat/136)+690 := by
  exact CurrentKeccak.Hash.call_cost source hashArguments (data.pointers index) (digestPointer data index) (data.lengths index).toNat
    (by have h:=layout.lengths index inside; omega) state.arena.code (hash_arguments_read data origin source index state inside)

end InitECandidate.Solver.Headers.CurrentValidate

#print axioms InitECandidate.Solver.Headers.CurrentValidate.hash_arguments_read
#print axioms InitECandidate.Solver.Headers.CurrentValidate.hash_cost
