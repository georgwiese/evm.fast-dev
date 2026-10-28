import InitECandidate.Solver.Input.CurrentTable.NodeBuild.LoopState
import InitECandidate.Solver.CurrentKeccak.Cost
import InitECandidate.Solver.Input.LoadWord

namespace InitECandidate.Solver.Input.CurrentTable.NodeBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- The real builder's slice_arr/i address selects this actual record. -/
theorem row_read (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : State data origin source index) :
    eval source row=some (.val (.word (byteAddress data.array (16*index)))) := by
  simp [row,eval,evalHOLExact,evalListHOLExact,toExact,localVar,state.arrayCell,state.indexCell,
    valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,byteAddress,BitVec.ofNat_mul,Nat.mul_comm]

theorem hash_arguments (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : State data origin source index) (inside : index<data.total) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) hashArguments=
      some (CurrentKeccak.Hash.values (data.pointers index) data.out (data.lengths index).toNat) := by
  have firstMapped := AllocatedBytes.word_mapped source (byteAddress data.array (16*index)) 16 0 state.arena.domain
    (state.rows.rowArena index inside) (by decide) (state.rows.rowAligned index inside) (by decide)
  have secondMapped := AllocatedBytes.word_mapped source (byteAddress data.array (16*index)) 16 8 state.arena.domain
    (state.rows.rowArena index inside) (by decide) (state.rows.rowAligned index inside) (by decide)
  have first := Witness.load_word_read source row (byteAddress data.array (16*index)) (data.pointers index) (row_read data origin source index state)
    (by simpa [byteAddress] using firstMapped) (state.rows.cells index inside).1
  have addressRead : eval source (.op .add [localVar "slice_arr",.panop .mul [localVar "i",.const 16#64],.const 8#64])=
      some (.val (.word (byteAddress data.array (16*index)+8#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,state.arrayCell,state.indexCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,byteAddress,BitVec.ofNat_mul,Nat.mul_comm,BitVec.add_assoc]
  have second := Witness.load_word_read source _ (byteAddress data.array (16*index)+8#64) (data.lengths index) addressRead
    secondMapped (state.rows.cells index inside).2
  have outputRead : eval source (.var .global (ofString "mpt_hash_scratch"))=some (.val (.word data.out)) := by
    simp [eval,evalHOLExact,toExact,state.outCell]
  simp only [eval] at first second outputRead
  simp [hashArguments,CurrentKeccak.Hash.values,evalListHOLFinite,evalListHOLExact,first,second,outputRead]

theorem set_arguments (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : State data origin source index) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) setArguments=
      some [.val (.word data.table),.val (.word data.out),.val (.word (byteAddress data.array (16*index)))] := by
  have rowRead := row_read data origin source index state
  simp only [eval] at rowRead
  simp [setArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,state.tableCell,state.outCell,rowRead]

theorem hash_cost (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : State data origin source index) (layout : Layout data) (inside : index<data.total) :
    source.clock-(evaluateHOLFiniteState source hashCall).2.clock≤44*((data.lengths index).toNat/136)+690 := by
  exact CurrentKeccak.Hash.call_cost source hashArguments (data.pointers index) data.out (data.lengths index).toNat
    (by have := layout.lengths index inside; have := layout.itemSmall; omega) state.arena.code (hash_arguments data origin source index state inside)

end InitECandidate.Solver.Input.CurrentTable.NodeBuild

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.row_read
#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.hash_arguments
#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.set_arguments
#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.hash_cost
