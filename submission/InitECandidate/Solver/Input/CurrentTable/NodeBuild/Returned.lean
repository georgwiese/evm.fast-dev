import InitECandidate.Solver.Input.CurrentTable.NodeBuild.Entry
import InitECandidate.Solver.Input.CurrentTable.NodeBuild.CapacityNormal
import InitECandidate.Solver.Input.CurrentTable.NodeBuild.LoopReturned

namespace InitECandidate.Solver.Input.CurrentTable.NodeBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- Real physical result of a complete current node/code database builder. -/
structure Returned (data : Data) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap : BitVec 64) : Prop where
  arena : CurrentStartup.ArenaState post
  little : post.be=false
  environment : CurrentKeccak.Hash.Environment post data.stp data.pad
  outCell : post.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word data.out))
  heap : NormalHeapEffects.AtLeast (New.endPointer table cap).toNat post
  input : HashInput.Frame source post data.lower data.upper
  globals : ∀ key,key≠ofString "heap_ptr" → post.globals.lookup key=source.globals.lookup key
  image : ImageUpTo {data with table:=table,cap:=cap} post data.total
  tableAfter : data.upper≤table.toNat
  totalBound : data.total≤1048575

/-- A genuine normal whole-builder return supplies its actual allocated
Patricia image, record-value membership, advanced heap and protected input.
All prefixes come from the same run, at every incoming source clock. -/
theorem body_returned (data : Data) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry data source) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ table cap,value=.val (.word table) ∧ Returned data source post table cap := by
  obtain ⟨selected,inner,bits,bitsLower,bitsUpper,sufficient,capBound,capCell,same,price,others,allocatedRun,endpoint⟩ :=
    capacity_returned source post data.total entry.totalSmall entry.countCell value run
  have ready := entry.of_frame same ((others (ofString "slice_arr") (by decide)).trans entry.arrayCell)
    ((others (ofString "n") (by decide)).trans entry.countCell)
  obtain ⟨heap,heapCell,heapLower,heapBound,heapAligned⟩ := ready.workspace.heap
  let cap := BitVec.ofNat 64 (2^bits)
  have capNumber : cap.toNat=2^bits := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))]
  have capLow : 2≤cap.toNat := by
    rw [capNumber]
    have h := Nat.pow_le_pow_right (by decide : 0<2) bitsLower
    change 4≤2^bits at h
    omega
  have capSmall : cap.toNat≤2^32 := by rw [capNumber]; exact Nat.pow_le_pow_right (by decide) bitsUpper
  have context : New.Context selected heap cap data.stp data.pad :=
    ⟨ready.workspace.arena,ready.workspace.environment,heapCell,by have := ready.workspace.lowerDomain; omega,heapBound,heapAligned,capLow,capSmall⟩
  have args : evalListHOLFinite selected (h:=fun query=>Classical.propDecidable (selected.memaddrs query)) tableArguments=
      some [.val (.word 32#64),.val (.word cap)] := by
    simp [tableArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,capCell,cap]
  rw [table_shape] at allocatedRun
  obtain ⟨target,loopPost,constructor,forward,cost,tableRun,restored⟩ := New.scoped_returned selected inner heap cap data.stp data.pad context
    "t" tableArguments tableTail args value allocatedRun
  let currentData : Data := {data with table:=heap,cap:=cap}
  have layout : Layout currentData := ready.at_table heap cap (by rw [capNumber]; exact sufficient) heapLower
  obtain ⟨answer,result⟩ := table_tail_returned currentData selected target loopPost constructor layout ready.little ready.rows ready.outCell ready.arrayCell ready.countCell value tableRun
  have physical : LocalEffects.erase post=LocalEffects.erase loopPost := by rw [endpoint,restored]; rfl
  have memory := LocalEffects.memory_of_erase loopPost post physical
  have globals := congrArg PanSemStateFiniteExact.globals physical
  have endian := congrArg PanSemStateFiniteExact.be physical
  change post.globals=loopPost.globals at globals
  change post.be=loopPost.be at endian
  have oldMemory := LocalEffects.memory_of_erase source selected same
  have oldGlobals := congrArg PanSemStateFiniteExact.globals same
  change selected.globals=source.globals at oldGlobals
  obtain ⟨powerBound,totalBound⟩ := New.power_capacity heap cap constructor.geometry bits data.total bitsUpper rfl sufficient
  obtain ⟨cursor,cursorCell,cursorLower,cursorUpper,cursorAligned⟩ := result.heap
  obtain ⟨root,next,count,valid,nodeBits,left,right,keys,image,countBound⟩ := result.image
  refine ⟨heap,cap,answer,?_,?_,?_,?_,?_,?_,?_,?_,heapLower,totalBound⟩
  · exact result.arena.of_frame physical
  · exact endian.trans result.little
  · exact result.environment.of_frame physical
  · rw [globals]; exact result.outCell
  · exact ⟨cursor,by rw [globals]; exact cursorCell,cursorLower,cursorUpper,cursorAligned⟩
  · refine ⟨?_⟩
    intro query lower upper
    exact (congrFun memory query).trans ((result.input.words query lower upper).trans
      ((constructor.earlier query (by omega)).trans (congrFun oldMemory query)))
  · intro key different
    exact (congrArg (fun table=>table.lookup key) globals).trans ((result.globals key).trans
      ((constructor.globals key different).trans (congrArg (fun table=>table.lookup key) oldGlobals)))
  · exact ⟨root,next,count,valid,nodeBits,left,right,keys,image.of_frame physical,countBound⟩

end InitECandidate.Solver.Input.CurrentTable.NodeBuild

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.body_returned
