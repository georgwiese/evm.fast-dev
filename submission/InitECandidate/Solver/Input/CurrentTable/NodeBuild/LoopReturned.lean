import InitECandidate.Solver.Input.CurrentTable.NodeBuild.Initialized
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.Input.CurrentTable.NodeBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- Physical loop result after the original return and lexical restoration.
The returned function's local map is deliberately not an entry invariant. -/
structure LoopReturned (data : Data) (origin post : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  arena : CurrentStartup.ArenaState post
  little : post.be=false
  environment : CurrentKeccak.Hash.Environment post data.stp data.pad
  outCell : post.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word data.out))
  heap : NormalHeapEffects.AtLeast (New.endPointer data.table data.cap).toNat post
  input : HashInput.Frame origin post data.lower data.upper
  globals : ∀ key,post.globals.lookup key=origin.globals.lookup key
  image : ImageUpTo data post data.total

/-- A normal whole continuation passes through the same actual loop and
returns the genuine allocated table; it cannot use a stopped-cost shortcut. -/
theorem table_tail_returned (data : Data) (source target post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (returned : New.Returned source target data.table data.cap data.stp data.pad)
    (layout : Layout data) (little : source.be=false)
    (rows : Headers.Validate.Rows source data.array data.pointers data.lengths data.total data.lower data.upper)
    (outCell : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word data.out)))
    (arrayCell : source.locals.lookup (ofString "slice_arr")=some (.val (.word data.array)))
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 data.total))))
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState (CallNormal.continuationEntry source target "t" (.val (.word data.table))) tableTail=(some (.returned value),post)) :
    value=.val (.word data.table) ∧ LoopReturned data (loopEntry data source target) post := by
  let ready := CallNormal.continuationEntry source target "t" (.val (.word data.table))
  rw [table_tail_shape] at run
  obtain ⟨inner,continued,endpoint⟩ := declaration_return_word ready post "i" (.const 0#64) 0#64 (.seq loop returnTable) value rfl run
  have initial := initialized data source target returned layout little rows outCell arrayCell countCell
  have safe : LocalPrefix (ofString "n") loop := .loop condition iteration_local
  obtain ⟨finish,loopRun,returnRun⟩ := sequence_returned (loopEntry data source target) inner loop returnTable value
    (safe.summary_full (loopEntry data source target)).2.1 continued
  obtain ⟨index,bounded,state⟩ := loop_normal data (loopEntry data source target) (loopEntry data source target) finish 0 initial layout (by omega) loopRun
  obtain ⟨valueRead,returnEndpoint⟩ := return_normal finish inner (localVar "t") value returnRun
  have actualRead : eval finish (localVar "t")=some (.val (.word data.table)) := by
    simp [eval,evalHOLExact,toExact,localVar,state.tableCell]
  have valueEq := Option.some.inj (valueRead.symm.trans actualRead)
  have physical : LocalEffects.erase post=LocalEffects.erase finish := by rw [endpoint,returnEndpoint]; rfl
  have memory := LocalEffects.memory_of_erase finish post physical
  have globals := congrArg PanSemStateFiniteExact.globals physical
  have endian := congrArg PanSemStateFiniteExact.be physical
  change post.globals=finish.globals at globals
  change post.be=finish.be at endian
  obtain ⟨heap,heapCell,heapLower,heapUpper,heapAligned⟩ := state.heap
  obtain ⟨root,next,count,valid,bits,left,right,keys,image,countBound⟩ := state.image
  exact ⟨valueEq,⟨state.arena.of_frame physical,endian.trans state.little,state.environment.of_frame physical,
    (by rw [globals]; exact state.outCell),
    ⟨heap,(by rw [globals]; exact heapCell),heapLower,heapUpper,heapAligned⟩,
    ⟨by intro query lower upper; exact (congrFun memory query).trans (state.input.words query lower upper)⟩,
    (fun key=>(congrArg (fun table=>table.lookup key) globals).trans (state.globals key)),
    root,next,count,valid,bits,left,right,keys,image.of_frame physical,by omega⟩⟩

end InitECandidate.Solver.Input.CurrentTable.NodeBuild

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.table_tail_returned
