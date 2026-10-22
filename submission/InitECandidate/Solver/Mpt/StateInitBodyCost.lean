import InitECandidate.Solver.Mpt.StateInitSuffixCost
import InitECandidate.Solver.Mpt.StateInitAllocationTrace
import InitECandidate.Solver.Mpt.StateInitReadyRuntime
import InitECandidate.Solver.Mpt.StateInitReadyHeap
import InitECandidate.Solver.Input.RootDecoderCost

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open Input.Main.RunAttemptConstructors

/-- Workspace initialization retains the genuine input databases and
advances their current before-heap witnesses to its actual next cursor. -/
theorem ready_boundary (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap nodes root codes : BitVec 64) (boundary : StateInitBoundary input source)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (arena : AllocatedBytes.Arena heap 40) (aligned : heap.toNat%8=0) :
    StateInitBoundary input (ready source heap nodes root codes):=by
  obtain ⟨array,nodeTable,codeTable,current,nodeData,codeData,nodeCell,codeCell,currentCell,currentArena,currentAligned,nodeBefore,codeBefore⟩:=boundary
  have same : current=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (currentCell.symm.trans heapCell)))
  subst current
  have nodeKept:=ready_database source heap nodes root codes _ nodeTable _ _ _ _ nodeData nodeBefore arena
  have codeKept:=ready_database source heap nodes root codes _ codeTable _ _ _ _ codeData codeBefore arena
  have geometry:=workspace_heap_geometry heap arena aligned
  have advance (table : BitVec 64) (before : MutableTable.WitnessBuild.BeforeHeap (ready source heap nodes root codes) table heap.toNat) :
      MutableTable.WitnessBuild.BeforeHeap (ready source heap nodes root codes) table (PersistentAlloc.rounded heap 40#64).toNat:=by
    obtain ⟨capacity,cell,bound⟩:=before
    exact ⟨capacity,cell,bound.trans geometry.2.2⟩
  exact ⟨array,nodeTable,codeTable,PersistentAlloc.rounded heap 40#64,nodeKept.1,codeKept.1,nodeCell,codeCell,
    (ready_fields source heap nodes root codes).2.2.1,geometry.1,geometry.2.1,advance nodeTable nodeKept.2,advance codeTable codeKept.2⟩

theorem root_call_cost (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (nodes root : BitVec 64) (boundary : StateInitBoundary input source)
    (installed : Input.OriginalCode.Installed source.code) (scalars : Input.OriginalScalarGlobals.Scalars source.globals)
    (nodeCell : source.locals.lookup (ofString "nodedb")=some (.val (.word nodes)))
    (rootCell : source.locals.lookup (ofString "state_root")=some (.val (.word root)))
    (scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64)
    (environment : Keccak256.Environment source 2713714976#64 2713715176#64) :
    source.clock-(evaluateHOLFiniteState source rootCall).2.clock≤rootDecoderPrice input+1759:=by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) rootArguments=some (WitnessDecodeRoot.values nodes root):=by
    simp [rootArguments,WitnessDecodeRoot.values,QueryBranch.localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,nodeCell,rootCell]
  obtain ⟨callee,called,dbCell,hashCell⟩:=WitnessDecodeRoot.environment source.code.lookup nodes root (WitnessDecodeRoot.original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have entryBoundary:=RootBoundary.of_state_init input source entry boundary rfl (dbCell.trans nodeCell.symm)
  have entryScratch:=scratch.of_fields source entry 2713714688#64 2701135872#64 rfl rfl
  have entryEnvironment:=Keccak256.Environment.of_fields source entry 2713714976#64 2713715176#64 environment rfl rfl rfl (by intro key other; rfl)
  have bodyCost:=root_decoder_cost input entry root entryBoundary installed scalars hashCell entryScratch entryEnvironment
  rw [shapes.2.2.2.2]
  have cost:=Input.ClockCost.scoped_current source (ofString "root") .one (ofString "decode_witness_to_mpt") rootArguments (WitnessDecodeRoot.values nodes root)
    WitnessDecodeRoot.body afterRoot callee .one (rootDecoderPrice input) 1758 args called bodyCost (after_root_cost source.code installed)
  omega

def bodyPrice (input : Guest.InputBlob) : Nat:=rootDecoderPrice input+1760

/-- Whole unchanged original322 on all outcomes. Only actual current input
databases, installed/scalar runtime and original scratch/hash workspace are
entry premises. No root-buffer mapping, allocation room or successful future
call is assumed. These are source clocks, not target instructions. -/
theorem body_cost (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (boundary : StateInitBoundary input source) (installed : Input.OriginalCode.Installed source.code)
    (scalars : Input.OriginalScalarGlobals.Scalars source.globals)
    (rootCell : source.locals.lookup (ofString "state_root")=some (.val (.word root)))
    (scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64)
    (environment : Keccak256.Environment source 2713714976#64 2713715176#64) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤bodyPrice input:=by
  have saved:=boundary
  obtain ⟨array,nodes,codes,heap,nodeData,codeData,nodeCell,codeCell,heapCell,heapArena,aligned,nodeBefore,codeBefore⟩:=boundary
  obtain ⟨oldWs,wsCell⟩:=scalars _ workspace_name
  let output:=evaluateHOLFiniteState source body
  rcases allocation_trace source output.2 heap oldWs nodes root codes installed wsCell heapCell nodeCell rootCell codeCell nodeData.domain
    heapArena.lower (by have upper:=heapArena.upper; omega) aligned output.1 rfl with stopped|reached
  · unfold bodyPrice; exact stopped.trans (by omega)
  · obtain ⟨funded,arena,remaining⟩:=reached
    let entered:=ready source heap nodes root codes
    have callerBoundary:=ready_boundary input source heap nodes root codes saved heapCell arena aligned
    have callerScalars:=ready_scalars source heap nodes root codes scalars
    have callerScratch:=ready_scratch source heap nodes root codes 2713714688#64 2701135872#64 scratch
    have callerEnvironment:=ready_environment source heap nodes root codes 2713714976#64 2713715176#64 environment
    have cost:=root_call_cost input entered nodes root callerBoundary installed callerScalars nodeCell rootCell callerScratch callerEnvironment
    rw [remaining] at cost
    change entered.clock-output.2.clock≤rootDecoderPrice input+1759 at cost
    have clock : entered.clock=source.clock-1:=rfl
    unfold bodyPrice
    change source.clock-output.2.clock≤rootDecoderPrice input+1760
    omega

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.ready_boundary
#print axioms InitECandidate.Solver.Mpt.StateInit.root_call_cost
#print axioms InitECandidate.Solver.Mpt.StateInit.body_cost
