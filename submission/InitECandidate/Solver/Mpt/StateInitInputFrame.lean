import InitECandidate.Solver.Mpt.StateInitBoundaryNormal
import InitECandidate.Solver.Input.MainStateInitCallerInput

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open Input.Main.RunAttemptConstructors WitnessCore

/-- Compose the actual header/table frontier and normal initializer frame
on the original decoded region. The source heap cell identifies the real
workspace base; its separation is derived from the actual prefix. -/
theorem Output.input_frame (input : Guest.InputBlob)
    (origin caller source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (workspace nodes rootHash codes root : BitVec 64)
    (output : Output input source post workspace nodes rootHash codes)
    (workspaceCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word workspace)))
    (prefixInput : CallerInput caller source root)
    (before : root.toNat≤(initialHeap root).toNat)
    (original : Input.HashInput.Frame origin caller Input.Main.inputPointer.toNat root.toNat) :
    Input.HashInput.Frame origin post Input.Main.inputPointer.toNat root.toNat := by
  obtain ⟨heap,heapCell,heapBefore⟩:=prefixInput.heap
  have same : heap=workspace:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (heapCell.symm.trans workspaceCell)))
  rw [same] at heapBefore
  obtain ⟨installed,scalars,scratch,globals,code,domain,endian,oracle,finalHeap,trieRoot,storage,finalCell,arena,aligned,view,frozen,table,bs,
    registry,member,regions,block,older,workspaceBefore⟩:=output
  constructor
  intro query lower upper
  have fromInitializer:=older query (by change 2713731432≤query.toNat at lower; omega) (by omega)
  have fromPrefix:=prefixInput.memory.words query lower (by omega)
  exact fromInitializer.trans (fromPrefix.trans (original.words query lower upper))

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.Output.input_frame
