import InitECandidate.Solver.Input.MainMptWorkspace
import InitECandidate.Solver.Input.ConstructorRuntimeFrame
import InitECandidate.Solver.Mpt.StateInitNormal

namespace InitECandidate.Solver.Input.Main.MptWorkspace
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def Bindings (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop:=
  ∀ field : Field,source.globals.lookup field.name=some (.val (.word field.pointer))

theorem after_hash_bindings (input : Guest.InputBlob) (before copiedSource origin current : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (copied : InputCopied input before copiedSource)
    (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) origin)
    (returned : RequestHash.Returned input origin current root) : Bindings current :=
  after_hash_value input before copiedSource origin current root copied actual returned

theorem Bindings.of_erase (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (bindings : Bindings source)
    (same : LocalEffects.erase target=LocalEffects.erase source) : Bindings target := by
  intro field
  have globals:=congrArg (fun state=>state.globals.lookup field.name) same
  exact globals.trans (bindings field)

theorem Bindings.of_heap_globals (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (bindings : Bindings source)
    (same : HeapGlobals source target) : Bindings target := by
  intro field
  exact (same field.name field.not_heap).trans (bindings field)

theorem Bindings.of_constructor (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (bindings : Bindings source)
    (same : ConstructorRuntimeFrame source target) : Bindings target := by
  intro field
  exact (same.globals field.name field.not_heap (by cases field <;> decide) (by cases field <;> decide)).trans (bindings field)

theorem Bindings.of_state_init (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (workspace nodes rootHash codes : BitVec 64) (bindings : Bindings source)
    (output : Mpt.StateInit.Output input source target workspace nodes rootHash codes) : Bindings target := by
  intro field
  have kept:=output.2.2.2.1 field.name field.not_heap
    (by cases field <;> decide) (by cases field <;> decide) (by cases field <;> decide)
    (by cases field <;> decide) (by cases field <;> decide) (by cases field <;> decide) (by cases field <;> decide)
  exact kept.trans (bindings field)

theorem Bindings.at_callee (source : PanSemStateFiniteExact 64 Guest.HostMemory) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (bindings : Bindings source) : Bindings (callEntryStateHOLFinite source callee) := bindings

end InitECandidate.Solver.Input.Main.MptWorkspace

#print axioms InitECandidate.Solver.Input.Main.MptWorkspace.after_hash_bindings
#print axioms InitECandidate.Solver.Input.Main.MptWorkspace.Bindings.of_erase
#print axioms InitECandidate.Solver.Input.Main.MptWorkspace.Bindings.of_heap_globals
#print axioms InitECandidate.Solver.Input.Main.MptWorkspace.Bindings.of_constructor
#print axioms InitECandidate.Solver.Input.Main.MptWorkspace.Bindings.of_state_init
#print axioms InitECandidate.Solver.Input.Main.MptWorkspace.Bindings.at_callee
