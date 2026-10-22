import InitECandidate.Solver.Mpt.IndexedCounter
import InitECandidate.Solver.Mpt.IndexedSetup
import InitECandidate.Solver.Input.MptWorkspaceBindings

namespace InitECandidate.Solver.Mpt.Indexed
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem loop_entry_bindings (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (bindings : Input.Main.MptWorkspace.Bindings source) :
    Input.Main.MptWorkspace.Bindings (loopEntry source heap) :=
  Input.Main.MptWorkspace.Bindings.of_heap_globals source (loopEntry source heap) bindings (loop_entry_globals source heap)

/-- The original startup allocation supplies the complete mapped key buffer;
no successful future encoder call is assumed. -/
theorem key_buffer_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (domain : source.memaddrs=InitE.ordinaryDomain) :
    ∀ index<9,source.memaddrs (panByteAlignHOL (width:=64) (2713717624#64+BitVec.ofNat 64 index)) := by
  intro index inside
  exact AllocatedBytes.byte_mapped source 2713717624#64 16 index domain
    Input.Main.MptWorkspace.Field.key.geometry.1 (by omega)

theorem key_backing_bounds (index : Nat) (inside : index<9) :
    2713717624≤(panByteAlignHOL (width:=64) (2713717624#64+BitVec.ofNat 64 index)).toNat ∧
    (panByteAlignHOL (width:=64) (2713717624#64+BitVec.ofNat 64 index)).toNat<2713717640 := by
  have number:=byteAddress_toNat 2713717624#64 index (by change 2713717624+index<2^64; omega)
  change (2713717624#64+BitVec.ofNat 64 index).toNat=2713717624+index at number
  rw [AllocatedBytes.aligned_number,number]
  omega

theorem key_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : BitVec 64)
    (bindings : Input.Main.MptWorkspace.Bindings source)
    (i : source.locals.lookup (ofString "i")=some (.val (.word index))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) keyArguments=
      some [.val (.word 2713717624#64),.val (.word index)] := by
  have key:=bindings .key
  change source.globals.lookup (ofString "mpt_key_scratch")=some (.val (.word 2713717624#64)) at key
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,keyArguments,localVar,key,i]

end InitECandidate.Solver.Mpt.Indexed

#print axioms InitECandidate.Solver.Mpt.Indexed.loop_entry_bindings
#print axioms InitECandidate.Solver.Mpt.Indexed.key_buffer_mapped
#print axioms InitECandidate.Solver.Mpt.Indexed.key_backing_bounds
#print axioms InitECandidate.Solver.Mpt.Indexed.key_arguments
