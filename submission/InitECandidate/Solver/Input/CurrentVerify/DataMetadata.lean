import InitECandidate.Solver.Input.CurrentVerify.RunInputs
import InitECandidate.Solver.PanHeapGlobals
import InitECandidate.Solver.Input.UDivMod.CurrentFrame

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Transport current main inputs through an actual writer that retains
runtime/global metadata and all earlier decoded cells. Fresh later memory
may change freely; the caller's actual si binding is tracked separately. -/
theorem Data.of_metadata {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary)
    (frame : MemoryMetadata.erase target=MemoryMetadata.erase source)
    (siLocal : target.locals.lookup (ofString "si")=some (.val (.word si)))
    (memory : ∀ query : BitVec 64,2701134824≤query.toNat→query.toNat<boundary→target.memory query=source.memory query) :
    Data input target pointer si record gasWord boundary := by
  have domain:=MemoryMetadata.domain frame
  have endian:=MemoryMetadata.endian frame
  have code:=MemoryMetadata.code frame
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  change target.globals=source.globals at globals
  have arena : CurrentStartup.ArenaState target:=⟨by rw [globals]; exact data.arena.scratch,
    by rw [globals]; exact data.arena.frame,domain.trans data.arena.domain,by rw [code]; exact data.arena.code⟩
  have environment : CurrentKeccak.Hash.Environment target 2701132160#64 2701132360#64:=
    ⟨by rw [code]; exact data.keccak.installed,domain.trans data.keccak.domain,
      by rw [globals]; exact data.keccak.stateGlobal,by rw [globals]; exact data.keccak.padGlobal,
      data.keccak.stateArena,data.keccak.padArena,data.keccak.stateAligned,data.keccak.padAligned⟩
  obtain ⟨cursor,cell,lower,upper,aligned⟩:=data.heap
  have heap : NormalHeapEffects.AtLeast (boundary+32) target:=⟨cursor,by rw [globals]; exact cell,lower,upper,aligned⟩
  exact data.of_interval arena (endian.trans data.little) environment (by rw [globals]; exact data.mptHash) (by rw [globals]; exact data.mptKey) (by rw [globals]; exact data.mptEmpty) (by rw [globals]; exact data.shaState) (by rw [globals]; exact data.shaPad) (by rw [globals]; exact data.u256) heap siLocal memory

/-- Transport current decoded inputs through a same-execution heap
advance and bounded fresh writes. Every other global is retained; actual
new heap bounds and caller SI binding are supplied by that normal call. -/
theorem Data.of_heap_frame {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be) (code : target.code=source.code)
    (globals : HeapGlobals source target) (heap : NormalHeapEffects.AtLeast (boundary+32) target)
    (siLocal : target.locals.lookup (ofString "si")=some (.val (.word si)))
    (memory : ∀ query : BitVec 64,2701134824≤query.toNat→query.toNat<boundary→target.memory query=source.memory query) :
    Data input target pointer si record gasWord boundary := by
  have arena : CurrentStartup.ArenaState target:=
    ⟨(globals _ (by decide)).trans data.arena.scratch,(globals _ (by decide)).trans data.arena.frame,
      domain.trans data.arena.domain,by rw [code]; exact data.arena.code⟩
  have environment : CurrentKeccak.Hash.Environment target 2701132160#64 2701132360#64:=
    ⟨by rw [code]; exact data.keccak.installed,domain.trans data.keccak.domain,
      (globals _ (by decide)).trans data.keccak.stateGlobal,(globals _ (by decide)).trans data.keccak.padGlobal,
      data.keccak.stateArena,data.keccak.padArena,data.keccak.stateAligned,data.keccak.padAligned⟩
  exact data.of_interval arena (endian.trans data.little) environment
    ((globals _ (by decide)).trans data.mptHash) ((globals _ (by decide)).trans data.mptKey) ((globals _ (by decide)).trans data.mptEmpty)
    ((globals _ (by decide)).trans data.shaState) ((globals _ (by decide)).trans data.shaPad) ((globals _ (by decide)).trans data.u256)
    heap siLocal memory

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.Data.of_metadata

#print axioms InitECandidate.Solver.Input.CurrentVerify.Data.of_heap_frame


namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack PanSemStateFiniteExact

/-- The same reached main data supplies the real mapped u256 workspace. -/
theorem Data.u256_workspace {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary) :
    UDivMod.WideDigits.Workspace.Context source 2701134824#64 :=
  UDivMod.WideDigits.Workspace.current source data.u256 data.arena.domain

/-- The complete allocated workspace is before the copied input, stateless
record and payload record, all from their actual startup/decoder ownership. -/
theorem Data.workspace_separation {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary) :
    2701134824+640≤pointer.toNat ∧ 2701134824+640≤si.toNat ∧ 2701134824+640≤record.toNat := by
  have inputLower:=data.inputAfterWorkspace
  have siAfter:=data.siAfterInput
  have recordAfter:=data.copied.beforeRecord
  omega

theorem Data.workspace_slot_before_input {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary)
    (buffer : UDivMod.WideDigits.Workspace.Buffer) (index : Nat) (inside : index<UDivMod.WideDigits.Workspace.count buffer) :
    (UDivMod.WideDigits.slot (UDivMod.WideDigits.Workspace.pointer 2701134824#64 buffer) index).toNat+8≤pointer.toNat := by
  have location:=UDivMod.WideDigits.Workspace.slot_number source 2701134824#64 data.u256_workspace buffer index inside
  have extent:=UDivMod.WideDigits.Workspace.fits buffer
  have lower:=data.inputAfterWorkspace
  change (UDivMod.WideDigits.slot (UDivMod.WideDigits.Workspace.pointer 2701134824#64 buffer) index).toNat=
    2701134824+UDivMod.WideDigits.Workspace.offset buffer+8*index at location
  omega

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.Data.u256_workspace
#print axioms InitECandidate.Solver.Input.CurrentVerify.Data.workspace_separation
#print axioms InitECandidate.Solver.Input.CurrentVerify.Data.workspace_slot_before_input
