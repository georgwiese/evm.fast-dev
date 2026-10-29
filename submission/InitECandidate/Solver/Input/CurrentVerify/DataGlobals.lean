import InitECandidate.Solver.Input.CurrentVerify.RunInputs

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- These are exactly the global cells used by the current verification
input contract. Block-hash and EVM globals may change independently. -/
def dataGlobals : List MlS := [ofString "scratch_ptr",ofString "frame_mem_ptr",ofString "heap_ptr",ofString "keccak_st",ofString "keccak_pad",ofString "mpt_hash_scratch"]

theorem Data.with_globals {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (globals : HolFiniteMapExact MlS (ValueHOL 64))
    (kept : ∀ key∈dataGlobals,globals.lookup key=source.globals.lookup key) :
    Data input {source with globals:=globals} pointer si record gasWord boundary := by
  have arena : CurrentStartup.ArenaState {source with globals:=globals} :=
    ⟨(kept _ (by simp [dataGlobals])).trans data.arena.scratch,
      (kept _ (by simp [dataGlobals])).trans data.arena.frame,data.arena.domain,data.arena.code⟩
  have environment : CurrentKeccak.Hash.Environment {source with globals:=globals} 2701132160#64 2701132360#64 :=
    ⟨data.arena.code,data.keccak.domain,(kept _ (by simp [dataGlobals])).trans data.keccak.stateGlobal,
      (kept _ (by simp [dataGlobals])).trans data.keccak.padGlobal,
      data.keccak.stateArena,data.keccak.padArena,data.keccak.stateAligned,data.keccak.padAligned⟩
  obtain ⟨heap,cell,lower,upper,aligned⟩:=data.heap
  have nextHeap : NormalHeapEffects.AtLeast (boundary+32) {source with globals:=globals} :=
    ⟨heap,(kept _ (by simp [dataGlobals])).trans cell,lower,upper,aligned⟩
  obtain ⟨nodes,codes,headers,nodeStart,nodeLength,codeStart,codeLength,headerStart,headerLength,nodeImage,codeImage,headerImage⟩:=data.witnesses
  have memory (query : BitVec 64) (_low : 2701134824≤query.toNat) (_high : query.toNat<boundary) :
      ({source with globals:=globals} : PanSemStateFiniteExact 64 Guest.HostMemory).memory query=source.memory query := rfl
  exact ⟨arena,data.little,environment,(kept _ (by simp [dataGlobals])).trans data.mptHash,nextHeap,data.siLocal,data.siArena,data.siAligned,data.recordArena,data.recordAligned,data.recordInside,
    data.payloadCell,data.gasCell,data.gasBound,data.payload.of_interval (by intros; rfl) nextHeap,
    data.copied.of_interval boundary (by have before:=data.recordInside.2; omega) rfl rfl memory,nodes,codes,headers,nodeStart,nodeLength,codeStart,codeLength,headerStart,headerLength,
    nodeImage.of_interval (by decide) memory,codeImage.of_interval (by decide) memory,headerImage.of_interval (by decide) memory⟩

/-- An observed normal assignment to an unrelated global preserves the
complete physical input contract and the original SI binding. -/
theorem Data.global_assign {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary) (key : MlS) (expression : ExpHOL 64)
    (unrelated : key∉dataGlobals)
    (normal : evaluateHOLFiniteState source (.assign .global key expression)=(none,target)) :
    Data input target pointer si record gasWord boundary := by
  rw [evaluateHOLFiniteState_assign] at normal
  split at normal
  · cases normal
  · split at normal
    · have endpoint:=congrArg Prod.snd normal
      dsimp only at endpoint
      rw [←endpoint]
      apply data.with_globals
      intro protectedKey member
      have different : key≠protectedKey := by intro equal; apply unrelated; rw [equal]; exact member
      simp [HolFiniteMapExact.update,FUPDATE,different]
    · cases normal

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.Data.with_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.Data.global_assign
