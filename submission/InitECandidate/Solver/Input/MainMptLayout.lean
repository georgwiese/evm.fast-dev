import InitECandidate.Solver.Input.MainMptProgram

namespace InitECandidate.Solver.Input.Main.MptInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

structure Layout (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) : Prop where
  root : source.globals.lookup (ofString "empty_trie_root") = some (.val (.word (BitVec.ofNat 64 cursor)))
  hash : source.globals.lookup (ofString "empty_code_hash") = some (.val (.word (BitVec.ofNat 64 (cursor + 32))))
  nibbles : source.globals.lookup (ofString "mpt_nib_scratch") = some (.val (.word (BitVec.ofNat 64 (cursor + 64))))
  scratch : source.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word (BitVec.ofNat 64 (cursor + 128))))
  key : source.globals.lookup (ofString "mpt_key_scratch") = some (.val (.word (BitVec.ofNat 64 (cursor + 168))))

theorem layout (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) : Layout (allocated source cursor) cursor := by
  constructor
  all_goals simp [allocated,actions,InitializerAllocations.template,InitializerAllocations.reserve,InitializerAllocations.constant,putGlobal,HolFiniteMapExact.update,FUPDATE,
    show ofString "mpt_key_scratch" ≠ ofString "mpt_hash_scratch" by decide,show ofString "mpt_key_scratch" ≠ ofString "mpt_nib_scratch" by decide,
    show ofString "mpt_key_scratch" ≠ ofString "empty_code_hash" by decide,show ofString "mpt_key_scratch" ≠ ofString "empty_trie_root" by decide,
    show ofString "mpt_hash_scratch" ≠ ofString "mpt_nib_scratch" by decide,show ofString "mpt_hash_scratch" ≠ ofString "empty_code_hash" by decide,
    show ofString "mpt_hash_scratch" ≠ ofString "empty_trie_root" by decide,show ofString "mpt_nib_scratch" ≠ ofString "empty_code_hash" by decide,
    show ofString "mpt_nib_scratch" ≠ ofString "empty_trie_root" by decide,show ofString "empty_code_hash" ≠ ofString "empty_trie_root" by decide,
    show ofString "heap_ptr" ≠ ofString "empty_trie_root" by decide,show ofString "heap_ptr" ≠ ofString "empty_code_hash" by decide,
    show ofString "heap_ptr" ≠ ofString "mpt_nib_scratch" by decide,show ofString "heap_ptr" ≠ ofString "mpt_hash_scratch" by decide,
    show ofString "heap_ptr" ≠ ofString "mpt_key_scratch" by decide]

theorem Layout.of_globals (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (model : Layout source cursor) (globals : post.globals = source.globals) : Layout post cursor := by
  constructor
  · rw [globals]; exact model.root
  · rw [globals]; exact model.hash
  · rw [globals]; exact model.nibbles
  · rw [globals]; exact model.scratch
  · rw [globals]; exact model.key

theorem arenas (cursor : Nat) (lower : 2701131776 ≤ cursor) (room : cursor + 184 ≤ 33806089496) (aligned : cursor % 8 = 0) :
    AllocatedBytes.Arena (BitVec.ofNat 64 cursor) 32 ∧ AllocatedBytes.Arena (BitVec.ofNat 64 (cursor + 32)) 32 ∧
    AllocatedBytes.Arena (BitVec.ofNat 64 (cursor + 128)) 40 ∧ (BitVec.ofNat 64 (cursor + 128)).toNat % 8 = 0 := by
  have number (offset : Nat) (inside : offset ≤ 184) : (BitVec.ofNat 64 (cursor + offset)).toNat = cursor + offset := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have zero : (BitVec.ofNat 64 cursor).toNat = cursor := by simpa using number 0 (by decide)
  exact ⟨⟨by rw [zero]; exact lower,by rw [zero]; omega⟩,⟨by rw [number 32 (by decide)]; omega,by rw [number 32 (by decide)]; omega⟩,
    ⟨by rw [number 128 (by decide)]; omega,by rw [number 128 (by decide)]; omega⟩,by rw [number 128 (by decide)]; omega⟩

theorem seed_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor)
    (room : cursor + 184 ≤ 33806089496) (aligned : cursor % 8 = 0) :
    evaluateHOLFiniteState (allocated source cursor) seed = (none,seeded source cursor) := by
  have current := layout source cursor
  obtain ⟨_,_,arena,_⟩ := arenas cursor lower room aligned
  have mapped := AllocatedBytes.byte_mapped (allocated source cursor) (BitVec.ofNat 64 (cursor + 128)) 40 0 domain arena (by decide)
  apply ByteStore.execute _ _ _ _ 128#8
  · simp [WitnessRadix.QueryBranch.eval,evalHOLExact,toExact,current.scratch]
  · rfl
  · simpa [byteAddress] using mapped

theorem allocated_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat) :
    allocated {source with clock := clock} cursor = {allocated source cursor with clock := clock} :=
  InitializerAllocations.template_clock source cursor actions clock

theorem seeded_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat) :
    seeded {source with clock := clock} cursor = {seeded source cursor with clock := clock} := by
  unfold seeded
  rw [allocated_clock]

theorem allocated_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (key : MlS)
    (notHeap : key ≠ ofString "heap_ptr") (notRoot : key ≠ ofString "empty_trie_root") (notHash : key ≠ ofString "empty_code_hash")
    (notNibs : key ≠ ofString "mpt_nib_scratch") (notScratch : key ≠ ofString "mpt_hash_scratch") (notKey : key ≠ ofString "mpt_key_scratch") :
    (allocated source cursor).globals.lookup key = source.globals.lookup key := by
  apply InitializerAllocations.template_other source cursor actions key notHeap
  intro action member
  simp only [actions,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact notRoot
  · exact notHash
  · exact notNibs
  · exact notScratch
  · exact notKey

theorem allocated_environment (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (stp pad : BitVec 64)
    (installed : OriginalCode.Installed source.code) (environment : Keccak256.Environment source stp pad) :
    Keccak256.Environment (allocated source cursor) stp pad :=
  Keccak256.original_environment (allocated source cursor) stp pad installed environment.domain environment.hashCode.oracleEq
    ((allocated_other source cursor (ofString "keccak_st") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans environment.stateGlobal)
    ((allocated_other source cursor (ofString "keccak_pad") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans environment.scratchGlobal)

end InitECandidate.Solver.Input.Main.MptInitialization

#print axioms InitECandidate.Solver.Input.Main.MptInitialization.layout
#print axioms InitECandidate.Solver.Input.Main.MptInitialization.Layout.of_globals
#print axioms InitECandidate.Solver.Input.Main.MptInitialization.arenas
#print axioms InitECandidate.Solver.Input.Main.MptInitialization.seed_execute
#print axioms InitECandidate.Solver.Input.Main.MptInitialization.allocated_clock
#print axioms InitECandidate.Solver.Input.Main.MptInitialization.seeded_clock
#print axioms InitECandidate.Solver.Input.Main.MptInitialization.allocated_other
#print axioms InitECandidate.Solver.Input.Main.MptInitialization.allocated_environment
