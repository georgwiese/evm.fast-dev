import InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspaceCalls

namespace InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

private theorem zero_sha (action : InitializerAllocations.Action) (member : action ∈ shaActions) :
    ofString "zero_hashes" ≠ ofString action.name := by
  simp only [shaActions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide

private theorem zero_keccak (action : InitializerAllocations.Action) (member : action ∈ keccakActions) :
    ofString "zero_hashes" ≠ ofString action.name := by
  simp only [keccakActions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> decide

theorem ssz_template_offsets (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (InitializerAllocations.template source cursor sszActions).globals.lookup (ofString "ssz_offs") =
      some (.val (.word (BitVec.ofNat 64 (cursor + 32)))) := by
  simp [sszActions, InitializerAllocations.template, InitializerAllocations.reserve,
    InitializerAllocations.constant, putGlobal, HolFiniteMapExact.update, FUPDATE,
    show ofString "heap_ptr" ≠ ofString "ssz_offs" from by decide,
    show ofString "zero_hashes" ≠ ofString "ssz_offs" from by decide]

theorem ssz_template_chunk (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (InitializerAllocations.template source cursor sszActions).globals.lookup (ofString "ssz_len_chunk") =
      some (.val (.word (BitVec.ofNat 64 cursor))) := by
  simp [sszActions, InitializerAllocations.template, InitializerAllocations.reserve,
    InitializerAllocations.constant, putGlobal, HolFiniteMapExact.update, FUPDATE,
    show ofString "heap_ptr" ≠ ofString "ssz_len_chunk" from by decide,
    show ofString "zero_hashes" ≠ ofString "ssz_len_chunk" from by decide,
    show ofString "ssz_offs" ≠ ofString "ssz_len_chunk" from by decide]

theorem ssz_template_zeros (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (InitializerAllocations.template source cursor sszActions).globals.lookup (ofString "zero_hashes") =
      some (.val (.word (BitVec.ofNat 64 (cursor + 96)))) := by
  simp [sszActions, InitializerAllocations.template, InitializerAllocations.reserve,
    InitializerAllocations.constant, putGlobal, HolFiniteMapExact.update, FUPDATE, Nat.add_assoc,
    show ofString "heap_ptr" ≠ ofString "zero_hashes" from by decide]

/-- Derive the actual first SSZ workspace and heap cursor from the literal
first three startup calls. Every call is exposed from the observed completed
startup sequence; no supplied initializer return or future room is required. -/
theorem first_three (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "zero_hashes") = some (.val (.word 0#64)))
    (bounded : cursor ≤ 2952790016) (aligned : cursor % 8 = 0)
    (actual : evaluateHOLFiniteState source (withTail routines .skip) = (none, target)) :
    ∃ shaState keccakState sszState,
      evaluateHOLFiniteState source (.call (some (none, none)) (Code.name .sha256_init) []) = (none, shaState) ∧
      evaluateHOLFiniteState shaState (.call (some (none, none)) (Code.name .keccak_init) []) = (none, keccakState) ∧
      evaluateHOLFiniteState keccakState (.call (some (none, none)) (Code.name .ssz_init) []) = (none, sszState) ∧
      evaluateHOLFiniteState sszState (withTail (routines.drop 3) .skip) = (none, target) ∧
      OriginalCode.Installed sszState.code ∧ OriginalScalarGlobals.Scalars sszState.globals ∧
      sszState.globals.lookup (ofString "ssz_offs") = some (.val (.word (BitVec.ofNat 64 (cursor + 752)))) ∧
      sszState.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word (BitVec.ofNat 64 (cursor + 720)))) ∧
      sszState.globals.lookup (ofString "zero_hashes") = some (.val (.word (BitVec.ofNat 64 (cursor + 816)))) ∧
      sszState.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 2864)))) ∧
      cursor + 2864 ≤ 2952790016 ∧ (cursor + 2864) % 8 = 0 := by
  change evaluateHOLFiniteState source (.seq (.call (some (none, none)) (Code.name .sha256_init) [])
    (withTail (routines.drop 1) .skip)) = (none, target) at actual
  obtain ⟨shaState, shaRun, afterSha⟩ := sequence_none source target _ _ actual
  change evaluateHOLFiniteState shaState (.seq (.call (some (none, none)) (Code.name .keccak_init) [])
    (withTail (routines.drop 2) .skip)) = (none, target) at afterSha
  obtain ⟨keccakState, keccakRun, afterKeccak⟩ := sequence_none shaState target _ _ afterSha
  change evaluateHOLFiniteState keccakState (.seq (.call (some (none, none)) (Code.name .ssz_init) [])
    (withTail (routines.drop 3) .skip)) = (none, target) at afterKeccak
  obtain ⟨sszState, sszRun, afterSsz⟩ := sequence_none keccakState target _ _ afterKeccak
  obtain ⟨shaBound, shaGlobals⟩ := sha_call source shaState cursor installed scalars heap bounded aligned shaRun
  have shaCode : OriginalCode.Installed shaState.code := by
    rw [(evaluation_fields source shaState _ none shaRun).2.2.2]; exact installed
  have shaScalars := written_scalars source shaState cursor shaActions scalars shaGlobals
  have shaHeap : shaState.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 192)))) := by
    rw [shaGlobals]
    simpa [shaActions, InitializerAllocations.totalBytes, InitializerAllocations.constant] using
      InitializerAllocations.template_heap source cursor shaActions heap sha_valid
  have shaZero := (shaGlobals (ofString "zero_hashes")).trans
    ((InitializerAllocations.template_other source cursor shaActions (ofString "zero_hashes") (by decide) zero_sha).trans zero)
  have shaAligned : (cursor + 192) % 8 = 0 := by omega
  obtain ⟨keccakBound, keccakGlobals⟩ := keccak_call shaState keccakState (cursor + 192) shaCode shaScalars shaHeap shaBound shaAligned keccakRun
  have keccakCode : OriginalCode.Installed keccakState.code := by
    rw [(evaluation_fields shaState keccakState _ none keccakRun).2.2.2]; exact shaCode
  have keccakScalars := written_scalars shaState keccakState (cursor + 192) keccakActions shaScalars keccakGlobals
  have keccakHeap : keccakState.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 720)))) := by
    rw [keccakGlobals]
    simpa [keccakActions, InitializerAllocations.totalBytes, InitializerAllocations.constant, Nat.add_assoc] using
      InitializerAllocations.template_heap shaState (cursor + 192) keccakActions shaHeap keccak_valid
  have keccakZero := (keccakGlobals (ofString "zero_hashes")).trans
    ((InitializerAllocations.template_other shaState (cursor + 192) keccakActions (ofString "zero_hashes") (by decide) zero_keccak).trans shaZero)
  have keccakAligned : (cursor + 720) % 8 = 0 := by omega
  have keccakRoom : cursor + 720 ≤ 2952790016 := by omega
  obtain ⟨sszBound, sszGlobals⟩ := ssz_call keccakState sszState (cursor + 720) keccakCode keccakScalars keccakHeap
    keccakZero keccakRoom keccakAligned sszRun
  have sszCode : OriginalCode.Installed sszState.code := by
    rw [(evaluation_fields keccakState sszState _ none sszRun).2.2.2]; exact keccakCode
  have sszScalars := written_scalars keccakState sszState (cursor + 720) sszActions keccakScalars sszGlobals
  have offsets := (sszGlobals (ofString "ssz_offs")).trans (ssz_template_offsets keccakState (cursor + 720))
  have chunk := (sszGlobals (ofString "ssz_len_chunk")).trans (ssz_template_chunk keccakState (cursor + 720))
  have zeros := (sszGlobals (ofString "zero_hashes")).trans (ssz_template_zeros keccakState (cursor + 720))
  have finalHeap := (sszGlobals (ofString "heap_ptr")).trans
    (InitializerAllocations.template_heap keccakState (cursor + 720) sszActions keccakHeap ssz_valid)
  exact ⟨shaState, keccakState, sszState, shaRun, keccakRun, sszRun, afterSsz, sszCode, sszScalars,
    by simpa only [Nat.add_assoc] using offsets,
    chunk, by simpa only [Nat.add_assoc] using zeros,
    by simpa [sszActions, InitializerAllocations.totalBytes, InitializerAllocations.constant, Nat.add_assoc] using finalHeap,
    by omega, by omega⟩

/-- At the actual first startup pass from main, the SSZ offset allocation
is 0xa10002f0. Its transport through later initializers remains separate. -/
theorem main_first_three (input : Guest.InputBlob) (origin target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Main.Entry input origin)
    (actual : evaluateHOLFiniteState (Main.memoryState origin) (withTail routines .skip) = (none, target)) :
    ∃ sszState, evaluateHOLFiniteState sszState (withTail (routines.drop 3) .skip) = (none, target) ∧
      OriginalCode.Installed sszState.code ∧ OriginalScalarGlobals.Scalars sszState.globals ∧
      sszState.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)) ∧
      sszState.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word 2701132496#64)) ∧
      sszState.globals.lookup (ofString "zero_hashes") = some (.val (.word 2701132592#64)) ∧
      sszState.globals.lookup (ofString "heap_ptr") = some (.val (.word 2701134640#64)) := by
  have heap := (Main.memory_globals origin).1
  rw [entry.base] at heap
  have zero := (Main.memory_other origin (ofString "zero_hashes") (by decide) (by decide) (by decide)).trans
    (entry.zeros (ofString "zero_hashes") OriginalScalarGlobals.ssz_names.2.2)
  obtain ⟨shaState, keccakState, sszState, shaRun, keccakRun, sszRun, afterSsz, code, scalars, offsets, chunk, zeros, finalHeap, bound, aligned⟩ :=
    first_three (Main.memoryState origin) target InitE.sourceBase entry.code (Main.memory_scalars input origin entry)
      heap zero (by decide) (by decide) actual
  exact ⟨sszState, afterSsz, code, scalars, offsets, chunk, zeros, finalHeap⟩

/-- The same actual first three calls determine their entire global map.
This retains untouched globals as well as each real allocation binding. -/
theorem first_three_templates (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "zero_hashes")=some (.val (.word 0#64)))
    (bounded : cursor≤2952790016) (aligned : cursor%8=0)
    (actual : evaluateHOLFiniteState source (withTail routines .skip)=(none,target)) :
    ∃ sszState,evaluateHOLFiniteState sszState (withTail (routines.drop 3) .skip)=(none,target) ∧
      OriginalCode.Installed sszState.code ∧ OriginalScalarGlobals.Scalars sszState.globals ∧
      sszState.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 (cursor+2864)))) ∧
      cursor+2864≤2952790016 ∧ (cursor+2864)%8=0 ∧
      sszState.globals=(InitializerAllocations.template
        (InitializerAllocations.template (InitializerAllocations.template source cursor shaActions) (cursor+192) keccakActions)
        (cursor+720) sszActions).globals := by
  obtain ⟨shaState,keccakState,sszState,shaRun,keccakRun,sszRun,afterSsz,sszCode,sszScalars,offsets,chunk,zeros,finalHeap,room,sszAligned⟩:=
    first_three source target cursor installed scalars heap zero bounded aligned actual
  obtain ⟨shaBound,shaGlobals⟩:=sha_call source shaState cursor installed scalars heap bounded aligned shaRun
  have shaCode : OriginalCode.Installed shaState.code := by
    rw [(evaluation_fields source shaState _ none shaRun).2.2.2]
    exact installed
  have shaScalars:=written_scalars source shaState cursor shaActions scalars shaGlobals
  have shaHeap : shaState.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 (cursor+192)))) := by
    rw [shaGlobals]
    simpa [shaActions,InitializerAllocations.totalBytes,InitializerAllocations.constant] using InitializerAllocations.template_heap source cursor shaActions heap sha_valid
  obtain ⟨keccakBound,keccakGlobals⟩:=keccak_call shaState keccakState (cursor+192) shaCode shaScalars shaHeap shaBound (by omega) keccakRun
  have keccakCode : OriginalCode.Installed keccakState.code := by
    rw [(evaluation_fields shaState keccakState _ none keccakRun).2.2.2]
    exact shaCode
  have keccakScalars:=written_scalars shaState keccakState (cursor+192) keccakActions shaScalars keccakGlobals
  have keccakHeap : keccakState.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 (cursor+720)))) := by
    rw [keccakGlobals]
    simpa [keccakActions,InitializerAllocations.totalBytes,InitializerAllocations.constant,Nat.add_assoc] using InitializerAllocations.template_heap shaState (cursor+192) keccakActions shaHeap keccak_valid
  have shaZero : shaState.globals.lookup (ofString "zero_hashes")=some (.val (.word 0#64)) :=
    (shaGlobals _).trans ((InitializerAllocations.template_other source cursor shaActions _ (by decide)
      (by intro action member; simp [shaActions] at member; rcases member with rfl|rfl <;> decide)).trans zero)
  have keccakZero : keccakState.globals.lookup (ofString "zero_hashes")=some (.val (.word 0#64)) :=
    (keccakGlobals _).trans ((InitializerAllocations.template_other shaState (cursor+192) keccakActions _ (by decide)
      (by intro action member; simp [keccakActions] at member; rcases member with rfl|rfl|rfl <;> decide)).trans shaZero)
  obtain ⟨sszBound,sszGlobals⟩:=ssz_call keccakState sszState (cursor+720) keccakCode keccakScalars keccakHeap keccakZero (by omega) (by omega) sszRun
  have shaMap : shaState.globals=(InitializerAllocations.template source cursor shaActions).globals:=
    HolFiniteMapExact.ext (funext shaGlobals)
  have keccakMap : keccakState.globals=(InitializerAllocations.template
      (InitializerAllocations.template source cursor shaActions) (cursor+192) keccakActions).globals:=
    (HolFiniteMapExact.ext (funext keccakGlobals)).trans
      (template_globals shaState (InitializerAllocations.template source cursor shaActions) (cursor+192) keccakActions shaMap)
  have sszMap : sszState.globals=(InitializerAllocations.template
      (InitializerAllocations.template (InitializerAllocations.template source cursor shaActions) (cursor+192) keccakActions)
      (cursor+720) sszActions).globals:=
    (HolFiniteMapExact.ext (funext sszGlobals)).trans
      (template_globals keccakState (InitializerAllocations.template
        (InitializerAllocations.template source cursor shaActions) (cursor+192) keccakActions) (cursor+720) sszActions keccakMap)
  exact ⟨sszState,afterSsz,sszCode,sszScalars,finalHeap,room,sszAligned,sszMap⟩

end InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace

#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.ssz_template_offsets
#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.first_three
#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.main_first_three

#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.ssz_template_chunk
#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.ssz_template_zeros

#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.first_three_templates
