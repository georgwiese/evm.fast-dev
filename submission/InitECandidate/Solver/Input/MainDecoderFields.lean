import InitECandidate.Solver.Input.MainDecoderSetup
import InitECandidate.Solver.Input.HeapZeroFrame

namespace InitECandidate.Solver.Input.Main.DecoderSetup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

private theorem next_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (pointer next : Nat) :
    InitializerAllocations.context (PersistentAlloc.nextState source name pointer next) = InitializerAllocations.context source := rfl

theorem entered_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) :
    InitializerAllocations.context (entered source input) = InitializerAllocations.context source := by
  have first := next_context source "out" (cursor input) (cursor input + 256)
  have second := next_context (outState source input) "z32" (cursor input + 256) (cursor input + 288)
  have third : InitializerAllocations.context (cleared source input) = InitializerAllocations.context (zeroState source input) := rfl
  have last : InitializerAllocations.context (entered source input) = InitializerAllocations.context (cleared source input) := rfl
  exact last.trans (third.trans (second.trans first))

theorem entered_bindings (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) :
    (entered source input).locals.lookup (ofString "inp") = source.locals.lookup (ofString "inp") ∧
    (entered source input).locals.lookup (ofString "out") = some (.val (.word (BitVec.ofNat 64 (cursor input)))) ∧
    (entered source input).locals.lookup (ofString "z32") = some (.val (.word (zeroPointer input))) ∧
    (entered source input).locals.lookup (ofString "si") = some (.val (.word 0#64)) ∧
    (entered source input).locals.lookup (ofString "err_code") = some (.val (.word 0#64)) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals simp [entered,cleared,zeroState,outState,zeroPointer,PersistentAlloc.nextState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
    show ofString "err_code" ≠ ofString "inp" from by decide,show ofString "si" ≠ ofString "inp" from by decide,
    show ofString "z32" ≠ ofString "inp" from by decide,show ofString "out" ≠ ofString "inp" from by decide,
    show ofString "err_code" ≠ ofString "out" from by decide,show ofString "si" ≠ ofString "out" from by decide,
    show ofString "z32" ≠ ofString "out" from by decide,show ofString "err_code" ≠ ofString "z32" from by decide,
    show ofString "si" ≠ ofString "z32" from by decide,show ofString "err_code" ≠ ofString "si" from by decide]

theorem entered_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) :
    (entered source input).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor input + 288)))) := by
  simp [entered,cleared,zeroState,PersistentAlloc.nextState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]

theorem entered_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (scalars : OriginalScalarGlobals.Scalars source.globals) :
    OriginalScalarGlobals.Scalars (entered source input).globals :=
  (scalars.update (ofString "heap_ptr") (BitVec.ofNat 64 (cursor input + 256))).update (ofString "heap_ptr") (BitVec.ofNat 64 (cursor input + 288))

theorem entered_other_global (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (key : MlS)
    (different : key ≠ ofString "heap_ptr") : (entered source input).globals.lookup key = source.globals.lookup key := by
  simp [entered,cleared,zeroState,outState,PersistentAlloc.nextState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm different]

theorem entered_bytes (input : Guest.InputBlob) (before source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (copied : InputCopied input before source) (bounded : input.length % 2 ^ 64 ≤ Guest.maxInputBytes) : Blob.HeapInput (entered source input) input inputPointer := by
  have geometry := input_cursor_bounds input bounded
  have small : cursor input ≤ 2847949152 := geometry.2.1
  have endInput : 2713731432 + input.length % 2 ^ 64 + 8 ≤ cursor input := geometry.1
  have number : (zeroPointer input).toNat = cursor input + 256 := by unfold zeroPointer; rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have arena : AllocatedBytes.Arena (zeroPointer input) 32 := ⟨by rw [number]; omega,by rw [number]; omega⟩
  have initial : Blob.HeapInput (zeroState source input) input inputPointer := Blob.HeapInput.of_fields source (zeroState source input) input inputPointer rfl rfl rfl copied.bytes
  have preserved := Blob.HeapInput.zero_separate (zeroState source input) input inputPointer (zeroPointer input) 32 initial (by decide)
    (by change 2713731432 + input.length % 2 ^ 64 < _; have bound : input.length % 2 ^ 64 ≤ 134217712 := bounded; omega) arena
    (Or.inr (by rw [number]; change 2713731432 + input.length % 2 ^ 64 ≤ cursor input + 256; omega))
  exact Blob.HeapInput.of_fields _ (entered source input) input inputPointer rfl rfl rfl preserved

end InitECandidate.Solver.Input.Main.DecoderSetup

#print axioms InitECandidate.Solver.Input.Main.DecoderSetup.entered_context
#print axioms InitECandidate.Solver.Input.Main.DecoderSetup.entered_bindings
#print axioms InitECandidate.Solver.Input.Main.DecoderSetup.entered_heap
#print axioms InitECandidate.Solver.Input.Main.DecoderSetup.entered_scalars
#print axioms InitECandidate.Solver.Input.Main.DecoderSetup.entered_bytes

#print axioms InitECandidate.Solver.Input.Main.DecoderSetup.entered_other_global
