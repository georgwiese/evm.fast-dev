import InitECandidate.Solver.Headers.CurrentValidate.HashRead
import InitECandidate.Solver.Headers.CurrentValidate.Transport
import InitECandidate.Solver.WitnessRadix.CopyAwayIntervals

namespace InitECandidate.Solver.Headers.CurrentValidate
open Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix

/-- The actual current software hash preserves the reached witness region
and loop state. Its two workspaces precede the input, and its real digest
slot follows that input in the genuine allocated hash array. -/
theorem hash_normal (data : Data) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (layout : RoundLayout data) (inside : index<data.count)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak256") hashArguments)=(none,post)) :
    RoundState data origin post index := by
  have outArena:=hash_output_arena data layout index inside
  have number : (digestPointer data index).toNat=data.hashes.toNat+32*index :=
    MemoryBytes.offset_toNat data.hashes (32*index) (by have h:=layout.hashes.upper; omega)
  have aligned : (digestPointer data index).toNat%8=0 := by rw [number]; have h:=layout.hashesAligned; omega
  have small : data.lower<2^64 := by have h:=state.rows.inputAfter index inside; have b:=(data.pointers index).isLt; omega
  have frame : HashInput.Frame source post data.lower data.upper := by
    refine ⟨?_⟩
    intro query lower upper
    have actualFrame:=CurrentKeccak.Hash.call_frame source post data.stp data.pad (data.pointers index) (digestPointer data index) query (data.lengths index).toNat
      state.environment hashArguments (hash_arguments_read data origin source index state inside) (state.rows.inputArena index inside) outArena
      (CopyGeneral.Away.before data.stp query 200 data.lower layout.stateBefore small lower)
      (CopyGeneral.Away.before data.pad query 136 data.lower layout.padBefore small lower)
      (CopyGeneral.Away.after (digestPointer data index) query 32 aligned (by have h:=outArena.upper; omega)
        (by rw [number]; have a:=layout.inputBefore; have b:=layout.hsBeforeHashes; omega)) normal
    exact actualFrame.memory
  have globals (key : MlS) : post.globals.lookup key=source.globals.lookup key := by
    have actual:=CurrentKeccak.Hash.call_globals key source.code state.arena.code hashArguments source rfl
    rw [normal] at actual
    exact congrArg Prod.snd actual
  have fields:=evaluation_fields source post _ none normal
  exact state.transport data origin source post index fields.2.2.2 fields.1 globals
    (fun key=>CallNormal.ignored_lookup source post key (ofString "keccak256") hashArguments normal) frame

end InitECandidate.Solver.Headers.CurrentValidate

#print axioms InitECandidate.Solver.Headers.CurrentValidate.hash_normal
