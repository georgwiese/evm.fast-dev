import InitECandidate.Solver.Headers.ValidateHashRead
import InitECandidate.Solver.Headers.ValidateRoundTransport
import InitECandidate.Solver.WitnessRadix.CopyAwayIntervals

namespace InitECandidate.Solver.Headers.Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- The genuine original hash call retains the whole fixed input/record
region and loop context. Its scratch and output footprints are separated
using the actual startup buffers and original digest-array allocation. -/
theorem hash_normal (data : Data) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (layout : RoundLayout data) (inside : index<data.count)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak256") hashArguments)=(none,post)) :
    RoundState data origin post index := by
  have buffers:=hash_buffers data origin source index state layout inside
  have entered:=Keccak256.allocated_entry source data.stp (data.pointers index) data.pad (digestPointer data index) (data.lengths index).toNat state.environment buffers
  obtain ⟨locals,forward,cost,control,memory⟩ := Keccak256.call_normal source post hashArguments data.stp (data.pointers index) data.pad (digestPointer data index) (data.lengths index).toNat
    (hash_arguments_read data origin source index state inside) (hash_original_code source.code state.installed) entered
    (by have h:=buffers.inputArena.upper; omega) normal
  have fields:=Input.evaluation_fields source post _ none normal
  have globals:=congrArg PanSemStateFiniteExact.globals control
  change post.globals=source.globals at globals
  have number : (digestPointer data index).toNat=data.hashes.toNat+32*index :=
    MemoryBytes.offset_toNat data.hashes (32*index) (by have h:=layout.hashes.upper; omega)
  have aligned : (digestPointer data index).toNat%8=0 := by rw [number]; have h:=layout.hashesAligned; omega
  have small : data.lower<2^64 := by have h:=state.rows.inputAfter index inside; have b:=(data.pointers index).isLt; omega
  have frame : Input.HashInput.Frame source post data.lower data.upper := by
    refine ⟨?_⟩
    intro query lower upper
    apply memory query
    refine ⟨CopyGeneral.Away.before data.stp query 200 data.lower layout.stateBefore small lower,
      CopyGeneral.Away.before data.pad query 136 data.lower layout.padBefore small lower,?_⟩
    exact CopyGeneral.Away.after (digestPointer data index) query 32 aligned (by have h:=buffers.outputArena.upper; omega)
      (by rw [number]; have a:=layout.inputBefore; have b:=layout.hsBeforeHashes; omega)
  exact state.transport data origin source post index fields.2.2.2 fields.2.2.1 fields.1
    (Input.evaluation_oracle source post _ none normal) globals locals frame

end InitECandidate.Solver.Headers.Validate

#print axioms InitECandidate.Solver.Headers.Validate.hash_normal
