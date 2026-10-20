import InitECandidate.Solver.Input.MainForkProgram
import InitECandidate.Solver.Input.Be64CallExecution

namespace InitECandidate.Solver.Input.Main.ForkInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch GasBudget.MemoryWriter

theorem signature_stores_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset : Nat) (words : List (BitVec 64))
    (installed : OriginalCode.Installed source.code)
    (binding : source.globals.lookup (ofString "deposit_event_signature_hash") = some (.val (.word pointer)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (arena : AllocatedBytes.Arena pointer 32) (inside : offset + 8 * words.length ≤ 32)
    (enough : 3 * words.length ≤ source.clock) :
    ∃ post,evaluateHOLFiniteState source (signatureStores offset words) = (some (.returned (.val (.word 0#64))),post) ∧
      post.clock ≤ source.clock ∧ source.clock - 3 * words.length ≤ post.clock ∧ KeccakAbsorb.hashControl post = KeccakAbsorb.hashControl source := by
  induction words generalizing source offset with
  | nil =>
    exact ⟨emptyLocalsHOLFinite source,BuildEntry.zero_return source,Nat.le_refl _,Nat.le_refl _,rfl⟩
  | cons word rest ih =>
    have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query))
        [.op .add [.var .global (ofString "deposit_event_signature_hash"),.const (BitVec.ofNat 64 offset)],.const word] =
        some [.val (.word (byteAddress pointer offset)),.val (.word word)] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,binding,valueIsWord,valueWord,wordOpHOL,wordOp,byteAddress]
    have mapped : BytesMapped source (byteAddress pointer offset) 8 := by
      intro index bounded
      have actual := AllocatedBytes.byte_mapped source pointer 32 (offset + index) domain arena (by simp only [List.length_cons] at inside; omega)
      simpa only [byteAddress,BitVec.ofNat_add,BitVec.add_assoc] using actual
    obtain ⟨middle,called,_,upper,lower,control⟩ := MemoryWordCalls.be64_execute source (byteAddress pointer offset) word _ installed args mapped
      (by simp only [List.length_cons] at enough; omega)
    have globals : middle.globals = source.globals := by have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals) control; exact h
    have code : middle.code = source.code := by have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.code) control; exact h
    have currentDomain : middle.memaddrs = InitE.ordinaryDomain := by
      have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) control
      exact h.trans domain
    have currentInstalled : OriginalCode.Installed middle.code := code.symm ▸ installed
    have currentBinding : middle.globals.lookup (ofString "deposit_event_signature_hash") = some (.val (.word pointer)) := by rw [globals]; exact binding
    obtain ⟨post,remaining,tailUpper,tailLower,tailControl⟩ := ih middle (offset + 8) currentInstalled currentBinding currentDomain
      (by simp only [List.length_cons] at inside; omega) (by simp only [List.length_cons] at enough; omega)
    have actual : evaluateHOLFiniteState source (signatureStores offset (word :: rest)) = (some (.returned (.val (.word 0#64))),post) := by
      rw [signatureStores,StateSteps.next_sequence source middle _ _ called upper]
      exact remaining
    refine ⟨post,actual,Nat.le_trans tailUpper upper,?_,tailControl.trans control⟩
    simp only [List.length_cons]
    omega

theorem signature_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor) (room : cursor + 32 ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : 13 ≤ source.clock) :
    ∃ post,evaluateHOLFiniteState source signatureProgram = (some (.returned (.val (.word 0#64))),post) ∧
      post.clock ≤ source.clock ∧ source.clock - 13 ≤ post.clock ∧
      KeccakAbsorb.hashControl post = KeccakAbsorb.hashControl (InitializerAllocations.template source cursor [signatureAction]) := by
  have allocated := InitializerAllocations.execute_prefix source cursor [signatureAction] (signatureStores 0 signatureWords) installed scalars heap
    (by intro action member; have same := List.mem_singleton.mp member; subst action; exact initial_valid.2.2)
    (by simpa only [InitializerAllocations.totalBytes,signatureAction,InitializerAllocations.constant,Nat.add_zero] using room) aligned (by change 1 ≤ source.clock; omega)
  let ready := {InitializerAllocations.template source cursor [signatureAction] with clock := source.clock - 1}
  have context : InitializerAllocations.context ready = InitializerAllocations.context source :=
    (InitializerAllocations.context_clock _ _).trans (InitializerAllocations.template_context source cursor [signatureAction])
  have currentInstalled := InitializerAllocations.installed_of_context source ready context installed
  have currentDomain := (InitializerAllocations.domain_of_context source ready context).trans domain
  have binding : ready.globals.lookup (ofString "deposit_event_signature_hash") = some (.val (.word (BitVec.ofNat 64 cursor))) := WordTableInitialization.allocated_binding source cursor signatureAction
  have number : (BitVec.ofNat 64 cursor).toNat = cursor := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  obtain ⟨post,run,upper,bounded,control⟩ := signature_stores_execute ready (BitVec.ofNat 64 cursor) 0 signatureWords currentInstalled binding currentDomain
    ⟨by rw [number]; exact lower,by rw [number]; exact room⟩ (by decide) (by change 12 ≤ source.clock - 1; omega)
  have actual : evaluateHOLFiniteState source signatureProgram = (some (.returned (.val (.word 0#64))),post) := by
    rw [signatureProgram,allocated]
    exact run
  refine ⟨post,actual,?_,?_,control⟩
  · change post.clock ≤ source.clock - 1 at upper
    omega
  · change source.clock - 1 - 12 ≤ post.clock at bounded
    omega

end InitECandidate.Solver.Input.Main.ForkInitialization

#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.signature_stores_execute
#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.signature_execute
