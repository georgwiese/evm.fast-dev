import InitECandidate.Solver.Input.MainForkSignature
import InitECandidate.Solver.Input.AddressFromWords

namespace InitECandidate.Solver.Input.Main.ForkInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch GasBudget.MemoryWriter

def finalActions (rows : List Address) := rows.map Address.action ++ [signatureAction]

private theorem combine_actions (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (row : Address) (rest : List Address) :
    InitializerAllocations.template (InitializerAllocations.template source cursor [row.action]) (cursor + 24) (finalActions rest) =
      InitializerAllocations.template source cursor (finalActions (row :: rest)) := by
  simp only [finalActions,List.map_cons,List.cons_append,InitializerAllocations.template,Address.action,InitializerAllocations.constant]

theorem addresses_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (rows : List Address)
    (members : ∀ row ∈ rows,row ∈ addresses)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor) (room : cursor + (24 * rows.length + 32) ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : 9 * rows.length + 13 ≤ source.clock) :
    ∃ post,evaluateHOLFiniteState source (addressProgram rows signatureProgram) = (some (.returned (.val (.word 0#64))),post) ∧
      post.clock ≤ source.clock ∧ source.clock - (9 * rows.length + 13) ≤ post.clock ∧
      KeccakAbsorb.hashControl post = KeccakAbsorb.hashControl (InitializerAllocations.template source cursor (finalActions rows)) := by
  induction rows generalizing source cursor with
  | nil => exact signature_execute source cursor installed scalars heap domain lower room aligned enough
  | cons row rest ih =>
    have valid := address_valid row (members row (by simp))
    have allocated := InitializerAllocations.execute_prefix source cursor [row.action] (.seq row.call (addressProgram rest signatureProgram)) installed scalars heap
      (by intro action member; have same := List.mem_singleton.mp member; subst action; exact valid)
      (by change cursor + (24 + 0) ≤ _; simp only [List.length_cons] at room; omega) aligned
      (by change 1 ≤ source.clock; simp only [List.length_cons] at enough; omega)
    let ready := {InitializerAllocations.template source cursor [row.action] with clock := source.clock - 1}
    have context : InitializerAllocations.context ready = InitializerAllocations.context source :=
      (InitializerAllocations.context_clock _ _).trans (InitializerAllocations.template_context source cursor [row.action])
    have currentInstalled := InitializerAllocations.installed_of_context source ready context installed
    have currentDomain := (InitializerAllocations.domain_of_context source ready context).trans domain
    have binding : ready.globals.lookup (ofString row.name) = some (.val (.word (BitVec.ofNat 64 cursor))) := WordTableInitialization.allocated_binding source cursor row.action
    have args : evalListHOLFinite ready (h := fun query => Classical.propDecidable (ready.memaddrs query))
        [.var .global (ofString row.name),.const row.hi,.const row.mid,.const row.lo] = some (AddressFromWords.values (BitVec.ofNat 64 cursor) row.hi row.mid row.lo) := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,binding,AddressFromWords.values]
    have number : (BitVec.ofNat 64 cursor).toNat = cursor := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by simp only [List.length_cons] at room; omega)]
    have arena : AllocatedBytes.Arena (BitVec.ofNat 64 cursor) 24 := ⟨by rw [number]; exact lower,by rw [number]; simp only [List.length_cons] at room; omega⟩
    have mapped : BytesMapped ready (BitVec.ofNat 64 cursor) 20 := by
      intro offset inside
      exact AllocatedBytes.byte_mapped ready _ 24 offset currentDomain arena (by omega)
    obtain ⟨middle,called,_,upper,bounded,control⟩ := AddressFromWords.call_execute ready (BitVec.ofNat 64 cursor) row.hi row.mid row.lo _ currentInstalled args mapped
      (by change 8 ≤ source.clock - 1; simp only [List.length_cons] at enough; omega)
    have globals : middle.globals = ready.globals := by have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals) control; exact h
    have code : middle.code = ready.code := by have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.code) control; exact h
    have nextDomain : middle.memaddrs = InitE.ordinaryDomain := by
      have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) control
      exact h.trans currentDomain
    have nextInstalled : OriginalCode.Installed middle.code := code.symm ▸ currentInstalled
    have nextScalars : OriginalScalarGlobals.Scalars middle.globals := by
      rw [globals]
      exact InitializerAllocations.template_scalars source cursor [row.action] scalars
    have nextHeap : middle.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 24)))) := by
      rw [globals]
      exact InitializerAllocations.template_heap source cursor [row.action] heap (by intro action member; have same := List.mem_singleton.mp member; subst action; exact valid)
    change source.clock - 1 - 8 ≤ middle.clock at bounded
    obtain ⟨post,remaining,tailUpper,tailLower,tailControl⟩ := ih middle (cursor + 24) (by intro item member; exact members item (List.mem_cons_of_mem _ member))
      nextInstalled nextScalars nextHeap nextDomain (by omega) (by simp only [List.length_cons] at room; omega) (by omega)
      (by simp only [List.length_cons] at enough; omega)
    have actual : evaluateHOLFiniteState source (addressProgram (row :: rest) signatureProgram) = (some (.returned (.val (.word 0#64))),post) := by
      rw [addressProgram,allocated]
      change evaluateHOLFiniteState ready (.seq row.call (addressProgram rest signatureProgram)) = _
      rw [StateSteps.next_sequence ready middle row.call _ called upper]
      exact remaining
    have transported := InitializerAllocations.template_hash_control ready middle (cursor + 24) (finalActions rest) control
    have clockModel : KeccakAbsorb.hashControl (InitializerAllocations.template ready (cursor + 24) (finalActions rest)) =
        KeccakAbsorb.hashControl (InitializerAllocations.template (InitializerAllocations.template source cursor [row.action]) (cursor + 24) (finalActions rest)) := by
      unfold ready
      rw [InitializerAllocations.template_clock]
      rfl
    have model := tailControl.trans (transported.trans clockModel)
    rw [combine_actions source cursor row rest] at model
    refine ⟨post,actual,?_,?_,model⟩
    · change middle.clock ≤ source.clock - 1 at upper
      omega
    · simp only [List.length_cons]
      omega

end InitECandidate.Solver.Input.Main.ForkInitialization

#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.addresses_execute
