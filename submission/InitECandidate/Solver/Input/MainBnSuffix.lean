import InitECandidate.Solver.Input.MainBnLayout

namespace InitECandidate.Solver.Input.Main.BnInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
set_option maxRecDepth 100000

def exponentWritten (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) :=
  InitializerWords.written {source with memory := StoreWord.put source.memory pointer 9698021743855595808#64} pointer 8 exponent.tail

theorem exponent_stores_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (binding : source.globals.lookup (ofString "bn_expw") = some (.val (.word pointer)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (arena : AllocatedBytes.Arena pointer 352) (aligned : pointer.toNat % 8 = 0) :
    evaluateHOLFiniteState source exponentStores = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite (exponentWritten source pointer)) := by
  have mapped : source.memaddrs pointer := by
    simpa [byteAddress] using AllocatedBytes.word_mapped source pointer 352 0 domain arena (by decide) aligned (by decide)
  have first := StoreWord.execute source (.var .global (ofString "bn_expw")) (.const 9698021743855595808#64) pointer 9698021743855595808#64 binding rfl mapped
  let middle := {source with memory := StoreWord.put source.memory pointer 9698021743855595808#64}
  have rest := InitializerWords.execute middle "bn_expw" pointer 8 352 exponent.tail (.return (.const 0#64)) binding domain arena aligned (by decide)
    (by simp only [List.length_tail,exponent_length]; omega)
  rw [exponentStores,StateSteps.next_sequence source middle _ _ first (Nat.le_refl _),rest]
  exact BuildEntry.zero_return (exponentWritten source pointer)

theorem after_b2_stores_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor)
    (room : cursor + 352 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 1 ≤ source.clock) :
    ∃ target,evaluateHOLFiniteState source afterB2Stores = (some (.returned (.val (.word 0#64))),target) ∧
      target.clock = source.clock - 1 ∧
      KeccakAbsorb.hashControl target = KeccakAbsorb.hashControl (InitializerAllocations.template source cursor [exponentAction]) := by
  have valid : ∀ action ∈ [exponentAction],InitializerAllocations.Valid action := by
    intro action member
    have same := List.mem_singleton.mp member
    subst action
    exact exponent_valid
  have allocated := InitializerAllocations.execute_prefix source cursor [exponentAction] exponentStores installed scalars heap valid room aligned enough
  let ready := {InitializerAllocations.template source cursor [exponentAction] with clock := source.clock - 1}
  have number : (BitVec.ofNat 64 cursor).toNat = cursor := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have binding : ready.globals.lookup (ofString "bn_expw") = some (.val (.word (BitVec.ofNat 64 cursor))) := by
    simp only [ready,InitializerAllocations.template_globals]
    simp [InitializerAllocations.globalTemplate,exponentAction,HolFiniteMapExact.update,FUPDATE,ofString]
  have run := exponent_stores_execute ready (BitVec.ofNat 64 cursor) binding domain ⟨by rw [number]; exact lower,by rw [number]; exact room⟩ (by rw [number]; exact aligned)
  refine ⟨emptyLocalsHOLFinite (exponentWritten ready (BitVec.ofNat 64 cursor)),?_,?_,?_⟩
  · rw [afterB2Stores,allocated]; exact run
  · change source.clock - 1 = source.clock - 1
    rfl
  · simp only [exponentWritten,InitializerWords.written,KeccakAbsorb.hashControl,emptyLocalsHOLFinite,ready]

def b2Written (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (real imaginary : RlpWrite.U256Value.Words) :=
  {source with memory := WordWrites.write (WordWrites.write source.memory (RlpWrite.U256Value.wordWrites pointer real)) (RlpWrite.U256Value.wordWrites (pointer + 32#64) imaginary)}

theorem b2_stores_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (real imaginary : RlpWrite.U256Value.Words)
    (binding : source.globals.lookup (ofString "bn_b2") = some (.val (.word pointer)))
    (realLocal : source.locals.lookup (ofString "b2r") = some (RlpWrite.U256Value.tuple real))
    (imaginaryLocal : source.locals.lookup (ofString "b2i") = some (RlpWrite.U256Value.tuple imaginary))
    (domain : source.memaddrs = InitE.ordinaryDomain) (arena : AllocatedBytes.Arena pointer 64) (aligned : pointer.toNat % 8 = 0) :
    evaluateHOLFiniteState source b2Stores = evaluateHOLFiniteState (b2Written source pointer real imaginary) afterB2Stores := by
  have mapped (offset : Nat) (offsetAligned : offset % 8 = 0) (inside : offset + 32 ≤ 64) (index : Fin 4) :
      source.memaddrs (pointer + BitVec.ofNat 64 offset + BitVec.ofNat 64 (8 * index.val)) := by
    have current := AllocatedBytes.word_mapped source pointer 64 (offset + 8 * index.val) domain arena (by omega) aligned (by omega)
    simpa only [byteAddress,BitVec.ofNat_add,BitVec.add_assoc] using current
  have first := RlpWrite.U256Value.store_execute source (.var .global (ofString "bn_b2")) (.var .local (ofString "b2r")) pointer real binding realLocal (by simpa using mapped 0 (by decide) (by decide))
  let middle := {source with memory := WordWrites.write source.memory (RlpWrite.U256Value.wordWrites pointer real)}
  have destination : eval middle (.op .add [.var .global (ofString "bn_b2"),.const 32#64]) = some (.val (.word (pointer + 32#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,middle,binding,valueIsWord,valueWord,wordOpHOL,wordOp]
  have second := RlpWrite.U256Value.store_execute middle _ (.var .local (ofString "b2i")) (pointer + 32#64) imaginary destination imaginaryLocal (mapped 32 (by decide) (by decide))
  rw [b2Stores,StateSteps.next_sequence source middle _ _ first (Nat.le_refl _),StateSteps.next_sequence middle (b2Written source pointer real imaginary) _ _ second (Nat.le_refl _)]

end InitECandidate.Solver.Input.Main.BnInitialization

#print axioms InitECandidate.Solver.Input.Main.BnInitialization.exponent_stores_execute
#print axioms InitECandidate.Solver.Input.Main.BnInitialization.after_b2_stores_execute
#print axioms InitECandidate.Solver.Input.Main.BnInitialization.b2_stores_execute
