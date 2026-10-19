import InitECandidate.Solver.Mpt.AccountCreatedProgram
import InitECandidate.Solver.Mpt.AccountRegistry
import InitECandidate.Solver.Input.LocalPrefix
import InitECandidate.Solver.Input.ReturnNormal
import InitECandidate.Solver.GasBudget.JournalCounterLedger

namespace InitECandidate.Solver.Mpt.AccountCreated
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable GasBudget

theorem body_registered {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address transaction : BitVec 64)
    (cursor cutoff : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap) (environment : WarmKeys.Environment source)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (owned : property writer 1#64)
    (writerKind : (objects writer).kind = .account) (addressArena : AllocatedBytes.Arena address 20)
    (transactionGlobal : source.globals.lookup (ofString "ts") = some (.val (.word transaction)))
    (tableMapped : source.memaddrs (transaction + 56#64)) (tableStored : source.memory (transaction + 56#64) = .word (objects writer).pointer)
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ ∃ (paid nextCursor : Nat) (next : TableFamily.Object),
      paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model post nextCursor (Function.update objects writer next) ∧
      Journal.Image post (Function.update objects writer next) base count entries ∧ Journal.Zone (Function.update objects writer next) base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
        9 * (objects writer).slots.length + 12 + GrowRuntime.growthPotential (objects writer).kind next.plan.capacity ∧
      next.slots.length ≤ (objects writer).slots.length + 1 ∧ post.code = source.code ∧ WarmKeys.Environment post ∧ HeapGlobals source post ∧
      TableFamily.ValuesHave post (Function.update objects writer next) property ∧ AccountDecode.Registry post cutoff nextCursor (Function.update objects writer next) accounts ∧
      TableFamily.PersistentFrame 0 cursor objects (Function.update objects writer next) source post ∧
      TableFamily.Metadata objects (Function.update objects writer next) ∧ Journal.CounterEffect source post 0 0 0 := by
  rw [body_shape] at normal
  have safe : Input.LocalPrefix (ofString "addr") mutation := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨mutated,mutationRun,returnRun,keepAddress⟩ := safe.normal_continue source post (.return (.const 0#64)) returned normal
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) [table,localVar "addr",.const 1#64] =
      some (TableCall.values (objects writer).pointer address 1#64) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,table,localVar,toExact,transactionGlobal,addressLocal,valueIsWord,valueWord,wordOpHOL,wordOp,
      memLoadHOLExact,isWfShapeExactHOL,tableMapped,tableStored,TableCall.values]
  have queryFits : address.toNat + KeyHash.keySize (objects writer).kind < 2^64 := by
    rw [writerKind]
    change address.toNat + 20 < 2^64
    have := addressArena.upper
    omega
  have queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind,
      source.memaddrs (panByteAlignHOL (width := 64) (byteAddress address offset)) := by
    rw [writerKind]
    intro offset inside
    exact AllocatedBytes.byte_mapped source address 20 offset environment.domain addressArena inside
  obtain ⟨paid,nextCursor,next,funded,clock,forward,kind,models,nextImage,nextZone,price,population,locals,codes,nextEnvironment,globals,floorFrame,frame,nextValues,metadata⟩ :=
    Journal.set_zone_normal_values source mutated cursor objects writer base cap count entries family image zone countBound environment address 1#64 property values owned queryFits queryMapped _ args mutationRun
  have nextRegistry := registry.framed source mutated cutoff cursor nextCursor objects (Function.update objects writer next) accounts
    ⟨fun query above earlier outside => frame.words query (Nat.zero_le _) earlier outside⟩ forward (nextEnvironment.domain.trans environment.domain.symm)
  have returnedInfo := Input.return_normal mutated post (.const 0#64) returned returnRun
  have answerEq : returned = .val (.word 0#64) := Option.some.inj (returnedInfo.1.symm.trans rfl)
  rw [returnedInfo.2]
  let finish := emptyLocalsHOLFinite mutated
  have finalFamily : TableFamily.Model finish nextCursor (Function.update objects writer next) := models.of_control rfl rfl rfl rfl
  have finalImage : Journal.Image finish (Function.update objects writer next) base count entries := nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
  have finalRegistry := nextRegistry.framed mutated finish cutoff nextCursor nextCursor (Function.update objects writer next) (Function.update objects writer next) accounts
    (TableFamily.PersistentFrame.of_memory cutoff nextCursor _ mutated finish rfl) (Nat.le_refl _) rfl
  have effect := Journal.CounterEffect.unchanged source finish (globals (ofString "journal_n") (by decide))
  rw [writerKind,set_price] at price
  refine ⟨answerEq,paid,nextCursor,next,funded,clock,forward,finalFamily,finalImage,nextZone,?_,population,codes,nextEnvironment.of_fields rfl rfl rfl,
    globals,nextValues,finalRegistry,⟨frame.words⟩,metadata,effect⟩
  rw [writerKind]
  exact price

end InitECandidate.Solver.Mpt.AccountCreated

#print axioms InitECandidate.Solver.Mpt.AccountCreated.body_registered
