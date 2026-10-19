import InitECandidate.Solver.Mpt.AccountCreatedNormal

namespace InitECandidate.Solver.Mpt.AccountCreated
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable GasBudget

theorem call_registered {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address transaction : BitVec 64)
    (cursor cutoff : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap) (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (owned : property writer 1#64)
    (writerKind : (objects writer).kind = .account) (addressArena : AllocatedBytes.Arena address 20)
    (transactionGlobal : source.globals.lookup (ofString "ts") = some (.val (.word transaction)))
    (tableMapped : source.memaddrs (transaction + 56#64)) (tableStored : source.memory (transaction + 56#64) = .word (objects writer).pointer)
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) expressions = some [.val (.word address)])
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "mark_account_created") expressions) = (none,post)) :
    ∃ (paid nextCursor : Nat) (next : TableFamily.Object),
      1 ≤ paid ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model post nextCursor (Function.update objects writer next) ∧
      Journal.Image post (Function.update objects writer next) base count entries ∧ Journal.Zone (Function.update objects writer next) base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
        9 * (objects writer).slots.length + 13 + GrowRuntime.growthPotential (objects writer).kind next.plan.capacity ∧
      next.slots.length ≤ (objects writer).slots.length + 1 ∧ post.locals = source.locals ∧ post.code = source.code ∧ WarmKeys.Environment post ∧ HeapGlobals source post ∧
      TableFamily.ValuesHave post (Function.update objects writer next) property ∧ AccountDecode.Registry post cutoff nextCursor (Function.update objects writer next) accounts ∧
      TableFamily.PersistentFrame 0 cursor objects (Function.update objects writer next) source post ∧
      TableFamily.Metadata objects (Function.update objects writer next) ∧ Journal.CounterEffect source post 0 0 0 := by
  obtain ⟨callee,called,addressLocal⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "mark_account_created") "addr" body address
    (original_code source.code installed)
  obtain ⟨positive,target,answer,bodyRun⟩ := Input.CallNormal.ignored_callee_return source post (ofString "mark_account_created") expressions _ body callee .one args called normal
  let entry := callEntryStateHOLFinite source callee
  have entryFamily : TableFamily.Model entry cursor objects := family.of_control rfl rfl rfl rfl
  have entryImage : Journal.Image entry objects base count entries := image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  have entryRegistry := registry.framed source entry cutoff cursor cursor objects objects accounts
    (TableFamily.PersistentFrame.of_memory cutoff cursor objects source entry rfl) (Nat.le_refl _) rfl
  obtain ⟨answerEq,paid,nextCursor,next,funded,clock,forward,models,nextImage,nextZone,price,population,codes,nextEnvironment,globals,nextValues,nextRegistry,frame,metadata,effect⟩ :=
    body_registered entry target address transaction cursor cutoff objects writer base cap count entries entryFamily entryImage zone countBound (environment.of_fields rfl rfl rfl)
      accounts entryRegistry property values owned writerKind addressArena transactionGlobal tableMapped tableStored addressLocal answer bodyRun
  rw [answerEq] at bodyRun
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "mark_account_created") expressions _ body callee .one
    (.val (.word 0#64)) target args called (by omega) bodyRun (by simp [shapeOfHOLExact,shapeEqHOL])
  have postEq := congrArg Prod.snd (normal.symm.trans actual)
  change post = {target with locals := source.locals} at postEq
  subst post
  let finish := {target with locals := source.locals}
  have finalFamily : TableFamily.Model finish nextCursor (Function.update objects writer next) := models.of_control rfl rfl rfl rfl
  have finalImage : Journal.Image finish (Function.update objects writer next) base count entries := nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
  have finalRegistry := nextRegistry.framed target finish cutoff nextCursor nextCursor (Function.update objects writer next) (Function.update objects writer next) accounts
    (TableFamily.PersistentFrame.of_memory cutoff nextCursor _ target finish rfl) (Nat.le_refl _) rfl
  change paid ≤ source.clock - 1 at funded
  change target.clock = source.clock - 1 - paid at clock
  exact ⟨1 + paid,nextCursor,next,by omega,by omega,by change target.clock = _; omega,forward,finalFamily,finalImage,nextZone,by omega,population,rfl,codes,
    nextEnvironment.of_fields rfl rfl rfl,globals,nextValues,finalRegistry,⟨frame.words⟩,metadata,effect⟩

end InitECandidate.Solver.Mpt.AccountCreated

#print axioms InitECandidate.Solver.Mpt.AccountCreated.call_registered
