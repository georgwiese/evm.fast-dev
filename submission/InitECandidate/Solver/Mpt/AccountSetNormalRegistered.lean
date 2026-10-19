import InitECandidate.Solver.Mpt.AccountSetProgram
import InitECandidate.Solver.GasBudget.JournalAppendSetRegistered
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.Mpt.AccountSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable GasBudget

/-- Complete unchanged set_account, including its real ts-field read,
journaled mutation and zero return. It retains current account, cache/undo,
table and journal ownership and stable metadata without a future model. -/
theorem body_registered {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (transaction query account : BitVec 64)
    (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count≤cap)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (cutoff : Nat) (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (accountApart : ∀ item,item∈accounts → item.toNat+56≤base ∨ base+32*cap≤item.toNat)
    (property : ι → BitVec 64 → Prop) (tableValues : TableFamily.ValuesHave source objects property)
    (owned : property writer account) (savedValues : Journal.EntryValues entries count property)
    (writerKind : (objects writer).kind=.account) (queryArena : AllocatedBytes.Arena query 20)
    (transactionGlobal : source.globals.lookup (ofString "ts")=some (.val (.word transaction)))
    (tableMapped : source.memaddrs (transaction+16#64)) (tableStored : source.memory (transaction+16#64)=.word (objects writer).pointer)
    (journal : source.globals.lookup (ofString "journal")=some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap")=some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n")=some (.val (.word (BitVec.ofNat 64 count))))
    (queryCell : source.locals.lookup (ofString "addr")=some (.val (.word query)))
    (accountCell : source.locals.lookup (ofString "a")=some (.val (.word account)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    count<cap ∧ returned=.val (.word 0#64) ∧ ∃ (paid nextCursor : Nat) (next : TableFamily.Object) (oldFlag oldValue : BitVec 64),
      1≤paid ∧ paid≤source.clock ∧ post.clock=source.clock-paid ∧ cursor≤nextCursor ∧ next.kind=(objects writer).kind ∧
      (oldFlag=0#64 ∨ oldFlag=1#64) ∧ TableFamily.Model post nextCursor (Function.update objects writer next) ∧
      Journal.Image post (Function.update objects writer next) base (count+1) (Function.update entries count ⟨writer,BitVec.ofNat 64 cursor,oldFlag,oldValue⟩) ∧
      Journal.Zone (Function.update objects writer next) base cap nextCursor ∧
      paid+GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity≤
        Journal.Append.setPrice (objects writer).kind (objects writer).slots.length+1+GrowRuntime.growthPotential (objects writer).kind next.plan.capacity ∧
      next.slots.length≤(objects writer).slots.length+1 ∧
      post.globals.lookup (ofString "journal_n")=some (.val (.word (BitVec.ofNat 64 (count+1)))) ∧
      post.code=source.code ∧ WarmKeys.Environment post ∧ Journal.OtherGlobals source post ∧
      Journal.ProtectedFrame base cap cursor objects (Function.update objects writer next) source post ∧
      TableFamily.ValuesHave post (Function.update objects writer next) property ∧
      Journal.EntryValues (Function.update entries count ⟨writer,BitVec.ofNat 64 cursor,oldFlag,oldValue⟩) (count+1) property ∧
      AccountDecode.Registry post cutoff nextCursor (Function.update objects writer next) accounts ∧ TableFamily.Metadata objects (Function.update objects writer next) := by
  rw [body_shape] at normal
  have safe : Input.LocalPrefix (ofString "addr") mutation := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨called,mutationRun,returnRun,saved⟩ := safe.normal_continue source post (.return (.const 0#64)) returned normal
  have args := arguments source transaction (objects writer).pointer query account transactionGlobal tableMapped tableStored queryCell accountCell
  have queryFits : query.toNat+KeyHash.keySize (objects writer).kind<2^64 := by
    rw [writerKind]
    change query.toNat+20<2^64
    have := queryArena.upper
    omega
  have queryMapped : ∀ offset<KeyHash.keySize (objects writer).kind,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress query offset)) := by
    intro offset inside
    apply AllocatedBytes.byte_mapped source query 20 offset environment.domain queryArena
    simpa only [writerKind,KeyHash.keySize] using inside
  obtain ⟨room,paid,nextCursor,next,flag,oldValue,positive,funded,clock,forward,kind,binary,models,nextImage,nextZone,price,population,nextCounter,locals,codeEq,nextEnvironment,globals,effect,frame,nextValues,nextSaved,nextRegistry,metadata⟩ :=
    Journal.Append.set_call_registered_values source called cursor objects writer base cap count entries family image zone countBound environment cutoff accounts registry accountApart query account
      property tableValues owned savedValues queryFits queryMapped (Get.original_code source.code installed) (journal_code source.code installed)
      journal capacity counter _ args mutationRun
  have actual := Input.return_normal called post (.const 0#64) returned returnRun
  have returnedEq : returned=.val (.word 0#64) := Option.some.inj (actual.1.symm.trans rfl)
  have postEq := actual.2
  have finalFamily : TableFamily.Model post nextCursor (Function.update objects writer next) := by rw [postEq]; exact models.of_control rfl rfl rfl rfl
  have finalImage : Journal.Image post (Function.update objects writer next) base (count+1) (Function.update entries count ⟨writer,BitVec.ofNat 64 cursor,flag,oldValue⟩) := by
    rw [postEq]
    exact nextImage.transfer rfl (fun _=>rfl) (fun _=>rfl) (fun _ _ _=>rfl) nextImage.separate
  have finalRegistry := nextRegistry.framed called post cutoff nextCursor nextCursor (Function.update objects writer next) (Function.update objects writer next) accounts
    (TableFamily.PersistentFrame.of_memory cutoff nextCursor _ called post (by rw [postEq] <;> rfl)) (Nat.le_refl _) (by rw [postEq] <;> rfl)
  refine ⟨room,returnedEq,paid,nextCursor,next,flag,oldValue,positive,funded,?_,forward,kind,binary,finalFamily,finalImage,nextZone,price,population,?_,?_,?_,?_,?_,?_,nextSaved,finalRegistry,metadata⟩
  · rw [postEq]; exact clock
  · rw [postEq]; exact nextCounter
  · rw [postEq]; exact codeEq
  · rw [postEq]; exact nextEnvironment.of_fields rfl rfl rfl
  · rw [postEq]; exact globals
  · rw [postEq]; exact ⟨frame.words⟩
  · rw [postEq]; exact nextValues

end InitECandidate.Solver.Mpt.AccountSet

#print axioms InitECandidate.Solver.Mpt.AccountSet.body_registered
