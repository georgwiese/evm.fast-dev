import InitECandidate.Solver.Mpt.AccountSetNormalRegistered
import InitECandidate.Solver.Mpt.AccountSetEnvironment

namespace InitECandidate.Solver.Mpt.AccountSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable GasBudget

/-- Actual unchanged set_account caller retains complete current ownership,
metadata and the one-record journal effect at its reached normal post-state. -/
theorem call_registered {ι : Type} [DecidableEq ι]
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
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (values query account))
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "set_account") expressions)=(none,post)) :
    count<cap ∧ ∃ (paid nextCursor : Nat) (next : TableFamily.Object) (oldFlag oldValue : BitVec 64),
      2≤paid ∧ paid≤source.clock ∧ post.clock=source.clock-paid ∧ cursor≤nextCursor ∧ next.kind=(objects writer).kind ∧
      (oldFlag=0#64 ∨ oldFlag=1#64) ∧ TableFamily.Model post nextCursor (Function.update objects writer next) ∧
      Journal.Image post (Function.update objects writer next) base (count+1) (Function.update entries count ⟨writer,BitVec.ofNat 64 cursor,oldFlag,oldValue⟩) ∧
      Journal.Zone (Function.update objects writer next) base cap nextCursor ∧
      paid+GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity≤
        Journal.Append.setPrice (objects writer).kind (objects writer).slots.length+2+GrowRuntime.growthPotential (objects writer).kind next.plan.capacity ∧
      next.slots.length≤(objects writer).slots.length+1 ∧
      post.globals.lookup (ofString "journal_n")=some (.val (.word (BitVec.ofNat 64 (count+1)))) ∧
      post.locals=source.locals ∧ post.code=source.code ∧ WarmKeys.Environment post ∧ Journal.OtherGlobals source post ∧
      Journal.ProtectedFrame base cap cursor objects (Function.update objects writer next) source post ∧
      TableFamily.ValuesHave post (Function.update objects writer next) property ∧
      Journal.EntryValues (Function.update entries count ⟨writer,BitVec.ofNat 64 cursor,oldFlag,oldValue⟩) (count+1) property ∧
      AccountDecode.Registry post cutoff nextCursor (Function.update objects writer next) accounts ∧ TableFamily.Metadata objects (Function.update objects writer next) ∧ Journal.CounterEffect source post 1 0 0 := by
  obtain ⟨callee,called,queryCell,accountCell⟩ := InitECandidate.Solver.Mpt.AccountSet.environment source.code.lookup query account (original_code source.code installed)
  obtain ⟨positive,target,answer,bodyRun⟩ := Input.CallNormal.ignored_callee_return source post (ofString "set_account") expressions _ body callee .one args called normal
  let entry := callEntryStateHOLFinite source callee
  have entryFamily : TableFamily.Model entry cursor objects := family.of_control rfl rfl rfl rfl
  have entryImage : Journal.Image entry objects base count entries := image.transfer rfl (fun _=>rfl) (fun _=>rfl) (fun _ _ _=>rfl) image.separate
  have entryRegistry := registry.framed source entry cutoff cursor cursor objects objects accounts
    (TableFamily.PersistentFrame.of_memory cutoff cursor objects source entry rfl) (Nat.le_refl _) rfl
  obtain ⟨room,answerEq,paid,nextCursor,next,flag,oldValue,bodyPositive,funded,clock,forward,kind,binary,models,nextImage,nextZone,price,population,nextCounter,codeEq,nextEnvironment,globals,frame,nextValues,nextSaved,nextRegistry,metadata⟩ :=
    body_registered entry target transaction query account cursor objects writer base cap count entries entryFamily entryImage zone countBound
      (environment.of_fields rfl rfl rfl) installed cutoff accounts entryRegistry accountApart property tableValues owned savedValues writerKind queryArena
      transactionGlobal tableMapped tableStored journal capacity counter queryCell accountCell answer bodyRun
  rw [answerEq] at bodyRun
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "set_account") expressions _ body callee .one
    (.val (.word 0#64)) target args called (by omega) bodyRun (by simp [shapeOfHOLExact,shapeEqHOL])
  have same := congrArg Prod.snd (normal.symm.trans actual)
  change post={target with locals:=source.locals} at same
  subst post
  have finalFamily : TableFamily.Model {target with locals:=source.locals} nextCursor (Function.update objects writer next) := models.of_control rfl rfl rfl rfl
  have finalImage : Journal.Image {target with locals:=source.locals} (Function.update objects writer next) base (count+1)
      (Function.update entries count ⟨writer,BitVec.ofNat 64 cursor,flag,oldValue⟩) := nextImage.transfer rfl (fun _=>rfl) (fun _=>rfl) (fun _ _ _=>rfl) nextImage.separate
  have finalRegistry := nextRegistry.framed target {target with locals:=source.locals} cutoff nextCursor nextCursor (Function.update objects writer next) (Function.update objects writer next) accounts
    (TableFamily.PersistentFrame.of_memory cutoff nextCursor _ target _ rfl) (Nat.le_refl _) rfl
  have small : count+1<2^64 := by
    have upper := zone.valid.upper
    change base+32*cap≤33806089496 at upper
    omega
  have effect := Journal.CounterEffect.append source {target with locals:=source.locals} count small counter nextCounter
  change paid≤source.clock-1 at funded
  change target.clock=source.clock-1-paid at clock
  exact ⟨room,1+paid,nextCursor,next,flag,oldValue,by omega,by omega,by change target.clock=_; omega,forward,kind,binary,
    finalFamily,finalImage,nextZone,by omega,population,nextCounter,rfl,codeEq,nextEnvironment.of_fields rfl rfl rfl,globals,⟨frame.words⟩,
    nextValues,nextSaved,finalRegistry,metadata,effect⟩

end InitECandidate.Solver.Mpt.AccountSet

#print axioms InitECandidate.Solver.Mpt.AccountSet.call_registered
