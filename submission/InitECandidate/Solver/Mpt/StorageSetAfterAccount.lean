import InitECandidate.Solver.Mpt.StorageSetGetter
import InitECandidate.Solver.PanDeclarations

namespace InitECandidate.Solver.Mpt.StorageSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem after_account_normal {ι : Type} [Fintype ι] [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address query : BitVec 64) (words : Input.RlpWrite.U256Value.Words)
    (cursor cutoff population : Nat) (objects : ι → TableFamily.Object) (outer : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap) (populations : ∀ reader,(objects reader).slots.length ≤ population)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (accountApart : ∀ account,account ∈ accounts → account.toNat + 56 ≤ base ∨ base + 32 * cap ≤ account.toNat)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (savedValues : Journal.EntryValues entries count property)
    (references : ∀ value,property outer value → ∃ reader,(objects reader).pointer = value ∧ (objects reader).kind = .word)
    (freshOwned : ∀ reader,(objects reader).kind = .word → ∀ pointer,AllocatedBytes.Arena pointer 32 → pointer.toNat % 8 = 0 → property reader pointer)
    (outerKind : (objects outer).kind = .account) (addressArena : AllocatedBytes.Arena address 20) (queryArena : AllocatedBytes.Arena query 32)
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (queryLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (valueLocal : source.locals.lookup (ofString "value") = some (Input.RlpWrite.U256Value.tuple words))
    (transaction : BitVec 64) (transactionGlobal : source.globals.lookup (ofString "ts") = some (.val (.word transaction)))
    (tableMapped : source.memaddrs (transaction + 32#64)) (tableStored : source.memory (transaction + 32#64) = .word (objects outer).pointer)
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterAccount = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ Result source post cursor cutoff population objects outer base cap count accounts property (fun created => Get.bodyPrice .account population + 1 + tailPrice population created) := by
  have guard : Input.PureGuard (.ite (.cmp .equal (localVar "a") (.const 1#64)) (.raise (ofString "StateErr") (.const 3#64)) .skip) := .ite _ (.raise _ _) .skip
  have tailRun := guard.normal_continue source post (.dec (ofString "outer") .one table getter) returned normal
  let ready := bind source "outer" (objects outer).pointer
  have tableRead : eval source table = some (.val (.word (objects outer).pointer)) := by
    simp [eval,table,evalHOLExact,evalListHOLExact,toExact,transactionGlobal,valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,tableMapped,tableStored]
  have setup : BuildEntry.Initializes source [("outer",table)] ready (restore source "outer") := .step _ tableRead (.done _)
  change evaluateHOLFiniteState source (BuildEntry.declarations [("outer",table)] getter) = _ at tailRun
  rw [BuildEntry.declarations_execute setup getter] at tailRun
  let finish := (evaluateHOLFiniteState ready getter).2
  have resultEq := congrArg Prod.fst tailRun
  change (evaluateHOLFiniteState ready getter).1 = some (.returned returned) at resultEq
  have getterRun : evaluateHOLFiniteState ready getter = (some (.returned returned),finish) := Prod.ext resultEq rfl
  have scope := congrArg Prod.snd tailRun
  change restore source "outer" finish = post at scope
  have readyFamily : TableFamily.Model ready cursor objects := family.of_control rfl rfl rfl rfl
  have readyImage : Journal.Image ready objects base count entries := image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  have readyRegistry := registry.framed source ready cutoff cursor cursor objects objects accounts
    (TableFamily.PersistentFrame.of_memory cutoff cursor objects source ready rfl) (Nat.le_refl _) rfl
  have readyAddress : ready.locals.lookup (ofString "addr") = some (.val (.word address)) :=
    (bind_lookup_other source "outer" "addr" _ (by decide)).trans addressLocal
  have readyQuery : ready.locals.lookup (ofString "key") = some (.val (.word query)) :=
    (bind_lookup_other source "outer" "key" _ (by decide)).trans queryLocal
  have readyValue : ready.locals.lookup (ofString "value") = some (Input.RlpWrite.U256Value.tuple words) :=
    (bind_lookup_other source "outer" "value" _ (by decide)).trans valueLocal
  obtain ⟨answerEq,result⟩ := getter_normal ready finish address query words cursor cutoff population objects outer base cap count entries readyFamily readyImage zone countBound populations
    (environment.of_fields rfl rfl rfl) installed accounts readyRegistry accountApart property values savedValues references freshOwned outerKind addressArena queryArena readyAddress readyQuery readyValue (bind_lookup_same _ _ _)
    journal capacity counter returned getterRun
  have fullResult := result.prepend_readonly (source := source) 0 0 (Nat.zero_le _) (Nat.le_refl _) (by simp [ready,QueryBranch.bind,setVarHOLFinite]) rfl rfl rfl
  rw [← scope]
  refine ⟨answerEq,?_⟩
  simpa only [Nat.zero_add,restore] using fullResult.locals (HolFiniteMapExact.resVarEq finish.locals (ofString "outer",source.locals.lookup (ofString "outer")))

end InitECandidate.Solver.Mpt.StorageSet

#print axioms InitECandidate.Solver.Mpt.StorageSet.after_account_normal
