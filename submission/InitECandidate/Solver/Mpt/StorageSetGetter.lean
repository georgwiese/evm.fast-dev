import InitECandidate.Solver.Mpt.StorageSetAfterGet
import InitECandidate.Solver.Mpt.StorageSetResultControl
import InitECandidate.Solver.MutableTable.GetCallOrigin

namespace InitECandidate.Solver.Mpt.StorageSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem getter_normal {ι : Type} [Fintype ι] [DecidableEq ι]
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
    (outerLocal : source.locals.lookup (ofString "outer") = some (.val (.word (objects outer).pointer)))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source getter = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ Result source post cursor cutoff population objects outer base cap count accounts property (fun created => Get.bodyPrice .account population + 1 + tailPrice population created) := by
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) [localVar "outer",localVar "addr"] =
      some [.val (.word (objects outer).pointer),.val (.word address)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,outerLocal,addressLocal]
  have queryFits : address.toNat + KeyHash.keySize (objects outer).kind < 2^64 := by
    rw [outerKind]
    change address.toNat + 20 < 2^64
    have := addressArena.upper
    omega
  have queryMapped : ∀ offset < KeyHash.keySize (objects outer).kind,source.memaddrs (panByteAlignHOL (width := 64) (byteAddress address offset)) := by
    rw [outerKind]
    intro offset inside
    exact AllocatedBytes.byte_mapped source address 20 offset environment.domain addressArena inside
  obtain ⟨getPaid,flag,value,finish,getPositive,getBound,getFunded,binary,origin,tailRun,scope⟩ := Get.model_normal_entry_origin source post (objects outer).kind (objects outer).plan
    (objects outer).slots cursor (objects outer).floor (family.tables outer) environment address queryFits queryMapped (Get.original_code source.code installed) "m" _ afterGet args returned normal
  let ready := setVarHOLFinite (ofString "m") (Get.pair flag value) {source with clock := source.clock - getPaid}
  have readyFamily : TableFamily.Model ready cursor objects := family.of_control rfl rfl rfl rfl
  have readyImage : Journal.Image ready objects base count entries := image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  have readyRegistry := registry.framed source ready cutoff cursor cursor objects objects accounts
    (TableFamily.PersistentFrame.of_memory cutoff cursor objects source ready rfl) (Nat.le_refl _) rfl
  have readyAddress : ready.locals.lookup (ofString "addr") = some (.val (.word address)) := by
    simpa [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "m" ≠ ofString "addr" by decide] using addressLocal
  have readyQuery : ready.locals.lookup (ofString "key") = some (.val (.word query)) := by
    simpa [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "m" ≠ ofString "key" by decide] using queryLocal
  have readyValue : ready.locals.lookup (ofString "value") = some (Input.RlpWrite.U256Value.tuple words) := by
    simpa [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "m" ≠ ofString "value" by decide] using valueLocal
  have readyOuter : ready.locals.lookup (ofString "outer") = some (.val (.word (objects outer).pointer)) := by
    simpa [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "m" ≠ ofString "outer" by decide] using outerLocal
  have readyPair : ready.locals.lookup (ofString "m") = some (Get.pair flag value) := by simp [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have owned := origin.occupied_property source (cell (objects outer).plan .values 0) (BitVec.ofNat 64 (objects outer).plan.capacity) flag value (objects outer).slots (property outer) (values outer)
  obtain ⟨answerEq,result⟩ := after_get_normal ready finish address query flag value words cursor cutoff population objects outer base cap count entries readyFamily readyImage zone countBound populations
    (environment.of_fields rfl rfl rfl) installed accounts readyRegistry accountApart property values savedValues references freshOwned outerKind addressArena queryArena readyAddress readyQuery readyValue readyOuter readyPair owned
    journal capacity counter returned tailRun
  have getterMono : Get.bodyPrice .account (objects outer).slots.length ≤ Get.bodyPrice .account population := by
    unfold Get.bodyPrice
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (populations outer)) _
  change getPaid ≤ Get.bodyPrice (objects outer).kind (objects outer).slots.length + 1 at getBound
  rw [outerKind] at getBound
  have fullResult := result.prepend_readonly (source := source) getPaid (Get.bodyPrice .account population + 1) getFunded (by omega) rfl rfl rfl rfl
  rw [scope]
  exact ⟨answerEq,fullResult.locals _⟩

end InitECandidate.Solver.Mpt.StorageSet

#print axioms InitECandidate.Solver.Mpt.StorageSet.getter_normal
