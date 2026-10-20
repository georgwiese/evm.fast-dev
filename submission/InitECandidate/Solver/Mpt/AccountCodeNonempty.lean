import InitECandidate.Solver.Mpt.AccountCodeProgram
import InitECandidate.Solver.Mpt.CodeSliceAllocation
import InitECandidate.Solver.Mpt.AccountJournalSetResult
import InitECandidate.Solver.Mpt.AccountMutationValueExtension
import InitECandidate.Solver.Mpt.AccountMutationAgreement

namespace InitECandidate.Solver.Mpt.AccountCode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix MutableTable NaturalLayout GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem nonempty_normal {ι : Type} [Fintype ι] [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor cutoff protectedCursor population : Nat)
    (objects : ι → TableFamily.Object) (writer outer : ι) (kind : (objects writer).kind = .word) (different : writer ≠ outer)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι) (accounts : List (BitVec 64)) (property : ι → BitVec 64 → Prop)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap) (before : protectedCursor ≤ cursor)
    (journalAbove : cutoff ≤ base) (populations : ∀ index,(objects index).slots.length ≤ population)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (values : TableFamily.ValuesHave source objects property) (savedValues : Journal.EntryValues entries count property)
    (accountApart : ∀ account,account ∈ accounts → account.toNat + 56 ≤ base ∨ base + 32 * cap ≤ account.toNat)
    (code hashValue transaction : BitVec 64) (length : Nat)
    (codeArena : AllocatedBytes.Arena code length) (hashArena : AllocatedBytes.Arena hashValue 32)
    (codeLocal : source.locals.lookup (ofString "code") = some (.val (.word code)))
    (lengthLocal : source.locals.lookup (ofString "code_len") = some (.val (.word (BitVec.ofNat 64 length))))
    (hashLocal : source.locals.lookup (ofString "h") = some (.val (.word hashValue)))
    (transactionGlobal : source.globals.lookup (ofString "ts") = some (.val (.word transaction)))
    (mapped : source.memaddrs (transaction + 48#64)) (storedTable : source.memory (transaction + 48#64) = .word (objects writer).pointer)
    (tableBefore : (transaction + 48#64).toNat < cursor)
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (normal : evaluateHOLFiniteState source nonemptyBranch = (none,post)) :
    ∃ nextCursor nextEntries next,
      cursor + 16 ≤ nextCursor ∧ CodeSlice.Image post (BitVec.ofNat 64 cursor) code length ∧
      (∀ offset : Nat,offset < 16 → TableFamily.Outside next (BitVec.ofNat 64 cursor + BitVec.ofNat 64 offset)) ∧
      AccountMutation.Result source post cursor nextCursor cutoff protectedCursor objects next outer base cap count (count + 1) nextEntries accounts accounts property
        (AccountValueExtension.added property writer (BitVec.ofNat 64 cursor))
        (Journal.Append.setPrice .word (objects writer).slots.length + 2) 1 (population + 1) := by
  rw [nonempty_execute source] at normal
  have lifted := Input.CallNormal.fallthrough_return source post "sl" .one (ofString "alloc") [.const 16#64] (.seq sliceStores codeSetCall) normal
  have reassociate := Input.CallNormal.continuation_congr source (ofString "sl") .one (ofString "alloc") [.const 16#64]
    (.seq (.seq sliceStores codeSetCall) (.return (.const 0#64))) (.seq sliceStores (.seq codeSetCall (.return (.const 0#64))))
    (fun state => MemeqByteRuntime.sequence_assoc state sliceStores codeSetCall (.return (.const 0#64)))
  rw [reassociate] at lifted
  obtain ⟨sliceImage,window,allocationData,inner,tailRun,scope⟩ := CodeSlice.prefix_normal source _ cursor cutoff protectedCursor population objects writer outer base cap count entries accounts property
    family image zone countBound before journalAbove populations environment registry values savedValues counter code length codeArena codeLocal lengthLocal (.seq codeSetCall (.return (.const 0#64))) _ lifted
  let ready := CodeSlice.stored source cursor code length
  let fresh := BitVec.ofNat 64 cursor
  let nextProperty := AccountValueExtension.added property writer fresh
  have published := allocationData.add_non_account_value writer (by rw [kind]; decide) different fresh
  have safe : Input.LocalPrefix (ofString "addr") codeSetCall := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨mutated,setRun,returnRun,_⟩ := safe.normal_continue ready inner (.return (.const 0#64)) _ tailRun
  have returnInfo := Input.return_normal mutated inner (.const 0#64) _ returnRun
  have keep (name : String) (different : ofString "sl" ≠ ofString name) : ready.locals.lookup (ofString name) = source.locals.lookup (ofString name) := by
    simp [ready,CodeSlice.stored,CodeSlice.written,CodeSlice.allocated,PersistentAlloc.nextState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different]
  have sliceLocal : ready.locals.lookup (ofString "sl") = some (.val (.word fresh)) := by
    simp [ready,fresh,CodeSlice.stored,CodeSlice.written,CodeSlice.allocated,PersistentAlloc.nextState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have tableCell : ready.memory (transaction + 48#64) = .word (objects writer).pointer := (window _ (Or.inl tableBefore)).trans storedTable
  have readyMapped : ready.memaddrs (transaction + 48#64) := mapped
  have args : evalListHOLFinite ready (h := fun query => Classical.propDecidable (ready.memaddrs query))
      [.load .one (.op .add [.var .global (ofString "ts"),.const 48#64]),localVar "h",localVar "sl"] = some (TableCall.values (objects writer).pointer hashValue fresh) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,show ready.globals.lookup (ofString "ts") = source.globals.lookup (ofString "ts") from (published.globals (ofString "ts") (by decide) (by decide)),
      transactionGlobal,(keep "h" (by decide)).trans hashLocal,sliceLocal,valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,readyMapped,tableCell,TableCall.values]
  obtain ⟨nextCursor,nextEntries,next,_,setFrame,setData⟩ := AccountMutation.journal_set ready mutated (cursor + 16) protectedCursor population objects writer outer base cap count entries published.family published.image published.zone countBound published.environment cutoff accounts published.registry
    (fun account member => accountApart account member) (by have := published.protectedBefore; omega) populations hashValue fresh nextProperty published.values (Or.inr ⟨rfl,rfl⟩) published.savedValues
    (by rw [kind,KeyHash.keySize]; have := hashArena.upper; omega)
    (by intro offset inside; rw [kind,KeyHash.keySize] at inside; exact AllocatedBytes.byte_mapped ready hashValue 32 offset published.environment.domain hashArena inside)
    (Get.original_code ready.code (by rw [published.code]; exact installed)) (AccountSet.journal_code ready.code (by rw [published.code]; exact installed))
    ((published.globals (ofString "journal") (by decide) (by decide)).trans journal) ((published.globals (ofString "journal_cap") (by decide) (by decide)).trans capacity) published.counter _ args setRun
  have agreement : emptyLocalsHOLFinite post = emptyLocalsHOLFinite mutated := by
    have same := congrArg (fun s : PanSemStateFiniteExact 64 Guest.HostMemory => emptyLocalsHOLFinite s) scope
    rw [returnInfo.2] at same
    exact same
  have cursorNumber : fresh.toNat = cursor := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := (family.tables writer).bounded; omega)]
  have freshArena : AllocatedBytes.Arena fresh 16 := sliceImage.arena
  have sliceWords (offset : Nat) (inside : offset < 16) : TableFamily.Outside next (fresh + BitVec.ofNat 64 offset) ∧
      post.memory (fresh + BitVec.ofNat 64 offset) = ready.memory (fresh + BitVec.ofNat 64 offset) := by
    have number : (fresh + BitVec.ofNat 64 offset).toNat = cursor + offset := by change (byteAddress fresh offset).toNat = cursor + offset; rw [byteAddress_toNat fresh offset (by have := freshArena.upper; omega),cursorNumber]
    have outside : TableFamily.Outside objects (fresh + BitVec.ofNat 64 offset) := by
      intro index
      apply TableFootprint.Outside.of_regions _ _ (family.tables index).valid
      intro pool
      right
      rw [number]
      have := (family.tables index).earlier pool
      omega
    have retained := setFrame.words _ (by rw [number]; omega) outside (Or.inr (by rw [number]; have := zone.earlier; omega))
    have memory := congrArg (fun s : PanSemStateFiniteExact 64 Guest.HostMemory => s.memory) agreement
    exact ⟨retained.1,(congrFun memory _).trans retained.2⟩
  have finalImage := CodeSlice.Image.of_agreement ready post fresh code length sliceImage (by simpa using (sliceWords 0 (by decide)).2) (sliceWords 8 (by decide)).2
  refine ⟨nextCursor,nextEntries,next,setData.cursorForward,finalImage,fun offset inside => (sliceWords offset inside).1,?_⟩
  have combined := (published.trans setData).local_agreement agreement
  simpa only [kind,Nat.zero_add,show 1 + (Journal.Append.setPrice .word (objects writer).slots.length + 1) = Journal.Append.setPrice .word (objects writer).slots.length + 2 by omega] using combined

end InitECandidate.Solver.Mpt.AccountCode

#print axioms InitECandidate.Solver.Mpt.AccountCode.nonempty_normal
