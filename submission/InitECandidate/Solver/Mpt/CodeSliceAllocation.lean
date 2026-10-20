import InitECandidate.Solver.Mpt.CodeSlice
import InitECandidate.Solver.Mpt.AccountMutationAllocation
import InitECandidate.Solver.MutableTable.FamilyValuePools

namespace InitECandidate.Solver.Mpt.CodeSlice
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix MutableTable NaturalLayout GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def allocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) := PersistentAlloc.nextState source "sl" cursor (cursor + 16)
def stored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (code : BitVec 64) (length : Nat) :=
  written (allocated source cursor) (BitVec.ofNat 64 cursor) code length

theorem prefix_normal {ι : Type} [Fintype ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor cutoff protectedCursor population : Nat)
    (objects : ι → TableFamily.Object) (anchor outer : ι) (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (accounts : List (BitVec 64)) (property : ι → BitVec 64 → Prop)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap) (before : protectedCursor ≤ cursor)
    (journalAbove : cutoff ≤ base) (populations : ∀ index,(objects index).slots.length ≤ population)
    (environment : WarmKeys.Environment source) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (values : TableFamily.ValuesHave source objects property) (savedValues : Journal.EntryValues entries count property)
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (code : BitVec 64) (length : Nat) (codeArena : AllocatedBytes.Arena code length)
    (codeLocal : source.locals.lookup (ofString "code") = some (.val (.word code)))
    (lengthLocal : source.locals.lookup (ofString "code_len") = some (.val (.word (BitVec.ofNat 64 length))))
    (continuation : ProgHOL 64) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString "sl") .one (ofString "alloc") [.const 16#64] (.seq stores continuation)) = (some (.returned returned),post)) :
    Image (stored source cursor code length) (BitVec.ofNat 64 cursor) code length ∧
      Rlp.Slices.Window source (stored source cursor code length) cursor (cursor + 16) ∧
      AccountMutation.Result source (stored source cursor code length) cursor (cursor + 16) cutoff protectedCursor objects objects outer base cap count count entries accounts accounts property property 1 0 population ∧
      ∃ finish,evaluateHOLFiniteState (stored source cursor code length) continuation = (some (.returned returned),finish) ∧ post = restore source "sl" finish := by
  obtain ⟨room,funded,arena,pointerAligned,allocationData,inner,afterAllocation,restored⟩ := AccountMutation.allocate source post cursor cutoff protectedCursor population objects anchor outer base cap count entries accounts property
    family image zone countBound before journalAbove populations environment registry values savedValues counter "sl" 16 (by decide) (by decide) (.seq stores continuation) returned normal
  let ready := allocated source cursor
  have keep (name : String) (different : ofString name ≠ ofString "sl") : ready.locals.lookup (ofString name) = source.locals.lookup (ofString name) := by
    simp [ready,allocated,PersistentAlloc.nextState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm different]
  have sliceLocal : ready.locals.lookup (ofString "sl") = some (.val (.word (BitVec.ofNat 64 cursor))) := by
    simp [ready,allocated,PersistentAlloc.nextState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  obtain ⟨storeRun,sliceImage,window⟩ := stores_execute ready (BitVec.ofNat 64 cursor) code length environment.domain arena pointerAligned codeArena sliceLocal
    ((keep "code" (by decide)).trans codeLocal) ((keep "code_len" (by decide)).trans lengthLocal)
  let target := stored source cursor code length
  have cursorNumber : (BitVec.ofNat 64 cursor).toNat = cursor := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := (family.tables anchor).bounded; omega)]
  rw [cursorNumber] at window
  have fullWindow : Rlp.Slices.Window source target cursor (cursor + 16) := window
  have earlierWords (query : BitVec 64) (earlier : query.toNat < cursor) : target.memory query = source.memory query := fullWindow query (Or.inl earlier)
  have pools : ∀ index,MemoryModel.PoolFrame source.memory target.memory (objects index).kind (objects index).plan := by
    intro index pool offset inside
    apply earlierWords
    rw [number (objects index).kind (objects index).plan (family.tables index).valid pool offset inside]
    have old := (family.tables index).earlier pool
    omega
  have nextFamily := allocationData.family.of_pools (target := target) rfl rfl rfl pools
  have nextValues := values.of_pools source target objects cursor family property pools
  have frame : TableFamily.PersistentFrame cutoff cursor objects objects source target := ⟨fun query _ earlier outside => ⟨outside,earlierWords query earlier⟩⟩
  have nextRegistry := registry.framed source target cutoff cursor (cursor + 16) objects objects accounts frame (by omega) rfl
  have result := AccountMutation.heap_prefix source target cursor (cursor + 16) cutoff protectedCursor population objects objects outer base cap count entries accounts accounts property 1 1
    funded
    rfl (by omega) before (Nat.le_refl _) nextFamily populations image zone countBound journalAbove environment (environment.of_fields rfl rfl rfl) rfl rfl (HeapGlobals.update source (BitVec.ofNat 64 (cursor + 16)))
    nextRegistry (AccountDecode.Registry.Extension.refl accounts cursor) nextValues savedValues frame (TableFamily.Metadata.refl objects) counter
  have tailRun : evaluateHOLFiniteState target continuation = (some (.returned returned),inner) :=
    (StateSteps.next_sequence ready target stores continuation storeRun (Nat.le_refl _)).symm.trans afterAllocation
  exact ⟨sliceImage,fullWindow,result,inner,tailRun,restored⟩

end InitECandidate.Solver.Mpt.CodeSlice

#print axioms InitECandidate.Solver.Mpt.CodeSlice.prefix_normal
