import InitECandidate.Solver.Mpt.AccountMutationHeapPrefix
import InitECandidate.Solver.WitnessRadix.AllocationNormalExpected
import InitECandidate.Solver.MutableTable.FamilyAdvancePools

namespace InitECandidate.Solver.Mpt.AccountMutation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix MutableTable GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A real scoped allocation derives its own room and preserves all current
tables, registered accounts and undo entries before entering its continuation. -/
theorem allocate {ι : Type} [Fintype ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor cutoff protectedCursor population : Nat)
    (objects : ι → TableFamily.Object) (anchor outer : ι) (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (accounts : List (BitVec 64)) (property : ι → BitVec 64 → Prop)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap) (before : protectedCursor ≤ cursor)
    (journalAbove : cutoff ≤ base) (populations : ∀ index,(objects index).slots.length ≤ population)
    (environment : WarmKeys.Environment source) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (values : TableFamily.ValuesHave source objects property) (savedValues : Journal.EntryValues entries count property)
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (name : String) (size : Nat) (sizeSmall : size < 2^64) (sizeAligned : size % 8 = 0)
    (continuation : ProgHOL 64) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "alloc") [.const (BitVec.ofNat 64 size)] continuation) = (some (.returned returned),post)) :
    cursor + size ≤ 33806089496 ∧ 1 ≤ source.clock ∧ AllocatedBytes.Arena (BitVec.ofNat 64 cursor) size ∧
      (BitVec.ofNat 64 cursor).toNat % 8 = 0 ∧
      Result source (PersistentAlloc.nextState source name cursor (cursor + size)) cursor (cursor + size) cutoff protectedCursor objects objects outer base cap count count entries accounts accounts property property 1 0 population ∧
      ∃ finish,evaluateHOLFiniteState (PersistentAlloc.nextState source name cursor (cursor + size)) continuation = (some (.returned returned),finish) ∧ post = restore source name finish := by
  have table := family.tables anchor
  have aligned : (cursor + size) % 8 = 0 := by have := table.aligned; omega
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) [.const (BitVec.ofNat 64 size)] = some (PersistentAlloc.values (BitVec.ofNat 64 size)) := rfl
  obtain ⟨room,nextBound,funded,finish,tailRun,restored⟩ := PersistentAlloc.call_normal_expected source post name [.const (BitVec.ofNat 64 size)] continuation cursor size (cursor + size)
    table.bounded sizeSmall (Nat.le_refl _) (by omega) aligned args environment.allocCode environment.trapCode table.heap returned normal
  let ready := PersistentAlloc.nextState source name cursor (cursor + size)
  have globals : HeapGlobals source ready := HeapGlobals.update source (BitVec.ofNat 64 (cursor + size))
  have nextFamily : TableFamily.Model ready (cursor + size) objects := family.advance_pools
    (by simp [ready,PersistentAlloc.nextState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]) (by omega) nextBound aligned rfl rfl (fun _ _ _ _ => rfl)
  have frame : TableFamily.PersistentFrame cutoff cursor objects objects source ready := ⟨fun _ _ _ outside => ⟨outside,rfl⟩⟩
  have nextRegistry := registry.framed source ready cutoff cursor (cursor + size) objects objects accounts frame (by omega) rfl
  have nextValues := values.of_memory source ready objects property rfl
  have result := heap_prefix source ready cursor (cursor + size) cutoff protectedCursor population objects objects outer base cap count entries accounts accounts property 1 1 funded rfl
    (by omega) before (Nat.le_refl _) nextFamily populations image zone countBound journalAbove environment (environment.of_fields rfl rfl rfl) rfl rfl globals nextRegistry
    (AccountDecode.Registry.Extension.refl accounts cursor) nextValues savedValues frame (TableFamily.Metadata.refl objects) counter
  have cursorNumber : (BitVec.ofNat 64 cursor).toNat = cursor := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := table.bounded; omega)]
  have arena : AllocatedBytes.Arena (BitVec.ofNat 64 cursor) size := by
    constructor
    · rw [cursorNumber]
      have lower := table.valid.lower .header
      have earlier := table.earlier .header
      change (objects anchor).plan.base .header + 72 ≤ cursor at earlier
      omega
    · rw [cursorNumber]; exact room
  exact ⟨room,funded,arena,by rw [cursorNumber]; exact table.aligned,result,finish,tailRun,restored⟩

end InitECandidate.Solver.Mpt.AccountMutation

#print axioms InitECandidate.Solver.Mpt.AccountMutation.allocate
