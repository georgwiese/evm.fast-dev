import InitECandidate.Solver.Mpt.AccountBalanceSetAfterGet
import InitECandidate.Solver.MutableTable.FamilyTwoPotential

namespace InitECandidate.Solver.Mpt.AccountBalanceSet
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable GasBudget
open Flapjack.Basis.Pure.MlString

def suffixPrice (markers outers accounts : Nat) (destroyed found : Bool) (iterations : Nat) : Nat :=
  Journal.Append.setPrice .account accounts + 17 +
    (if destroyed then Get.bodyPrice .account outers + 3 +
      (if found then DestroyStorage.loopPrice markers iterations + Journal.Append.deletePrice .account outers + 1 else 0) +
      Journal.Append.setPrice .account (accounts + 1) + 2 else 0)

/-- A real copied account is published, with current ownership, journal
conservation and one potential for the whole family retained for the caller. -/
def Result {ι : Type} [Fintype ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor cutoff population : Nat)
    (objects : ι → TableFamily.Object) (accountWriter : ι) (base cap count : Nat)
    (accounts : List (BitVec 64)) (property : ι → BitVec 64 → Prop) (budget : Bool → Bool → Nat → Nat) : Prop :=
  ∃ (freshCursor paid nextCursor : Nat) (next : ι → TableFamily.Object) (nextEntries : Nat → Journal.Entry ι)
    (nextAccounts : List (BitVec 64)) (added : Nat) (destroyed found : Bool) (iterations : Nat),
    cursor ≤ freshCursor ∧ AccountDecode.Registry.Extension accounts nextAccounts cursor ∧
    paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ 1 ≤ added ∧ added ≤ 3 ∧ count + added ≤ cap ∧
    TableFamily.Model post nextCursor next ∧ Journal.Image post next base (count + added) nextEntries ∧ Journal.Zone next base cap nextCursor ∧
    paid + TableFamily.potential objects ≤ budget destroyed found iterations + TableFamily.potential next ∧
    post.code = source.code ∧ WarmKeys.Environment post ∧ Journal.OtherGlobals source post ∧
    TableFamily.ValuesHave post next (AccountValueExtension.added property accountWriter (BitVec.ofNat 64 freshCursor)) ∧
    Journal.EntryValues nextEntries (count + added) (AccountValueExtension.added property accountWriter (BitVec.ofNat 64 freshCursor)) ∧
    AccountDecode.Registry post cutoff nextCursor next nextAccounts ∧ Journal.CounterEffect source post added 0 0 ∧
    TableFamily.Metadata objects next ∧
    (∀ query : BitVec 64,cutoff ≤ query.toNat → query.toNat < cursor → TableFamily.Outside objects query → Journal.Away base cap query →
      TableFamily.Outside next query ∧ post.memory query = source.memory query) ∧
    post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + added)))) ∧
    (if destroyed then 2 ≤ added else added = 1 ∧ found = false ∧ iterations = 0) ∧ iterations ≤ population ∧ BitVec.ofNat 64 freshCursor ∈ nextAccounts

end InitECandidate.Solver.Mpt.AccountBalanceSet
