import InitECandidate.Solver.Mpt.AccountBalanceSetResult
import InitECandidate.Solver.Input.EvaluationOracle

namespace InitECandidate.Solver.Mpt.AccountMutation
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable GasBudget
open Flapjack.Basis.Pure.MlString

/-- The reached state of a real account mutation. Counts, objects and value
predicates are explicit, so two journal-changing phases compose directly. -/
structure Result {ι : Type} [Fintype ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor nextCursor cutoff protectedCursor : Nat)
    (objects next : ι → TableFamily.Object) (outer : ι) (base cap count nextCount : Nat) (nextEntries : Nat → Journal.Entry ι)
    (accounts nextAccounts : List (BitVec 64)) (property nextProperty : ι → BitVec 64 → Prop)
    (price appendLimit populationLimit : Nat) : Prop where
  clockForward : post.clock ≤ source.clock
  cursorForward : cursor ≤ nextCursor
  protectedBefore : protectedCursor ≤ cursor
  countForward : count ≤ nextCount
  countBound : nextCount ≤ cap
  appends : nextCount - count ≤ appendLimit
  family : TableFamily.Model post nextCursor next
  image : Journal.Image post next base nextCount nextEntries
  zone : Journal.Zone next base cap nextCursor
  work : source.clock - post.clock + TableFamily.potential objects ≤ price + TableFamily.potential next
  populations : ∀ index,(next index).slots.length ≤ populationLimit
  code : post.code = source.code
  oracle : post.ffi.oracle = source.ffi.oracle
  environment : WarmKeys.Environment post
  globals : Journal.OtherGlobals source post
  values : TableFamily.ValuesHave post next nextProperty
  savedValues : Journal.EntryValues nextEntries nextCount nextProperty
  registry : AccountDecode.Registry post cutoff nextCursor next nextAccounts
  extension : AccountDecode.Registry.Extension accounts nextAccounts cursor
  effect : Journal.CounterEffect source post (nextCount - count) 0 0
  metadata : TableFamily.Metadata objects next
  frame : ∀ query : BitVec 64,cutoff ≤ query.toNat → query.toNat < protectedCursor → TableFamily.Outside objects query → Journal.Away base cap query →
    TableFamily.Outside next query ∧ post.memory query = source.memory query
  counter : post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 nextCount)))
  propertyIncluded : ∀ index value,property index value → nextProperty index value
  outerValues : ∀ value,nextProperty outer value ↔ property outer value
  readerKnown : ∀ index,(objects index).kind = .account →
    (∀ value,property index value → AccountDecode.Registry.Known accounts value) →
    ∀ value,nextProperty index value → AccountDecode.Registry.Known nextAccounts value

end InitECandidate.Solver.Mpt.AccountMutation
