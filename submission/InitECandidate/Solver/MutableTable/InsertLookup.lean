import InitECandidate.Solver.MutableTable.InsertGeneralEntry
import InitECandidate.Solver.MutableTable.FindGeneralCall

namespace InitECandidate.Solver.MutableTable.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

def findPrice (kind : KeyHash.Kind) (count : Nat) : Nat := Find.generalProbePrice kind * count + (KeyHash.hashPrice kind + 1)
def rawPrice (kind : KeyHash.Kind) (count : Nat) : Nat := count + KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 2

/-- The physical insertion table data also derives the actual read-only
lookup caller for any caller parameter names, at every original key width. -/
theorem GeneralData.find_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Find.Parameters)
    (kind : KeyHash.Kind) (vals order position count : BitVec 64) (bits : Nat) (items : List Nat)
    (data : GeneralData source table p kind vals order position count bits items)
    (memeqCode : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (findCode : source.code.lookup (ofString "htab_find_slot") = some (Find.formals, Find.body, .one))
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word table), .val (.word p.key)])
    (enough : findPrice kind items.length ≤ source.clock) :
    ∃ paid index, paid ≤ findPrice kind items.length ∧ index.toNat ≤ p.capacity.toNat ∧
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_find_slot") arguments continuation) =
        (let output := evaluateHOLFiniteState (WitnessRadix.QueryBranch.bind {source with clock := source.clock - paid} name index) continuation
         (output.1, restore source name output.2)) := by
  have capNumber : p.capacity.toNat = 2 ^ bits := by
    rw [data.capacity, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) data.small)]
  have inside (i : Nat) (bounded : i < 2 ^ bits) : (BitVec.ofNat 64 i).toNat < p.capacity.toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans bounded (Nat.pow_lt_pow_right (by decide) data.small)), capNumber]
    exact bounded
  exact Find.general_call source table p kind data.header data.keyLength bits data.small data.capacity items data.room data.binary data.covered
    (by intro i bounded; exact (data.slots _ (inside i bounded)).fits)
    (by intro i bounded; exact (data.slots _ (inside i bounded)).mapped)
    data.queryFits data.queryMapped data.hashCode memeqCode findCode name arguments continuation args data.little enough

end InitECandidate.Solver.MutableTable.Insert

#print axioms InitECandidate.Solver.MutableTable.Insert.GeneralData.find_call
