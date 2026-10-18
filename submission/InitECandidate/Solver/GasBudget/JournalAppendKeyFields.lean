import InitECandidate.Solver.GasBudget.JournalAppendKeyModel

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

theorem key_local (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (cursor : Nat) (query : BitVec 64)
    (name : String) (lengthOther : ofString "klen" ≠ ofString name) (copyOther : ofString "kc" ≠ ofString name) :
    (keyState source kind cursor query).locals.lookup (ofString name) = source.locals.lookup (ofString name) :=
  (bind_lookup_other _ "kc" name _ copyOther).trans (bind_lookup_other source "klen" name _ lengthOther)

theorem copied_key_geometry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (cursor : Nat) (query : BitVec 64)
    (region : MemoryRegion.Valid ⟨cursor, NaturalLayout.stride kind⟩) (domain : source.memaddrs = InitE.ordinaryDomain) :
    (BitVec.ofNat 64 cursor).toNat + KeyHash.keySize kind < 2 ^ 64 ∧
      ∀ offset < KeyHash.keySize kind, (keyState source kind cursor query).memaddrs
        (panByteAlignHOL (width := 64) (byteAddress (BitVec.ofNat 64 cursor) offset)) := by
  have upper := region.upper
  change cursor + NaturalLayout.stride kind ≤ 33806089496 at upper
  have room := (key_rounding kind).1
  constructor
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  · intro offset inside
    rw [show (keyState source kind cursor query).memaddrs = InitE.ordinaryDomain from domain]
    exact MemoryRegion.byte_mapped ⟨cursor, NaturalLayout.stride kind⟩ region offset (by change offset < NaturalLayout.stride kind; omega)

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.key_local
#print axioms InitECandidate.Solver.GasBudget.Journal.Append.copied_key_geometry
