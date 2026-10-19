import InitECandidate.Solver.Mpt.StorageKeyNormal
import InitECandidate.Solver.WitnessRadix.CopyAwayIntervals
import InitECandidate.Solver.MutableTable.FamilyRangeMemory
import InitECandidate.Solver.MutableTable.FamilyValueRange
import InitECandidate.Solver.Mpt.AccountRegistry

namespace InitECandidate.Solver.Mpt.StorageKey
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix MutableTable

theorem result_above (source : PanSemStateFiniteExact 64 Guest.HostMemory) (address key scratch : BitVec 64)
    (cutoff : Nat) (scratchArena : AllocatedBytes.Arena scratch 52) (scratchBelow : scratch.toNat + 52 ≤ cutoff)
    (small : cutoff < 2^64) (query : BitVec 64) (above : cutoff ≤ query.toNat) :
    (resultState source address key scratch).memory query = source.memory query := by
  have number : (scratch + 20#64).toNat = scratch.toNat + 20 := by
    rw [BitVec.toNat_add_of_lt (by change scratch.toNat + 20 < 2^64; have := scratchArena.upper; omega)]
    rfl
  have firstAway := CopyGeneral.Away.before scratch query 20 cutoff (by omega) small above
  have secondAway := CopyGeneral.Away.before (scratch + 20#64) query 32 cutoff (by rw [number]; omega) small above
  exact (CopyGeneral.call_memory_away (CopyGeneral.callState source address scratch 20) key (scratch + 20#64) query 32 secondAway).trans
    (CopyGeneral.call_memory_away source address scratch query 20 firstAway)

theorem body_registered {ι : Type}
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address key scratch : BitVec 64)
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word key)))
    (scratchGlobal : source.globals.lookup (ofString "sk_buf") = some (.val (.word scratch)))
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (addressArena : AllocatedBytes.Arena address 20) (keyArena : AllocatedBytes.Arena key 32)
    (scratchArena : AllocatedBytes.Arena scratch 52) (installed : Input.OriginalCode.Installed source.code)
    (cutoff cursor : Nat) (objects : ι → TableFamily.Object) (accounts : List (BitVec 64))
    (family : TableFamily.Model source cursor objects) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property)
    (floors : ∀ index, cutoff ≤ (objects index).floor) (scratchBelow : scratch.toNat + 52 ≤ cutoff) (small : cutoff < 2^64)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned returned),post)) :
    price address key scratch ≤ source.clock ∧ returned = .val (.word scratch) ∧
      post.clock = source.clock - price address key scratch ∧
      TableFamily.Model post cursor objects ∧ TableFamily.ValuesHave post objects property ∧
      AccountDecode.Registry post cutoff cursor objects accounts ∧
      TableFamily.PersistentFrame cutoff cursor objects objects source post ∧
      (∀ query : BitVec 64, cutoff ≤ query.toNat → post.memory query = source.memory query) ∧
      post = emptyLocalsHOLFinite (resultState source address key scratch) := by
  obtain ⟨funded,answer,postEq⟩ := body_normal source post address key scratch addressLocal keyLocal scratchGlobal domain
    addressArena keyArena scratchArena installed returned normal
  subst post
  let target := emptyLocalsHOLFinite (resultState source address key scratch)
  have words (query : BitVec 64) (above : cutoff ≤ query.toNat) : target.memory query = source.memory query :=
    result_above source address key scratch cutoff scratchArena scratchBelow small query above
  have models : TableFamily.Model target cursor objects := family.of_range rfl rfl rfl floors (fun query above earlier => words query above)
  have tableValues := values.of_range source target cutoff cursor objects property family floors (fun query above earlier => words query above)
  have frame : TableFamily.PersistentFrame cutoff cursor objects objects source target := ⟨fun query above earlier outside => ⟨outside,words query above⟩⟩
  have nextRegistry := registry.framed source target cutoff cursor cursor objects objects accounts frame (Nat.le_refl _) rfl
  exact ⟨funded,answer,result_clock source address key scratch,models,tableValues,nextRegistry,frame,words,rfl⟩

end InitECandidate.Solver.Mpt.StorageKey

#print axioms InitECandidate.Solver.Mpt.StorageKey.result_above
#print axioms InitECandidate.Solver.Mpt.StorageKey.body_registered
