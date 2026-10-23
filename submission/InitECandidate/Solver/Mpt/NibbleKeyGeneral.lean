import InitECandidate.Solver.Mpt.NibbleKeySecureCost
import InitECandidate.Solver.Mpt.NibbleKeyUnsecured

namespace InitECandidate.Solver.Mpt.NibbleKey
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def nibbleLength (flag : BitVec 64) (length : Nat) : Nat:=if flag=0#64 then 2*length else 64
def nibbleValue (pointer : BitVec 64) (length : Nat) : ValueHOL 64:=.rStruct [.val (.word pointer),.val (.word (BitVec.ofNat 64 length))]

theorem nibble_length_bound (flag : BitVec 64) (length : Nat) (small : length≤32) : nibbleLength flag length≤64 := by
  unfold nibbleLength
  split <;> omega

/-- The actual original helper for either current flag. Secure callers
hash and convert32 bytes; unsecured callers convert the actual short key.
Both derive their real tuple, bounded nibble span, allocation, control
frame and protected memory from a genuine normal return. -/
theorem general_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (m flag key stp pad hash heap : BitVec 64) (length : Nat) (small : length≤32)
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain) (little : source.be=false)
    (mCell : source.locals.lookup (ofString "m")=some (.val (.word m)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 length))))
    (mapped : source.memaddrs (m+8#64)) (cell : source.memory (m+8#64)=.word flag)
    (hashCell : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word hash)))
    (data : Keccak256.EntryData source stp key pad hash length)
    (hashArena : AllocatedBytes.Arena hash 32) (hashBefore : hash.toNat+32≤heap.toNat)
    (inputArena : AllocatedBytes.Arena key length) (inputBefore : key.toNat+length≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    AllocatedBytes.Arena heap (nibbleLength flag length) ∧ value=nibbleValue heap (nibbleLength flag length) ∧
      TrieWalk.KeyView target.memory target.memaddrs target.be heap (nibbleLength flag length) ∧
      source.clock-target.clock≤217 ∧
      KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl (PersistentAlloc.post source heap (BitVec.ofNat 64 (nibbleLength flag length))) ∧
      ∀ query : BitVec 64,Keccak256.Protected stp pad hash query→
        (query.toNat<heap.toNat ∨ heap.toNat+nibbleLength flag length≤query.toNat)→target.memory query=source.memory query := by
  by_cases zero : flag=0#64
  · subst flag
    simp only [nibbleLength,if_pos rfl]
    obtain ⟨arena,answer,view,cost,fields,memory⟩:=unsecured_normal source target m key heap length small installed domain little mCell keyCell lengthCell mapped cell heapCell frontier aligned inputArena inputBefore value normal
    have control:=KeccakAbsorb.hashControl_of_control (PersistentAlloc.post source heap (BitVec.ofNat 64 (2*length))) target fields
    have quotient : length/4≤8:=Nat.div_le_div_right small
    exact ⟨arena,answer,view,(by omega),control,fun query _ outside=>memory query outside⟩
  · simp only [nibbleLength,if_neg zero]
    obtain ⟨arena,answer,view,cost,control,memory⟩:=secured_normal source target m flag key stp pad hash heap length small installed domain little mCell keyCell lengthCell mapped cell zero hashCell data hashArena hashBefore
      heapCell frontier aligned value normal
    have price : Keccak256.price length=202:=by
      simp [Keccak256.price,Nat.div_eq_of_lt (by omega : length<136)]
    rw [price] at cost
    exact ⟨arena,answer,view,(by omega),control,memory⟩

/-- All outcomes for both original flags, within217 source call/loop
ticks for actual input keys of at most32 bytes. Failed hash/allocator/
converter execution is included and requires no successful future model. -/
theorem general_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (m flag key stp pad hash : BitVec 64) (length : Nat) (small : length≤32)
    (installed : Input.OriginalCode.Installed source.code)
    (mCell : source.locals.lookup (ofString "m")=some (.val (.word m)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 length))))
    (mapped : source.memaddrs (m+8#64)) (cell : source.memory (m+8#64)=.word flag)
    (hashCell : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word hash)))
    (data : Keccak256.EntryData source stp key pad hash length) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤217 := by
  by_cases zero : flag=0#64
  · subst flag
    have cost:=unsecured_cost source m key length (by omega) installed mCell keyCell lengthCell mapped cell
    have quotient : length/4≤8:=Nat.div_le_div_right small
    omega
  · have cost:=secured_cost source m flag key stp pad hash length (by omega) installed mCell keyCell lengthCell mapped cell zero hashCell data
    have price : Keccak256.price length=202:=by simp [Keccak256.price,Nat.div_eq_of_lt (by omega : length<136)]
    rwa [price] at cost

end InitECandidate.Solver.Mpt.NibbleKey

#print axioms InitECandidate.Solver.Mpt.NibbleKey.nibble_length_bound
#print axioms InitECandidate.Solver.Mpt.NibbleKey.general_normal
#print axioms InitECandidate.Solver.Mpt.NibbleKey.general_cost
