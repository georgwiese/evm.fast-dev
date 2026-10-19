import InitECandidate.Solver.Mpt.AccountImage
import InitECandidate.Solver.MutableTable.FamilyPersistentFrame

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable

/-- Current real account objects, before the heap and separated from each
other. Every byte position lies outside every live table pool, including
when records occur between older and newer pools. -/
structure Registry {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cutoff cursor : Nat)
    (objects : ι → TableFamily.Object) (accounts : List (BitVec 64)) : Prop where
  distinct : accounts.Nodup
  images : ∀ account,account∈accounts → Nonempty (Image source account)
  above : ∀ account,account∈accounts → cutoff≤account.toNat
  before : ∀ account,account∈accounts → account.toNat+56≤cursor
  separated : ∀ first,first∈accounts → ∀ second,second∈accounts → first≠second →
    first.toNat+56≤second.toNat ∨ second.toNat+56≤first.toNat
  objectOutside : ∀ account,account∈accounts → ∀ offset : Nat,offset<56 → TableFamily.Outside objects (account+BitVec.ofNat 64 offset)

theorem Registry.referencesOutside {ι : Type} {source : PanSemStateFiniteExact 64 Guest.HostMemory} {cutoff cursor : Nat}
    {objects : ι → TableFamily.Object} {accounts : List (BitVec 64)} (registry : Registry source cutoff cursor objects accounts)
    (account : BitVec 64) (member : account∈accounts) (offset : Nat) (selected : offset=40 ∨ offset=48) :
    TableFamily.Outside objects (account+BitVec.ofNat 64 offset) := registry.objectOutside account member offset (by omega)

/-- An occupied cache value is the actual absent sentinel or a registered
account pointer. Uninitialized unused value cells impose no obligation. -/
def Registry.Known (accounts : List (BitVec 64)) (value : BitVec 64) : Prop := value=1#64 ∨ value∈accounts

theorem Registry.known_mono (accounts next : List (BitVec 64)) (subset : ∀ value,value∈accounts → value∈next)
    (value : BitVec 64) (known : Registry.Known accounts value) : Registry.Known next value := by
  rcases known with absent | member
  · exact Or.inl absent
  · exact Or.inr (subset value member)

theorem Registry.known_image {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cutoff cursor : Nat)
    (objects : ι → TableFamily.Object) (accounts : List (BitVec 64)) (registry : Registry source cutoff cursor objects accounts)
    (value : BitVec 64) (known : Registry.Known accounts value) (present : value≠1#64) : Nonempty (Image source value) := by
  rcases known with absent | member
  · exact (present absent).elim
  · exact registry.images value member

theorem Registry.empty {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cutoff cursor : Nat) (objects : ι → TableFamily.Object) :
    Registry source cutoff cursor objects [] := by
  constructor
  · simp
  all_goals intro account member; cases member

theorem Output.slot_number (account : BitVec 64) (output : Output account) (offset : Nat) (inside : offset<56) :
    (account+BitVec.ofNat 64 offset).toNat=account.toNat+offset :=
  byteAddress_toNat account offset (by have := output.upper; omega)

/-- Actual persistent memory/separation frames retain every old account
image, even through relocated table arrays and unrelated allocations. -/
theorem Registry.framed {ι : Type} (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cutoff cursor nextCursor : Nat)
    (objects next : ι → TableFamily.Object) (accounts : List (BitVec 64)) (registry : Registry source cutoff cursor objects accounts)
    (frame : TableFamily.PersistentFrame cutoff cursor objects next source target) (forward : cursor≤nextCursor)
    (domain : target.memaddrs=source.memaddrs) : Registry target cutoff nextCursor next accounts := by
  have refs (account : BitVec 64) (member : account∈accounts) (offset : Nat) (inside : offset<56) :
      TableFamily.Outside next (account+BitVec.ofNat 64 offset) ∧ target.memory (account+BitVec.ofNat 64 offset)=source.memory (account+BitVec.ofNat 64 offset) := by
    obtain ⟨image⟩ := registry.images account member
    have number := image.output.slot_number account offset inside
    apply frame.words _
    · rw [number]; have := registry.above account member; omega
    · rw [number]; have := registry.before account member; omega
    · exact registry.objectOutside account member offset inside
  refine ⟨registry.distinct,?_,registry.above,?_,registry.separated,fun account member offset inside=>(refs account member offset inside).1⟩
  · intro account member
    obtain ⟨image⟩ := registry.images account member
    exact ⟨Image.of_agreement source target account image domain (refs account member 40 (by decide)).2 (refs account member 48 (by decide)).2⟩
  · intro account member
    have := registry.before account member
    omega

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.Registry.known_mono
#print axioms InitECandidate.Solver.Mpt.AccountDecode.Registry.known_image
#print axioms InitECandidate.Solver.Mpt.AccountDecode.Registry.empty
#print axioms InitECandidate.Solver.Mpt.AccountDecode.Output.slot_number
#print axioms InitECandidate.Solver.Mpt.AccountDecode.Registry.framed

#print axioms InitECandidate.Solver.Mpt.AccountDecode.Registry.referencesOutside
