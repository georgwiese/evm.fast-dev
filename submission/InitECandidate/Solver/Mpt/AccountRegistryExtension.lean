import InitECandidate.Solver.Mpt.AccountRegistry

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack

/-- Real account registration retains old members and introduces only objects
allocated at or beyond the old heap. This tracks provenance independently of
the scratch/witness boundary used by physical memory frames. -/
structure Registry.Extension (accounts next : List (BitVec 64)) (cursor : Nat) : Prop where
  included : ∀ account,account∈accounts → account∈next
  fresh : ∀ account,account∈next → account∈accounts ∨ cursor≤account.toNat

theorem Registry.Extension.known {accounts next : List (BitVec 64)} {cursor : Nat}
    (extension : Registry.Extension accounts next cursor) :
    ∀ value : BitVec 64,Registry.Known accounts value → Registry.Known next value :=
  Registry.known_mono accounts next extension.included

instance {accounts next : List (BitVec 64)} {cursor : Nat} :
    CoeFun (Registry.Extension accounts next cursor)
      (fun _=>∀ value : BitVec 64,Registry.Known accounts value → Registry.Known next value) :=
  ⟨fun extension=>extension.known⟩

theorem Registry.Extension.known_function {accounts next : List (BitVec 64)} {cursor : Nat}
    (extension : Registry.Extension accounts next cursor) :
    ∀ value : BitVec 64,Registry.Known accounts value → Registry.Known next value := extension

theorem Registry.Extension.refl (accounts : List (BitVec 64)) (cursor : Nat) : Registry.Extension accounts accounts cursor :=
  ⟨fun account member=>member,fun account member=>Or.inl member⟩

theorem Registry.Extension.append (accounts : List (BitVec 64)) (fresh : BitVec 64) (cursor : Nat) (after : cursor≤fresh.toNat) :
    Registry.Extension accounts (accounts++[fresh]) cursor := by
  refine ⟨fun account member=>List.mem_append.mpr (Or.inl member),?_⟩
  intro account member
  have choices : account∈accounts ∨ account=fresh := by simpa using member
  rcases choices with old | rfl
  · exact Or.inl old
  · exact Or.inr after

theorem Registry.Extension.lower {accounts next : List (BitVec 64)} {cursor lower : Nat}
    (extension : Registry.Extension accounts next cursor) (earlier : lower≤cursor) : Registry.Extension accounts next lower := by
  refine ⟨extension.included,?_⟩
  intro account member
  rcases extension.fresh account member with old | fresh
  · exact Or.inl old
  · exact Or.inr (Nat.le_trans earlier fresh)

theorem Registry.Extension.trans {accounts middle next : List (BitVec 64)} {cursor middleCursor : Nat}
    (first : Registry.Extension accounts middle cursor) (second : Registry.Extension middle next middleCursor)
    (forward : cursor≤middleCursor) : Registry.Extension accounts next cursor := by
  refine ⟨fun account member=>second.included account (first.included account member),?_⟩
  intro account member
  rcases second.fresh account member with old | fresh
  · exact first.fresh account old
  · exact Or.inr (Nat.le_trans forward fresh)

/-- The real old heap bound and registration provenance retain separation
from the whole journal reservation, without conflating it with the immutable
witness's earlier scratch boundary. -/
theorem Registry.Extension.journal_apart {accounts next : List (BitVec 64)} {cursor base cap : Nat}
    (extension : Registry.Extension accounts next cursor)
    (apart : ∀ account,account∈accounts → account.toNat+56≤base ∨ base+32*cap≤account.toNat)
    (after : base+32*cap≤cursor) :
    ∀ account,account∈next → account.toNat+56≤base ∨ base+32*cap≤account.toNat := by
  intro account member
  rcases extension.fresh account member with old | fresh
  · exact apart account old
  · exact Or.inr (Nat.le_trans after fresh)

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.Registry.Extension.known_function
#print axioms InitECandidate.Solver.Mpt.AccountDecode.Registry.Extension.refl
#print axioms InitECandidate.Solver.Mpt.AccountDecode.Registry.Extension.append
#print axioms InitECandidate.Solver.Mpt.AccountDecode.Registry.Extension.lower
#print axioms InitECandidate.Solver.Mpt.AccountDecode.Registry.Extension.trans
#print axioms InitECandidate.Solver.Mpt.AccountDecode.Registry.Extension.journal_apart
