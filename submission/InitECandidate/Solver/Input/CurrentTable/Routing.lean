import InitECandidate.Solver.Input.CurrentTable.KeyBits

namespace InitECandidate.Solver.Input.CurrentTable

/-- Logical information needed in addition to the physical node image.
Representatives are actual leaf keys at leaves; an internal representative
summarizes the common prefix of its entire subtree. Actual insertion must
establish and preserve these facts. -/
structure Routing (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat)
    (left right : BitVec 64 → BitVec 64) (keys : BitVec 64 → KeyBits.Key) : Prop where
  nonzero : ∀ node,valid node → node ≠ 0#64
  leftMember : ∀ node,valid node → bits node < 256 → valid (left node)
  rightMember : ∀ node,valid node → bits node < 256 → valid (right node)
  leftGreater : ∀ node,valid node → bits node < 256 → bits node < bits (left node)
  rightGreater : ∀ node,valid node → bits node < 256 → bits node < bits (right node)
  leftPrefix : ∀ node,valid node → bits node < 256 → ∀ position,position < bits node →
    KeyBits.bit (keys (left node)) position = KeyBits.bit (keys node) position
  rightPrefix : ∀ node,valid node → bits node < 256 → ∀ position,position < bits node →
    KeyBits.bit (keys (right node)) position = KeyBits.bit (keys node) position
  leftDigit : ∀ node,valid node → bits node < 256 → KeyBits.bit (keys (left node)) (bits node) = false
  rightDigit : ∀ node,valid node → bits node < 256 → KeyBits.bit (keys (right node)) (bits node) = true

/-- A finite prefix of the actual query-directed child route. This relation
supplies no completed execution, funding or successful future leaf search. -/
inductive Route (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64)
    (query : KeyBits.Key) : BitVec 64 → BitVec 64 → Prop where
  | here (node) : Route bits left right query node node
  | left (node finish) (internal : bits node < 256) (digit : KeyBits.bit query (bits node) = false)
      (tail : Route bits left right query (left node) finish) : Route bits left right query node finish
  | right (node finish) (internal : bits node < 256) (digit : KeyBits.bit query (bits node) = true)
      (tail : Route bits left right query (right node) finish) : Route bits left right query node finish

theorem Route.trans {bits left right query a b c}
    (front : Route bits left right query a b) (back : Route bits left right query b c) : Route bits left right query a c := by
  induction front with
  | here node => exact back
  | left node finish internal digit tail ih => exact .left node c internal digit (ih back)
  | right node finish internal digit tail ih => exact .right node c internal digit (ih back)

theorem Route.valid {valid bits left right keys query root finish}
    (model : Routing valid bits left right keys) (route : Route bits left right query root finish)
    (member : valid root) : valid finish := by
  induction route with
  | here node => exact member
  | left node finish internal digit tail ih => exact ih (model.leftMember node member internal)
  | right node finish internal digit tail ih => exact ih (model.rightMember node member internal)

theorem Route.bit_mono {valid bits left right keys query root finish}
    (model : Routing valid bits left right keys) (route : Route bits left right query root finish)
    (member : valid root) : bits root ≤ bits finish := by
  induction route with
  | here node => omega
  | left node finish internal digit tail ih =>
    have next := ih (model.leftMember node member internal)
    have greater := model.leftGreater node member internal
    omega
  | right node finish internal digit tail ih =>
    have next := ih (model.rightMember node member internal)
    have greater := model.rightGreater node member internal
    omega

/-- Every descendant representative retains the real common subtree prefix. -/
theorem Route.prefix {valid bits left right keys query root finish}
    (model : Routing valid bits left right keys) (route : Route bits left right query root finish)
    (member : valid root) (position : Nat) (inside : position < bits root) :
    KeyBits.bit (keys finish) position = KeyBits.bit (keys root) position := by
  induction route with
  | here node => rfl
  | left node finish internal digit tail ih =>
    have greater := model.leftGreater node member internal
    exact (ih (model.leftMember node member internal) (by omega)).trans (model.leftPrefix node member internal position inside)
  | right node finish internal digit tail ih =>
    have greater := model.rightGreater node member internal
    exact (ih (model.rightMember node member internal) (by omega)).trans (model.rightPrefix node member internal position inside)

/-- A route ending at a leaf must leave every internal node through the
child selected by its query. -/
theorem Route.head {bits left right query root leaf}
    (route : Route bits left right query root leaf) (internal : bits root < 256) (marked : bits leaf = 256) :
    Route bits left right query (if KeyBits.bit query (bits root) then right root else left root) leaf := by
  cases route with
  | here node => omega
  | left node finish active digit tail => simpa [digit] using tail
  | right node finish active digit tail => simpa [digit] using tail

/-- At a traversed split the reached leaf has the query's chosen digit. -/
theorem Route.split {valid bits left right keys query root leaf}
    (model : Routing valid bits left right keys) (route : Route bits left right query root leaf)
    (member : valid root) (internal : bits root < 256) (marked : bits leaf = 256) :
    KeyBits.bit (keys leaf) (bits root) = KeyBits.bit query (bits root) := by
  cases route with
  | here node => omega
  | left node finish active digit tail =>
    have below := model.leftGreater root member active
    exact (tail.prefix model (model.leftMember root member active) (bits root) below).trans
      ((model.leftDigit root member active).trans digit.symm)
  | right node finish active digit tail =>
    have below := model.rightGreater root member active
    exact (tail.prefix model (model.rightMember root member active) (bits root) below).trans
      ((model.rightDigit root member active).trans digit.symm)

/-- The insertion stop cannot have its bit equal to the first mismatch:
that equality contradicts the leaf reached by the earlier real lookup. -/
theorem Route.stop_strict {valid bits left right keys query root leaf position}
    (model : Routing valid bits left right keys) (route : Route bits left right query root leaf)
    (member : valid root) (marked : bits leaf = 256)
    (difference : KeyBits.First query (keys leaf) position) (inside : position < 256)
    (stopped : position ≤ bits root) : position < bits root := by
  by_contra notStrict
  have same : bits root = position := by omega
  have selected := route.split model member (by omega) marked
  rw [same] at selected
  exact difference.unequal inside selected.symm

end InitECandidate.Solver.Input.CurrentTable

#print axioms InitECandidate.Solver.Input.CurrentTable.Route.prefix
#print axioms InitECandidate.Solver.Input.CurrentTable.Route.head
#print axioms InitECandidate.Solver.Input.CurrentTable.Route.split
#print axioms InitECandidate.Solver.Input.CurrentTable.Route.stop_strict
