import InitECandidate.Solver.Arenas.Arithmetic

namespace InitECandidate.Solver.Arenas

/-- Word locations outside the live allocation interval. Persistent inputs
are below the lower cursor; older scratch objects are above the upper one. -/
def Outside (lower upper query : BitVec 64) : Prop :=
  query.toNat < lower.toNat ∨ upper.toNat ≤ query.toNat

end InitECandidate.Solver.Arenas
