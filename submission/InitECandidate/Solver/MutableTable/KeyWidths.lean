namespace InitECandidate.Solver.MutableTable.KeyHash

/-- Exactly the key widths used by original table constructors. -/
inductive Kind where | account | indexedAccount | word | storage | indexedStorage
  deriving DecidableEq

def keySize : Kind → Nat | .account => 20 | .indexedAccount => 28 | .word => 32 | .storage => 52 | .indexedStorage => 60

theorem key_size_small (kind : Kind) : keySize kind ≤ 64 := by cases kind <;> decide

end InitECandidate.Solver.MutableTable.KeyHash

#print axioms InitECandidate.Solver.MutableTable.KeyHash.key_size_small
