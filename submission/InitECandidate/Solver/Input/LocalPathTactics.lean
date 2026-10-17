import InitECandidate.Solver.Input.LocalPath

/-! Structural proof construction for actual local-preserving prefixes. Every
constructor is checked by the kernel; unsupported syntax fails elaboration. -/
namespace InitECandidate.Solver.Input

syntax "prove_local_prefix" : tactic
macro_rules
  | `(tactic| prove_local_prefix) => `(tactic|
      first
      | exact LocalPrefix.skip
      | exact LocalPrefix.store _ _
      | apply LocalPrefix.assign; decide
      | apply LocalPrefix.call none; intro name impossible; cases impossible
      | apply LocalPrefix.call (some _); intro name same; cases same; decide
      | apply LocalPrefix.seq <;> prove_local_prefix
      | apply LocalPrefix.ite <;> prove_local_prefix
      | apply LocalPrefix.loop <;> prove_local_prefix
      | apply LocalPrefix.dec
        · decide
        · prove_local_prefix
      | apply LocalPrefix.decCall
        · decide
        · prove_local_prefix)

syntax "prove_local_path" : tactic
macro_rules
  | `(tactic| prove_local_path) => `(tactic|
      first
      | exact LocalPath.here
      | apply LocalPath.seq
        · prove_local_prefix
        · prove_local_path
      | apply LocalPath.dec _ _ _ (by decide)
        prove_local_path
      | apply LocalPath.decCall _ _ _ _ (by decide)
        prove_local_path)

end InitECandidate.Solver.Input
