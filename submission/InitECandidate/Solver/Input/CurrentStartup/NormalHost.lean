import InitECandidate.Solver.Input.CurrentStartup.Code
import InitECandidate.Solver.Input.NormalHostCall
import InitECandidate.Solver.Input.NormalHostLoop
import InitECandidate.Solver.Input.TrapNoReturn

namespace InitECandidate.Solver.Input.CurrentStartup.NormalHost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

-- Generated compositional proofs over actual fixed syntax. No helper return,
-- successful allocation, readable buffer or oracle behavior is assumed.

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem trap_with (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .trap_with) := by
  intro source codeEq value returned
  have same : Code.body .trap_with = Trap.body := by
    simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
      declToHOL, funDeclToHOL, Guest.Software.guestFn_trap_with, Trap.body]
  rw [same] at returned
  exact (Trap.never_returns source value returned).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem alloc (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .alloc) := by
  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_alloc, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.conditional code _ _ _
  (NormalHostEffects.call_body code (some none) (Code.name .trap_with) _ (Code.formals .trap_with) (Code.body .trap_with) (Code.shape .trap_with)
  (Code.installed code installed .trap_with) (trap_with code installed))
  (NormalHostEffects.skip code))
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.conditional code _ _ _
  (NormalHostEffects.call_body code (some none) (Code.name .trap_with) _ (Code.formals .trap_with) (Code.body .trap_with) (Code.shape .trap_with)
  (Code.installed code installed .trap_with) (trap_with code installed))
  (NormalHostEffects.skip code))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.returned code _))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem sha256_init (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .sha256_init) := by
  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_sha256_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.returned code _)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem keccak_init (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .keccak_init) := by
  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_keccak_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.returned code _))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem ssz_init (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .ssz_init) := by
  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_ssz_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHostEffects.sequence code _ _
  (NormalHostEffects.conditional code _ _ _
  (NormalHostEffects.returned code _)
  (NormalHostEffects.skip code))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.returned code _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem keccak_f1600 (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .keccak_f1600) := by
  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_keccak_f1600, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.loop code _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.assign code _ _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.returned code _)))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem keccak_absorb_block (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .keccak_absorb_block) := by
  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_keccak_absorb_block, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.conditional code _ _ _
  (NormalHostEffects.loop code _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.assign code _ _ _)))
  (NormalHostEffects.loop code _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.assign code _ _ _))))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .keccak_f1600) _ (Code.formals .keccak_f1600) (Code.body .keccak_f1600) (Code.shape .keccak_f1600)
  (Code.installed code installed .keccak_f1600) (keccak_f1600 code installed))
  (NormalHostEffects.returned code _))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem memcpy (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .memcpy) := by
  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_memcpy, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.conditional code _ _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.loop code _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.assign code _ _ _))))))
  (NormalHostEffects.loop code _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.assign code _ _ _))))
  (NormalHostEffects.skip code))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.loop code _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.assign code _ _ _))))))))))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.loop code _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.assign code _ _ _)))
  (NormalHostEffects.returned code _)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem memzero (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .memzero) := by
  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_memzero, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.conditional code _ _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.loop code _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.assign code _ _ _))))))
  (NormalHostEffects.loop code _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.assign code _ _ _))))
  (NormalHostEffects.skip code))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.loop code _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.assign code _ _ _))))))))))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.loop code _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.assign code _ _ _)))
  (NormalHostEffects.returned code _)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem keccak256 (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .keccak256) := by
  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_keccak256, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (memzero code installed))
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.loop code _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .keccak_absorb_block) _ (Code.formals .keccak_absorb_block) (Code.body .keccak_absorb_block) (Code.shape .keccak_absorb_block)
  (Code.installed code installed .keccak_absorb_block) (keccak_absorb_block code installed))
  (NormalHostEffects.assign code _ _ _)))
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (memzero code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .memcpy) _ (Code.formals .memcpy) (Code.body .memcpy) (Code.shape .memcpy)
  (Code.installed code installed .memcpy) (memcpy code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .keccak_absorb_block) _ (Code.formals .keccak_absorb_block) (Code.body .keccak_absorb_block) (Code.shape .keccak_absorb_block)
  (Code.installed code installed .keccak_absorb_block) (keccak_absorb_block code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.conditional code _ _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.store code _ _))))
  (NormalHostEffects.call_body code (some none) (Code.name .memcpy) _ (Code.formals .memcpy) (Code.body .memcpy) (Code.shape .memcpy)
  (Code.installed code installed .memcpy) (memcpy code installed)))
  (NormalHostEffects.returned code _))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem mpt_init (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .mpt_init) := by
  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_mpt_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .keccak256) _ (Code.formals .keccak256) (Code.body .keccak256) (Code.shape .keccak256)
  (Code.installed code installed .keccak256) (keccak256 code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .keccak256) _ (Code.formals .keccak256) (Code.body .keccak256) (Code.shape .keccak256)
  (Code.installed code installed .keccak256) (keccak256 code installed))
  (NormalHostEffects.returned code _)))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem u256_ws_init (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .u256_ws_init) := by
  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_u256_ws_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHostEffects.sequence code _ _
  (NormalHostEffects.conditional code _ _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.skip code))
  (NormalHostEffects.returned code _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem secp256k1_init (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .secp256k1_init) := by
  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_secp256k1_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHostEffects.returned code _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem bn254_init (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .bn254_init) := by
  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_bn254_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHostEffects.sequence code _ _
  (NormalHostEffects.conditional code _ _ _
  (NormalHostEffects.returned code _)
  (NormalHostEffects.skip code))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.returned code _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem bls_consts_init (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .bls_consts_init) := by
  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_bls_consts_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHostEffects.sequence code _ _
  (NormalHostEffects.conditional code _ _ _
  (NormalHostEffects.returned code _)
  (NormalHostEffects.skip code))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.returned code _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem bls_lib_init (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .bls_lib_init) := by
  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_bls_lib_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .bls_consts_init) _ (Code.formals .bls_consts_init) (Code.body .bls_consts_init) (Code.shape .bls_consts_init)
  (Code.installed code installed .bls_consts_init) (bls_consts_init code installed))
  (NormalHostEffects.returned code _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem bls_precompiles_init (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .bls_precompiles_init) := by
  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_bls_precompiles_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHostEffects.sequence code _ _
  (NormalHostEffects.conditional code _ _ _
  (NormalHostEffects.returned code _)
  (NormalHostEffects.skip code))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .bls_lib_init) _ (Code.formals .bls_lib_init) (Code.body .bls_lib_init) (Code.shape .bls_lib_init)
  (Code.installed code installed .bls_lib_init) (bls_lib_init code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.returned code _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem ripemd160_init (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .ripemd160_init) := by
  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_ripemd160_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHostEffects.sequence code _ _
  (NormalHostEffects.conditional code _ _ _
  (NormalHostEffects.returned code _)
  (NormalHostEffects.skip code))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.returned code _))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem blake2_init (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .blake2_init) := by
  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_blake2_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHostEffects.sequence code _ _
  (NormalHostEffects.conditional code _ _ _
  (NormalHostEffects.returned code _)
  (NormalHostEffects.skip code))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.returned code _)))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem header_init (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .header_init) := by
  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_header_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHostEffects.sequence code _ _
  (NormalHostEffects.conditional code _ _ _
  (NormalHostEffects.returned code _)
  (NormalHostEffects.skip code))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (memzero code installed))
  (NormalHostEffects.returned code _))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem heap_mark (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .heap_mark) := by
  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_heap_mark, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHostEffects.returned code _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem heap_release (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .heap_release) := by
  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_heap_release, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.returned code _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem evm_init (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .evm_init) := by
  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_evm_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHostEffects.scoped_body code _ _ (Code.name .heap_mark) _ _ (Code.formals .heap_mark) (Code.body .heap_mark) (Code.shape .heap_mark)
  (Code.installed code installed .heap_mark) (heap_mark code installed)
  (NormalHostEffects.scoped_body code _ _ (Code.name .alloc) _ _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .heap_release) _ (Code.formals .heap_release) (Code.body .heap_release) (Code.shape .heap_release)
  (Code.installed code installed .heap_release) (heap_release code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .keccak256) _ (Code.formals .keccak256) (Code.body .keccak256) (Code.shape .keccak256)
  (Code.installed code installed .keccak256) (keccak256 code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.loop code _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.assign code _ _ _)))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (memzero code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (memzero code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.returned code _)))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem st_be32 (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .st_be32) := by
  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_st_be32, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.returned code _)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem bswap64 (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .bswap64) := by
  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_bswap64, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.assign code _ _ _)
  (NormalHostEffects.returned code _)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem st_be64 (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .st_be64) := by
  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_st_be64, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHostEffects.sequence code _ _
  (NormalHostEffects.conditional code _ _ _
  (NormalHostEffects.scoped_body code _ _ (Code.name .bswap64) _ _ (Code.formals .bswap64) (Code.body .bswap64) (Code.shape .bswap64)
  (Code.installed code installed .bswap64) (bswap64 code installed)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.store code _ _)
  (NormalHostEffects.returned code _)))
  (NormalHostEffects.skip code))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .st_be32) _ (Code.formals .st_be32) (Code.body .st_be32) (Code.shape .st_be32)
  (Code.installed code installed .st_be32) (st_be32 code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .st_be32) _ (Code.formals .st_be32) (Code.body .st_be32) (Code.shape .st_be32)
  (Code.installed code installed .st_be32) (st_be32 code installed))
  (NormalHostEffects.returned code _))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem addr_from_words (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .addr_from_words) := by
  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_addr_from_words, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .st_be32) _ (Code.formals .st_be32) (Code.body .st_be32) (Code.shape .st_be32)
  (Code.installed code installed .st_be32) (st_be32 code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .st_be64) _ (Code.formals .st_be64) (Code.body .st_be64) (Code.shape .st_be64)
  (Code.installed code installed .st_be64) (st_be64 code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .st_be64) _ (Code.formals .st_be64) (Code.body .st_be64) (Code.shape .st_be64)
  (Code.installed code installed .st_be64) (st_be64 code installed))
  (NormalHostEffects.returned code _))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem fork_init (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .fork_init) := by
  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_fork_init, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (memzero code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero)
  (Code.installed code installed .memzero) (memzero code installed))
  (NormalHostEffects.declared code _ _ _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.loop code _ _
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.assign code _ _ _)))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.byte_store code _ _)
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (addr_from_words code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (addr_from_words code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (addr_from_words code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (addr_from_words code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (addr_from_words code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (addr_from_words code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .addr_from_words) _ (Code.formals .addr_from_words) (Code.body .addr_from_words) (Code.shape .addr_from_words)
  (Code.installed code installed .addr_from_words) (addr_from_words code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some (some (.global, _))) (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (alloc code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .st_be64) _ (Code.formals .st_be64) (Code.body .st_be64) (Code.shape .st_be64)
  (Code.installed code installed .st_be64) (st_be64 code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .st_be64) _ (Code.formals .st_be64) (Code.body .st_be64) (Code.shape .st_be64)
  (Code.installed code installed .st_be64) (st_be64 code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .st_be64) _ (Code.formals .st_be64) (Code.body .st_be64) (Code.shape .st_be64)
  (Code.installed code installed .st_be64) (st_be64 code installed))
  (NormalHostEffects.sequence code _ _
  (NormalHostEffects.call_body code (some none) (Code.name .st_be64) _ (Code.formals .st_be64) (Code.body .st_be64) (Code.shape .st_be64)
  (Code.installed code installed .st_be64) (st_be64 code installed))
  (NormalHostEffects.returned code _)))))))))))))))))))))))))))

end InitECandidate.Solver.Input.CurrentStartup.NormalHost

#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.trap_with
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.alloc
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.sha256_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.keccak_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.ssz_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.keccak_f1600
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.keccak_absorb_block
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.memcpy
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.memzero
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.keccak256
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.mpt_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.u256_ws_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.secp256k1_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.bn254_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.bls_consts_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.bls_lib_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.bls_precompiles_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.ripemd160_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.blake2_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.header_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.heap_mark
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.heap_release
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.evm_init
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.st_be32
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.bswap64
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.st_be64
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.addr_from_words
#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.fork_init
