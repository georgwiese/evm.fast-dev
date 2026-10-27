import InitECandidate.Solver.Input.ZeroUnmapped
import InitECandidate.Solver.WitnessRadix.ZeroEnvironment
import InitECandidate.Solver.Input.OriginalEntry
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.IgnoredCallNormal

namespace InitECandidate.Solver.Input.ZeroUnmapped
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix

set_option maxRecDepth 100000 in
theorem zero_installed (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one) := by
  have found := OriginalCode.indexed code installed 12
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_memzero) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Zero.body, Zero.formals,
    Guest.Software.guestFn_memzero, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using found

/-- The actual current ignored memzero call cannot enter its caller suffix
after trying to clear at least32bytes at an aligned unmapped scratch address.
Errors and timeouts need no future read/store or oracle behavior assumption. -/
theorem call_not_normal {F : Type} (source post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (dst : BitVec 64) (length : Nat)
    (small : length + 32 < 2^64) (large : 32 ≤ length) (aligned : dst.toNat % 8 = 0)
    (domain : source.memaddrs = InitE.ordinaryDomain) (below : dst.toNat < InitE.sourceBase)
    (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      arguments = some (Zero.values dst length)) :
    evaluateHOLFiniteState source (.call (some (none, none)) (ofString "memzero") arguments) ≠ (none, post) := by
  intro normal
  obtain ⟨callee, called, dstCell, lengthCell⟩ := Zero.environment source.code.lookup dst length
    (zero_installed source.code installed)
  obtain ⟨positive, target, returned, actual⟩ := CallNormal.ignored_callee_return source post (ofString "memzero")
    arguments (Zero.values dst length) Zero.body callee .one args called normal
  exact body_no_return (callEntryStateHOLFinite source callee) dst length small large aligned
    domain below dstCell lengthCell returned (congrArg Prod.fst actual)

end InitECandidate.Solver.Input.ZeroUnmapped

#print axioms InitECandidate.Solver.Input.ZeroUnmapped.zero_installed
#print axioms InitECandidate.Solver.Input.ZeroUnmapped.call_not_normal
