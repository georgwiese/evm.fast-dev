import InitECandidate.Solver.WitnessRadix.ZeroCall
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment

namespace InitECandidate.Solver.WitnessRadix.Zero
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "memzero")=some (formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 12 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_memzero) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,
    Guest.guestFn_memzero,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

/-- Current mapped/aligned geometry gives an all-outcome source-clock
bound. Insufficient clocks stop within their initial budget; with enough
clocks, the existing exact original execution supplies the actual result. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arguments : List (ExpHOL 64)) (dst : BitVec 64) (length : Nat)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (values dst length))
    (code : source.code.lookup (ofString "memzero")=some (formals,body,.one))
    (small : length+32<2^64) (multiple : length%8=0) (aligned : dst.toNat%8=0)
    (mapped : ∀ offset,offset+8≤length → offset%8=0 → source.memaddrs (byteAddress dst offset)) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memzero") arguments)).2.clock≤price length+1 := by
  by_cases enough : price length+1≤source.clock
  · rw [call_execute source arguments dst length args code small multiple aligned mapped enough]
    change source.clock-(source.clock-(price length+1))≤price length+1
    omega
  · have bounded := Nat.sub_le source.clock (evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memzero") arguments)).2.clock
    omega

end InitECandidate.Solver.WitnessRadix.Zero

#print axioms InitECandidate.Solver.WitnessRadix.Zero.original_code
#print axioms InitECandidate.Solver.WitnessRadix.Zero.call_cost
