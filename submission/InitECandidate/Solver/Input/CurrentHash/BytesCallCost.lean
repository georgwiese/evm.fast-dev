import InitECandidate.Solver.Input.CurrentHash.BytesListCost
import InitECandidate.Solver.Input.CurrentHash.BytesVectorCost

namespace InitECandidate.Solver.Input.CurrentHash.BytesCallCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

inductive Kind where | vector | list

def routine : Kind → Code.Routine | .vector => .htr_bytes_vector | .list => .htr_bytes_list
def formals : Kind → List (MlS × ShapeHOL)
  | .vector => [(ofString "p", .one), (ofString "n", .one), (ofString "out", .one)]
  | .list => [(ofString "p", .one), (ofString "n", .one), (ofString "limit_chunks", .one), (ofString "out", .one)]
def values (kind : Kind) (p limit out : BitVec 64) (n : Nat) : List (ValueHOL 64) := match kind with
  | .vector => [.val (.word p), .val (.word (BitVec.ofNat 64 n)), .val (.word out)]
  | .list => [.val (.word p), .val (.word (BitVec.ofNat 64 n)), .val (.word limit), .val (.word out)]
def rawLocals (kind : Kind) (p limit out : BitVec 64) (n : Nat) (name : MlS) : Option (ValueHOL 64) := match kind with
  | .vector => if name = ofString "out" then some (.val (.word out)) else if name = ofString "n" then some (.val (.word (BitVec.ofNat 64 n)))
      else if name = ofString "p" then some (.val (.word p)) else none
  | .list => if name = ofString "out" then some (.val (.word out)) else if name = ofString "limit_chunks" then some (.val (.word limit))
      else if name = ofString "n" then some (.val (.word (BitVec.ofNat 64 n))) else if name = ofString "p" then some (.val (.word p)) else none

theorem entry (kind : Kind) (code) (installed : OriginalCode.Installed code) :
    code.lookup (Code.name (routine kind)) = some (formals kind, Code.body (routine kind), .one) := by
  have checked := Code.installed code installed (routine kind)
  cases kind <;>
    simpa only [routine, Code.formals, Code.shape, Code.entry, Code.declaration, formals,
      GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL,
      Guest.Software.guestFn_htr_bytes_vector, Guest.Software.guestFn_htr_bytes_list,
      shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using checked

theorem environment (kind : Kind) (code) (installed : OriginalCode.Installed code) (p limit out : BitVec 64) (n : Nat) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite code.lookup (Code.name (routine kind)) (values kind p limit out n) = some (Code.body (routine kind), callee, .one) ∧
      callee.lookup (ofString "p") = some (.val (.word p)) ∧ callee.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n))) ∧
      callee.lookup (ofString "out") = some (.val (.word out)) ∧
      (kind = .list → callee.lookup (ofString "limit_chunks") = some (.val (.word limit))) := by
  have valid : ((formals kind).map Prod.fst).Nodup ∧ (formals kind).length = (values kind p limit out n).length ∧
      ((formals kind).zip (values kind p limit out n)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)) = true := by
    cases kind <;> refine ⟨by decide, rfl, ?_⟩ <;> simp [formals, values, shapeEqHOL, shapeOfHOLExact]
  have raw : lookupCodeHOLExact code.lookup (Code.name (routine kind)) (values kind p limit out n) =
      some (Code.body (routine kind), rawLocals kind p limit out n, .one) := by
    simp only [lookupCodeHOLExact, entry kind code installed]
    rw [if_pos valid]
    cases kind <;> rfl
  obtain ⟨callee, called, locals⟩ := CodeEnvironment.finite_lookup code.lookup _ _ _ _ .one raw
  refine ⟨callee, called, ?_, ?_, ?_, ?_⟩
  · rw [locals]; cases kind <;> simp [rawLocals,
      show ofString "p" ≠ ofString "out" from by decide, show ofString "p" ≠ ofString "n" from by decide,
      show ofString "p" ≠ ofString "limit_chunks" from by decide]
  · rw [locals]; cases kind <;> simp [rawLocals,
      show ofString "n" ≠ ofString "out" from by decide, show ofString "n" ≠ ofString "limit_chunks" from by decide]
  · rw [locals]; cases kind <;> simp [rawLocals]
  · intro same; subst kind; rw [locals]; simp [rawLocals, show ofString "limit_chunks" ≠ ofString "out" from by decide]

def overhead : Kind → Nat | .vector => 53 | .list => 100

/-- Actual vector/list callers with their real ABI inputs. The chunk bound
comes from n; a list's declared Merkle limit is additionally bounded. No heap,
workspace, mapped input/output, successful hash or future funding is assumed. -/
theorem cost (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p limit out : BitVec 64) (n budget : Nat)
    (installed : OriginalCode.Installed source.code) (lengthSmall : n + 64 < 2^64) (small : budget < 58)
    (chunksBound : PackBytes.chunks n ≤ 2^budget) (limitBound : kind = .list → limit.toNat ≤ 2^budget)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values kind p limit out n))
    (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (Code.name (routine kind)) arguments) = (result, post))
    (notTimeout : result ≠ some .timeOut) : source.clock - post.clock ≤ PackBytesCost.price n + 88*PackBytes.chunks n + 4*budget + overhead kind := by
  obtain ⟨callee, called, pointer, length, output, maximum⟩ := environment kind source.code installed p limit out n
  have priced : ∀ result target, evaluateHOLFiniteState (callEntryStateHOLFinite source callee) (Code.body (routine kind)) = (result, target) → result ≠ some .timeOut →
      (callEntryStateHOLFinite source callee).clock - target.clock ≤ PackBytesCost.price n + 88*PackBytes.chunks n + 4*budget + (overhead kind - 1) := by
    intro result target evaluated notTimeout
    cases kind with
    | vector => exact BytesVectorCost.cost (callEntryStateHOLFinite source callee) target p out n budget ⟨pointer, length, output⟩ installed lengthSmall small chunksBound result evaluated notTimeout
    | list => exact BytesListCost.cost (callEntryStateHOLFinite source callee) target p limit out n budget ⟨pointer, length, maximum rfl, output⟩ installed lengthSmall small chunksBound (limitBound rfl) result evaluated notTimeout
  have total := ClockCost.call_current_terminating source post destination (Code.name (routine kind)) arguments (values kind p limit out n)
    (Code.body (routine kind)) callee .one (PackBytesCost.price n + 88*PackBytes.chunks n + 4*budget + (overhead kind - 1)) args called priced result actual notTimeout
  cases kind <;> simpa only [overhead] using total

end InitECandidate.Solver.Input.CurrentHash.BytesCallCost

#print axioms InitECandidate.Solver.Input.CurrentHash.BytesCallCost.entry
#print axioms InitECandidate.Solver.Input.CurrentHash.BytesCallCost.environment
#print axioms InitECandidate.Solver.Input.CurrentHash.BytesCallCost.cost
