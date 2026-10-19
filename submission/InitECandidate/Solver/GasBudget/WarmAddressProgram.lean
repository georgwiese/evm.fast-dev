import InitECandidate.Solver.MutableTable.HasNormalCall
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.GasBudget.WarmAddress
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

def body : ProgHOL 64 := match Guest.guestFn_is_warm_address with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "addr", .one)]
def afterHas : ProgHOL 64 := .return (localVar "h")

theorem body_shape : body = .decCall (ofString "h") .one (ofString "htab_has") [frameLoad 168#64, localVar "addr"] afterHas := by
  simp only [body, Guest.guestFn_is_warm_address, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    afterHas, localVar, frameLoad, frameAddress]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "is_warm_address") = some (formals, body, .one) := by
  have checked := Input.OriginalCode.indexed code installed 429 (OriginalCodeEnvironment.originalEntry Guest.guestFn_is_warm_address) (by rfl)
  simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, body, formals,
    Guest.guestFn_is_warm_address, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem has_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "htab_has") = some (Has.formals, Has.body, .one) := by
  have checked := Input.OriginalCode.indexed code installed 121 (OriginalCodeEnvironment.originalEntry Guest.guestFn_htab_has) (by rfl)
  simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Has.body, Has.formals, Find.formals,
    Guest.guestFn_htab_has, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using checked

/-- Actual warmth query, including the real parent-frame table read and all
collision probes. Current physical ownership is explicit; no warmth answer,
callee execution or initial clock allowance is assumed. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame query : BitVec 64)
    (plan : Plan) (slots : List Nat) (cursor floor : Nat) (table : TableState source .account plan slots cursor floor)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (tableMapped : source.memaddrs (frame + 168#64))
    (tableCell : source.memory (frame + 168#64) = .word (cell plan .header 0))
    (queryLocal : source.locals.lookup (ofString "addr") = some (.val (.word query)))
    (queryFits : query.toNat + 20 < 2^64)
    (queryMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress query offset)))
    (returned : ValueHOL 64) (run : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    ∃ paid answer, paid ≤ Has.bodyPrice .account slots.length + 1 ∧ paid ≤ source.clock ∧
      (answer = 0#64 ∨ answer = 1#64) ∧ returned = .val (.word answer) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with clock := source.clock - paid} := by
  have tableRead := frame_read source frame 168#64 (cell plan .header 0) ev tableMapped tableCell
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      [frameLoad 168#64, localVar "addr"] = some [.val (.word (cell plan .header 0)), .val (.word query)] := by
    simp only [eval] at tableRead
    simp [evalListHOLFinite, evalListHOLExact, tableRead, evalHOLExact, toExact, localVar, queryLocal]
  rw [body_shape] at run
  obtain ⟨paid, answer, inner, positive, bounded, funded, binary, tailRun, scope⟩ :=
    Has.model_normal_entry source post .account plan slots cursor floor table environment query queryFits queryMapped
      (has_code source.code installed) "h" [frameLoad 168#64, localVar "addr"] afterHas args returned run
  let ready := bind {source with clock := source.clock - paid} "h" answer
  obtain ⟨actualRead, postEq⟩ := Input.return_normal ready inner (localVar "h") returned tailRun
  have answerCell : ready.locals.lookup (ofString "h") = some (.val (.word answer)) := bind_lookup_same _ _ _
  have read : eval ready (localVar "h") = some (.val (.word answer)) := by simp [eval, localVar, evalHOLExact, toExact, answerCell]
  refine ⟨paid, answer, bounded, funded, binary, Option.some.inj (actualRead.symm.trans read), ?_⟩
  rw [scope, postEq]
  rfl

end InitECandidate.Solver.GasBudget.WarmAddress

#print axioms InitECandidate.Solver.GasBudget.WarmAddress.original_code
#print axioms InitECandidate.Solver.GasBudget.WarmAddress.has_code
#print axioms InitECandidate.Solver.GasBudget.WarmAddress.body_normal
