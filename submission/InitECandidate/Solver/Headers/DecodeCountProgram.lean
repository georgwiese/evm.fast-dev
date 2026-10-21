import InitECandidate.Solver.Headers.DecodeProgram
import InitECandidate.Solver.PanDeclarations

namespace InitECandidate.Solver.Headers.Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def localDeclarations : List (String×ExpHOL 64) :=
  [("arr",.rfield 0 (localVar "lst")),("n",.rfield 1 (localVar "lst")),("is_current",.const 0#64)]
def afterCurrent : ProgHOL 64 := match afterList with | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ rest))=>rest | _=>.skip
def afterCount : ProgHOL 64 := match afterCurrent with | .seq _ rest=>rest | _=>.skip
def afterAllocation : ProgHOL 64 := match afterCount with | .decCall _ _ _ _ rest=>rest | _=>.skip
def countGuard : ProgHOL 64 := .ite (.cmp .equal (localVar "n") (.const 23#64))
  (.assign .local (ofString "is_current") (.const 1#64))
  (.ite (.cmp .notEqual (localVar "n") (.const 21#64)) (.raise (ofString "HdrErr") (.const 11#64)) .skip)

theorem list_scope_shape : afterList=WitnessRadix.BuildEntry.declarations localDeclarations afterCurrent := by
  simp only [afterList,afterKind,afterTop,body,afterCurrent,localDeclarations,WitnessRadix.BuildEntry.declarations,
    localVar,Guest.guestFn_decode_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
theorem current_shape : afterCurrent=.seq countGuard afterCount := by
  simp only [afterCurrent,afterCount,afterList,afterKind,afterTop,body,countGuard,
    localVar,Guest.guestFn_decode_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
theorem allocation_shape : afterCount=.decCall (ofString "h") .one (ofString "alloc") [.const 248#64] afterAllocation := by
  simp only [afterCount,afterAllocation,afterCurrent,afterList,afterKind,afterTop,body,
    Guest.guestFn_decode_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]

/-- The literal21/23 count check performs only local/read-only work. -/
theorem count_guard_quiet (code) : Input.QuietClock.Preserves code countGuard :=
  Input.QuietClock.conditional code _ _ _ (Input.QuietClock.assign code _ _)
    (Input.QuietClock.conditional code _ _ _ (Input.QuietClock.raised code _ _) (Input.QuietClock.skip code))

theorem count_guard_readonly (code) : Input.LocalEffects.Preserves code countGuard :=
  Input.LocalEffects.conditional code _ _ _ (Input.LocalEffects.assign code _ _)
    (Input.LocalEffects.conditional code _ _ _ (Input.LocalEffects.raised code _ _) (Input.LocalEffects.skip code))

end InitECandidate.Solver.Headers.Decode

#print axioms InitECandidate.Solver.Headers.Decode.list_scope_shape
#print axioms InitECandidate.Solver.Headers.Decode.current_shape
#print axioms InitECandidate.Solver.Headers.Decode.allocation_shape
#print axioms InitECandidate.Solver.Headers.Decode.count_guard_quiet
#print axioms InitECandidate.Solver.Headers.Decode.count_guard_readonly
