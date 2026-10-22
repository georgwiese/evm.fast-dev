import InitECandidate.Solver.Input.ClockCostScopeLocals

namespace InitECandidate.Solver.Input.CallPrefix
open Flapjack Flapjack.Pancake.PanLang

/-- Original straight-line lexical context, retaining every declaration,
scoped call and command before one selected helper call. -/
inductive Action where
  | declare (name : MlS) (shape : ShapeHOL) (expression : ExpHOL 64)
  | scoped (name : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64))
  | command (program : ProgHOL 64)

def program : List Action→ProgHOL 64→ProgHOL 64
  | [],tail=>tail
  | .declare name shape expression::rest,tail=>.dec name shape expression (program rest tail)
  | .scoped name shape function arguments::rest,tail=>.decCall name shape function arguments (program rest tail)
  | .command command::rest,tail=>.seq command (program rest tail)

def cut (target : MlS) : ProgHOL 64→List Action×ProgHOL 64
  | .dec name shape expression rest=>
    let next:=cut target rest
    (.declare name shape expression::next.1,next.2)
  | .decCall name shape function arguments rest=>
    if function=target then ([],.decCall name shape function arguments rest) else
    let next:=cut target rest
    (.scoped name shape function arguments::next.1,next.2)
  | .seq command rest=>
    let next:=cut target rest
    (.command command::next.1,next.2)
  | other=>([],other)

/-- Cutting and rebuilding is literal syntax equality. It does not replace
guest code, omit an executed command or assume the selected call succeeds. -/
theorem reconstruct (target : MlS) (source : ProgHOL 64) :
    program (cut target source).1 (cut target source).2=source := by
  cases source with
  | dec name shape expression rest=>
    exact congrArg (ProgHOL.dec name shape expression) (reconstruct target rest)
  | decCall name shape function arguments rest=>
    by_cases same : function=target
    · simp only [cut,if_pos same,program]
    · simpa only [cut,if_neg same,program] using congrArg (ProgHOL.decCall name shape function arguments) (reconstruct target rest)
  | seq command rest=>
    exact congrArg (ProgHOL.seq command) (reconstruct target rest)
  | _=>rfl
termination_by source

end InitECandidate.Solver.Input.CallPrefix

#print axioms InitECandidate.Solver.Input.CallPrefix.reconstruct
