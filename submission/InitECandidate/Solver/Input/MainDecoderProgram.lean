import InitECandidate.Solver.Input.MainInputProgram
import InitECandidate.Solver.WitnessRadix.ProgramPrefix

namespace InitECandidate.Solver.Input.Main.DecoderSetup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def afterOutAllocation : ProgHOL 64 := match afterInput with | .decCall _ _ _ _ rest => rest | _ => .skip
def afterZeroAllocation : ProgHOL 64 := match afterOutAllocation with | .decCall _ _ _ _ rest => rest | _ => .skip
def decoder : ProgHOL 64 := match afterZeroAllocation with | .seq _ (.dec _ _ _ (.dec _ _ _ rest)) => rest | _ => .skip
def zeroCall : ProgHOL 64 := .call (some (none,none)) (ofString "memzero") [.var .local (ofString "z32"),.const 32#64]
def actions : List ProgramPrefix.Action :=
  [.allocate "out" (.const 256#64),.allocate "z32" (.const 32#64),.command zeroCall,.declare "si" (.const 0#64),.declare "err_code" (.const 0#64)]

set_option maxRecDepth 100000 in
theorem original_shape : afterInput = ProgramPrefix.program actions decoder := by
  simp only [afterInput,afterFork,afterEvm,afterHeader,afterBlake,afterRipemd,afterBls,afterBn,afterSecp,afterU256,afterMpt,afterSsz,afterKeccak,afterSha,afterMemory,Main.body,
    actions,ProgramPrefix.program,zeroCall,decoder,afterZeroAllocation,afterOutAllocation,Guest.guestFn_main,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]

end InitECandidate.Solver.Input.Main.DecoderSetup

#print axioms InitECandidate.Solver.Input.Main.DecoderSetup.original_shape
