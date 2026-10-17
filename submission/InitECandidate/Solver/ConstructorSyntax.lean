import InitECandidate.Solver.PanState

/-! Common syntax of the unchanged witness constructor. -/
namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString QueryBranch

def scaled (name : String) (stride : BitVec 64) : ExpHOL 64 :=
  .op .add [localVar name, .panop .mul [localVar "i", .const stride]]
def scratch : ExpHOL 64 := .var .global (ofString "mpt_hash_scratch")
def hashArguments : List (ExpHOL 64) :=
  [.load .one (scaled "slice_arr" 16#64),
   .load .one (.op .add [localVar "slice_arr", .panop .mul [localVar "i", .const 16#64], .const 8#64]), scratch]
def condition : ExpHOL 64 := .cmp .lower (localVar "i") (localVar "n")
def capacityLoop : ProgHOL 64 :=
  .while (.cmp .lower (localVar "cap")
    (.op .add [.panop .mul [.const 2#64, localVar "n"], .const 2#64]))
    (.assign .local (ofString "cap") (.panop .mul [localVar "cap", .const 2#64]))

end InitECandidate.Solver.WitnessRadix.Constructor
