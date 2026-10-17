import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

/-! Generic Pancake state helpers. Historical namespaces are retained to keep
original-program proofs stable; this module imports no replacement program. -/
namespace InitECandidate.Solver.WitnessRadix.QueryBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def localVar (name : String) : ExpHOL 64 := .var .local (ofString name)
def addConst (expression : ExpHOL 64) (offset : BitVec 64) : ExpHOL 64 :=
  .op .add [expression, .const offset]
noncomputable def eval {F : Type} (state : PanSemStateFiniteExact 64 F)
    (expression : ExpHOL 64) : Option (ValueHOL 64) :=
  @evalHOLExact 64 F _ state.toExact
    (fun address => Classical.propDecidable (state.memaddrs address)) expression

def bind {F : Type} (state : PanSemStateFiniteExact 64 F) (name : String)
    (word : BitVec 64) : PanSemStateFiniteExact 64 F :=
  setVarHOLFinite (ofString name) (.val (.word word)) state

def restore {F : Type} (saved : PanSemStateFiniteExact 64 F) (name : String)
    (state : PanSemStateFiniteExact 64 F) : PanSemStateFiniteExact 64 F :=
  { state with locals := HolFiniteMapExact.resVarEq state.locals (ofString name, saved.locals.lookup (ofString name)) }

end InitECandidate.Solver.WitnessRadix.QueryBranch
