import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
variable {F : Type}

/-- Actual six scalar caller operands, independent of graph validity or
success of any later comparison, allocation or mutation. -/
structure ScalarInputs (source : PanSemStateFiniteExact 64 F) (node key level length pointer size : BitVec 64) : Prop where
  nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))
  keyCell : source.locals.lookup (ofString "key")=some (.val (.word key))
  levelCell : source.locals.lookup (ofString "level")=some (.val (.word level))
  lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length))
  pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer))
  sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size))

theorem ScalarInputs.after_update (source target : PanSemStateFiniteExact 64 F)
    (node key level length pointer size : BitVec 64) (name : MlS) (value : ValueHOL 64) (inputs : ScalarInputs source node key level length pointer size)
    (notNode : ofString "node"≠name) (notKey : ofString "key"≠name) (notLevel : ofString "level"≠name)
    (notLength : ofString "klen"≠name) (notPointer : ofString "vptr"≠name) (notSize : ofString "vlen"≠name)
    (localsEq : target.locals=source.locals.update (name,value)) : ScalarInputs target node key level length pointer size := by
  have current (query : MlS) (other : query≠name) : target.locals.lookup query=source.locals.lookup query:=by
    rw [localsEq]
    simp [HolFiniteMapExact.update,FUPDATE,Ne.symm other]
  exact ⟨(current _ notNode).trans inputs.nodeCell,(current _ notKey).trans inputs.keyCell,(current _ notLevel).trans inputs.levelCell,
    (current _ notLength).trans inputs.lengthCell,(current _ notPointer).trans inputs.pointerCell,(current _ notSize).trans inputs.sizeCell⟩

theorem ScalarInputs.after_prefix (source target : PanSemStateFiniteExact 64 F)
    (node key level length pointer size : BitVec 64) (program : ProgHOL 64) (inputs : ScalarInputs source node key level length pointer size)
    (safe : ∀ name : MlS,Input.LocalPrefix name program) (normal : evaluateHOLFiniteState source program=(none,target)) :
    ScalarInputs target node key level length pointer size := by
  have current (name : MlS) : target.locals.lookup name=source.locals.lookup name:=by
    have summary:=(safe name).summary source
    rw [normal] at summary
    exact summary.1 rfl
  exact ⟨(current _).trans inputs.nodeCell,(current _).trans inputs.keyCell,(current _).trans inputs.levelCell,
    (current _).trans inputs.lengthCell,(current _).trans inputs.pointerCell,(current _).trans inputs.sizeCell⟩

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.ScalarInputs.after_update
#print axioms InitECandidate.Solver.Mpt.Insert.ScalarInputs.after_prefix
