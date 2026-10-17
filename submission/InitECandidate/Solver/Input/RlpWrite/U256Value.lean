import InitECandidate.Solver.Input.RlpWrite.BitLengthBuilt

namespace InitECandidate.Solver.Input.RlpWrite.U256Value
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

abbrev Words := Fin 4→BitVec 64
def tuple (words : Words) : ValueHOL 64 := .rStruct
  [.val (.word (words 0)),.val (.word (words 1)),.val (.word (words 2)),.val (.word (words 3))]
def tupleShape : ShapeHOL := .comb [.one,.one,.one,.one]
def limb (index : Fin 4) : ExpHOL 64 := .rfield index.val (localVar "a")

theorem limb_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : Words) (index : Fin 4)
    (a : source.locals.lookup (ofString "a")=some (tuple words)) :
    eval source (limb index)=some (.val (.word (words index))) := by
  obtain ⟨index,inside⟩:=index
  have cases : index=0 ∨ index=1 ∨ index=2 ∨ index=3 := by omega
  rcases cases with rfl|rfl|rfl|rfl <;>
    simp [eval,limb,localVar,evalHOLExact,toExact,a,tuple]

def rawLocals (words : Words) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "a" then some (tuple words) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (fn : MlS) (body : ProgHOL 64) (words : Words)
    (lookup : codeFn fn=some ([(ofString "a",tupleShape)],body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn fn [tuple words]=some (body,callee,.one) ∧
      callee.lookup (ofString "a")=some (tuple words) := by
  have valid : (([(ofString "a",tupleShape)] : List (MlS×ShapeHOL)).map Prod.fst).Nodup ∧
      ([(ofString "a",tupleShape)] : List (MlS×ShapeHOL)).length=([tuple words] : List (ValueHOL 64)).length ∧
      ((([(ofString "a",tupleShape)] : List (MlS×ShapeHOL)).zip [tuple words]).all
        (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    simp [tupleShape,tuple,shapeOfHOLExact,shapeEqHOL_eq_true]
  have raw : lookupCodeHOLExact codeFn fn [tuple words]=some (body,rawLocals words,.one) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_⟩
  rw [locals]
  simp [rawLocals]

end InitECandidate.Solver.Input.RlpWrite.U256Value

#print axioms InitECandidate.Solver.Input.RlpWrite.U256Value.limb_read
#print axioms InitECandidate.Solver.Input.RlpWrite.U256Value.environment
