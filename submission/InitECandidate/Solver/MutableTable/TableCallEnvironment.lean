import InitECandidate.Solver.MutableTable.MemoryValueCall

namespace InitECandidate.Solver.MutableTable.TableCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def formals : List (MlS×ShapeHOL):=[(ofString "t",.one),(ofString "key",.one),(ofString "value",.one)]
def values (table key value : BitVec 64) : List (ValueHOL 64):=[.val (.word table),.val (.word key),.val (.word value)]
def rawLocals (table key value : BitVec 64) (name : MlS) : Option (ValueHOL 64):=
  if name=ofString "value" then some (.val (.word value))
  else if name=ofString "key" then some (.val (.word key))
  else if name=ofString "t" then some (.val (.word table)) else none

theorem raw_lookup (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL))
    (function : MlS) (body : ProgHOL 64) (table key value : BitVec 64)
    (code : codeFn function=some (formals,body,.one)) :
    lookupCodeHOLExact codeFn function (values table key value)=some (body,rawLocals table key value,.one) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values table key value).length ∧
      ((formals.zip (values table key value)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
    decide
  simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
  rfl

/-- The actual three-word table-mutator ABI supplies a finite callee local
environment. This is shared by raw insertion and the ordinary setter. -/
theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL))
    (function : MlS) (body : ProgHOL 64) (table key value : BitVec 64)
    (code : codeFn function=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn function (values table key value)=some (body,callee,.one) ∧
      callee.lookup (ofString "t")=some (.val (.word table)) ∧
      callee.lookup (ofString "key")=some (.val (.word key)) ∧
      callee.lookup (ofString "value")=some (.val (.word value)) := by
  have raw:=raw_lookup codeFn function body table key value code
  cases lookup : lookupCodeHOLFinite codeFn function (values table key value) with
  | none=>
    have absent:=(lookupCodeHOLFinite_eq_none_iff codeFn _ _).mp lookup
    rw [raw] at absent
    cases absent
  | some data=>
    obtain ⟨body',callee,shape⟩:=data
    have equal:=lookupCodeHOLFinite_eq_some codeFn _ _ body' callee shape lookup
    rw [raw] at equal
    simp only [Option.some.injEq,Prod.mk.injEq] at equal
    obtain ⟨rfl,localsEq,rfl⟩:=equal
    refine ⟨callee,rfl,?_,?_,?_⟩
    all_goals rw [← localsEq]
    · simp [rawLocals,show ofString "t"≠ofString "value" by decide,show ofString "t"≠ofString "key" by decide]
    · simp [rawLocals,show ofString "key"≠ofString "value" by decide]
    · simp [rawLocals]

end InitECandidate.Solver.MutableTable.TableCall

#print axioms InitECandidate.Solver.MutableTable.TableCall.environment
