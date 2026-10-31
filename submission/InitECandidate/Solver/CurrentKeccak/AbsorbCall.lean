import InitECandidate.Solver.CurrentKeccak.AbsorbMemory
import InitECandidate.Solver.WitnessRadix.CodeEnvironment

namespace InitECandidate.Solver.CurrentKeccak.Absorb
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix
open Flapjack.Basis.Pure.MlString

def values (stp blk : BitVec 64) : List (ValueHOL 64) := [.val (.word stp),.val (.word blk)]
def rawLocals (stp blk : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "blk" then some (.val (.word blk))
  else if name = ofString "stp" then some (.val (.word stp)) else none

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (stp blk : BitVec 64)
    (code : codeFn (ofString "keccak_absorb_block") = some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "keccak_absorb_block") (values stp blk) = some (body,callee,.one) ∧
      callee.lookup (ofString "stp") = some (.val (.word stp)) ∧
      callee.lookup (ofString "blk") = some (.val (.word blk)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values stp blk).length ∧
      ((formals.zip (values stp blk)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact codeFn (ofString "keccak_absorb_block") (values stp blk) = some (body,rawLocals stp blk,.one) := by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  obtain ⟨callee,lookup,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,lookup,?_,?_⟩
  all_goals rw [locals]; simp [rawLocals,ofString]

/-- Ordinary actual block absorption protects every word outside its
25-lane state region, with real callee arguments and checked body return. -/
theorem call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp blk query : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values stp blk))
    (away : ∀ offset : Nat,offset<200 → offset%8=0 → query≠stp+BitVec.ofNat 64 offset)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak_absorb_block") arguments)=(none,post)) :
    post.memory query=source.memory query := by
  obtain ⟨callee,called,stpCell,blockCell⟩:=environment source.code.lookup stp blk (original_code source.code installed)
  apply Input.MemoryAt.call_normal source post _ arguments (values stp blk) body callee .one query args called ?_ run
  intro target value bodyRun
  exact body_memory (callEntryStateHOLFinite source callee) target stp blk query installed stpCell blockCell away value bodyRun

/-- A real returning absorb call derives the input pointer's domain bound
from that same callee execution, rather than a future-success assumption. -/
theorem call_input_upper (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp blk : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values stp blk))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak_absorb_block") arguments)=(none,post)) :
    blk.toNat<Input.CopyAny.ordinaryEnd := by
  obtain ⟨callee,called,stpCell,blockCell⟩:=environment source.code.lookup stp blk (original_code source.code installed)
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ :=
    Input.CallNormal.ignored_data source post _ arguments run
  have valuesEq : actualValues=values stp blk := Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq : (actualBody,actualCallee,actualShape)=(body,callee,.one) :=
    Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  exact body_input_upper (callEntryStateHOLFinite source callee) target stp blk stpCell blockCell domain returned bodyRun

end InitECandidate.Solver.CurrentKeccak.Absorb

#print axioms InitECandidate.Solver.CurrentKeccak.Absorb.environment
#print axioms InitECandidate.Solver.CurrentKeccak.Absorb.call_memory

#print axioms InitECandidate.Solver.CurrentKeccak.Absorb.call_input_upper
