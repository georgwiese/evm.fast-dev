import InitECandidate.Solver.Input.UDivMod.Step

namespace InitECandidate.Solver.Input.UDivMod
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem step_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b q r : BitVec 64) (index : Nat)
    (qLocal : source.locals.lookup (ofString "q")=some (.val (.word q))) :
    (step source a b q r index).locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (index-1)))) ∧
    (step source a b q r index).locals.lookup (ofString "q")=some (.val (.word (nextQ a b q r index))) ∧
    (step source a b q r index).locals.lookup (ofString "r")=some (.val (.word (nextR a b r index))) := by
  classical
  by_cases take : takeSubtract a b r index <;>
    simp [step,nextQ,nextR,take,WitnessRadix.QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,qLocal,show ofString "q"≠ofString "i" from by decide,show ofString "r"≠ofString "i" from by decide,show ofString "q"≠ofString "r" from by decide,show ofString "r"≠ofString "q" from by decide,show ofString "i"≠ofString "q" from by decide]

theorem step_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b q r : BitVec 64) (index : Nat) (name : MlS)
    (notI : name≠ofString "i") (notQ : name≠ofString "q") (notR : name≠ofString "r") :
    (step source a b q r index).locals.lookup name=source.locals.lookup name := by
  classical
  by_cases take : takeSubtract a b r index <;>
    simp [step,take,WitnessRadix.QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm notI,Ne.symm notQ,Ne.symm notR]

theorem step_state (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b q r : BitVec 64) (index : Nat) :
    step source a b q r index={source with locals:=(step source a b q r index).locals} := by
  by_cases take : takeSubtract a b r index
  · simp only [step,if_pos take]; rfl
  · simp only [step,if_neg take]; rfl

end InitECandidate.Solver.Input.UDivMod

#print axioms InitECandidate.Solver.Input.UDivMod.step_fields
#print axioms InitECandidate.Solver.Input.UDivMod.step_other
#print axioms InitECandidate.Solver.Input.UDivMod.step_state
