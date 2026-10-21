import InitECandidate.Solver.Mpt.WitnessResolveLookupNormal
import InitECandidate.Solver.Mpt.FailGuardReturn

namespace InitECandidate.Solver.Mpt.WitnessResolve
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem lookup_never : Input.NoFallthrough lookupCall :=
  Input.NoFallthrough.scoped _ _ _ _ _ (Input.NoFallthrough.sequence _ _ (Input.NoFallthrough.returned _))
theorem string_never : Input.NoFallthrough stringBranch :=
  Input.NoFallthrough.sequence _ _ (Input.NoFallthrough.sequence _ _ lookup_never)

theorem suffix_choice (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer header payload flag : BitVec 64)
    (itemCell : source.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag)) :
    evaluateHOLFiniteState source (WitnessStep.afterRlp .resolve)=
      if flag=0#64 then evaluateHOLFiniteState source stringBranch else evaluateHOLFiniteState source listReturn := by
  have selected : evaluateHOLFiniteState source (.ite stringTest stringBranch .skip)=
      if flag=0#64 then evaluateHOLFiniteState source stringBranch else (none,source):=by
    by_cases zero : flag=0#64 <;>
      simp [stringTest,evaluateHOLFiniteState_ite,field,evalHOLExact,localVar,toExact,itemCell,Rlp.Item.result,zero,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
  rw [suffix_shape]
  exact Input.sequence_choice source _ stringBranch listReturn (flag=0#64) selected string_never

theorem string_choice (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer header payload flag : BitVec 64)
    (itemCell : source.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag)) :
    evaluateHOLFiniteState source stringBranch=
      if payload=0#64 then evaluateHOLFiniteState source emptyReturn else evaluateHOLFiniteState source afterEmpty := by
  have selected : evaluateHOLFiniteState source (.ite emptyTest emptyReturn .skip)=
      if payload=0#64 then evaluateHOLFiniteState source emptyReturn else (none,source):=by
    by_cases zero : payload=0#64 <;>
      simp [emptyTest,evaluateHOLFiniteState_ite,field,evalHOLExact,localVar,toExact,itemCell,Rlp.Item.result,zero,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
  exact Input.sequence_choice source _ emptyReturn afterEmpty (payload=0#64) selected (Input.NoFallthrough.returned _)

/-- Any genuine nonempty string return passes the real32-byte guard,
and then returns through the original database lookup call. -/
theorem nonempty_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer header payload flag : BitVec 64)
    (itemCell : source.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterEmpty=(some (.returned value),post)) :
    payload=32#64 ∧ evaluateHOLFiniteState source lookupCall=(some (.returned value),post) := by
  obtain ⟨guardRun,continued⟩:=Fail.guard_return source post sizeTest [.const 10#64] lookupCall value installed normal
  have passed:=(Fail.guard_normal source source sizeTest [.const 10#64] installed guardRun).1
  have thirtyTwo : payload=32#64:=by
    by_contra other
    have one : eval source sizeTest=some (.val (.word 1#64)):=by
      simp [eval,sizeTest,field,evalHOLExact,localVar,toExact,itemCell,Rlp.Item.result,other,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have impossible : (1#64 : BitVec 64)=0#64:=by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using one.symm.trans passed
    exact (by decide : (1#64 : BitVec 64)≠0#64) impossible
  exact ⟨thirtyTwo,continued⟩

end InitECandidate.Solver.Mpt.WitnessResolve

#print axioms InitECandidate.Solver.Mpt.WitnessResolve.lookup_never
#print axioms InitECandidate.Solver.Mpt.WitnessResolve.string_never
#print axioms InitECandidate.Solver.Mpt.WitnessResolve.suffix_choice
#print axioms InitECandidate.Solver.Mpt.WitnessResolve.string_choice
#print axioms InitECandidate.Solver.Mpt.WitnessResolve.nonempty_normal
