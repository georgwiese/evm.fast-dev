import InitECandidate.Solver.Input.FqNegProgram
import InitECandidate.Solver.Input.PureValueReturn

namespace InitECandidate.Solver.Input.FqNeg
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
set_option maxRecDepth 100000

private theorem subtract_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a : Words)
    (aLocal : source.locals.lookup (ofString "a") = some (RlpWrite.U256Value.tuple a))
    (installed : OriginalCode.Installed source.code) (enough : 1 ≤ source.clock) :
    ∃ target,evaluateHOLFiniteState source subtraction = (some (.returned (RlpWrite.U256Value.tuple (GasBudget.U256Sub.result Main.BnAccelInitialization.modulus a))),target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - 1} := by
  obtain ⟨callee,called,aRead,bRead⟩ := GasBudget.U256Sub.environment source.code.lookup Main.BnAccelInitialization.modulus a (GasBudget.U256Sub.original_code source.code installed)
  let inner := callEntryStateHOLFinite source callee
  obtain ⟨target,run,frame⟩ := GasBudget.U256Sub.execute inner Main.BnAccelInitialization.modulus a aRead bRead
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query))
      [modulusExpression,.var .local (ofString "a")] = some [RlpWrite.U256Value.tuple Main.BnAccelInitialization.modulus,RlpWrite.U256Value.tuple a] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,modulusExpression,aLocal,RlpWrite.U256Value.tuple,Main.BnAccelInitialization.modulus]
  have actual := evaluateHOLFiniteState_call_return_none source (RlpWrite.U256Value.tuple (GasBudget.U256Sub.result Main.BnAccelInitialization.modulus a))
    (ofString "u256_sub") _ _ GasBudget.U256Sub.body callee RlpWrite.U256Value.tupleShape target args called (by omega) run
    (by simp [RlpWrite.U256Value.tuple,RlpWrite.U256Value.tupleShape,shapeOfHOLExact,shapeEqHOL_eq_true])
  exact ⟨emptyLocalsHOLFinite target,actual,frame⟩

/-- Both real fq_neg branches execute. The zero branch spends one body tick;
the nonzero branch spends two and uses the original four-limb subtraction. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a : Words)
    (aLocal : source.locals.lookup (ofString "a") = some (RlpWrite.U256Value.tuple a))
    (installed : OriginalCode.Installed source.code) (enough : 2 ≤ source.clock) :
    ∃ target answer paid,evaluateHOLFiniteState source body = (some (.returned (RlpWrite.U256Value.tuple answer)),target) ∧
      paid ≤ 2 ∧ emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - paid} := by
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query))
      [.var .local (ofString "a")] = some [RlpWrite.U256Value.tuple a] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,aLocal]
  have called := GasBudget.U256Zero.call_execute source a "z" [.var .local (ofString "a")] afterZero args
    (zero_original_code source.code installed) (by omega)
  let ready := bind {source with clock := source.clock - 1} "z" (GasBudget.U256Zero.resultWord a)
  have zRead : ready.locals.lookup (ofString "z") = some (.val (.word (GasBudget.U256Zero.resultWord a))) := by
    simp [ready,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have aRead : ready.locals.lookup (ofString "a") = some (RlpWrite.U256Value.tuple a) := by
    simpa [ready,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using aLocal
  by_cases zero : GasBudget.U256Zero.mixed a = 0#64
  · have guarded : evaluateHOLFiniteState ready guard =
        (some (.returned (RlpWrite.U256Value.tuple Main.BnAccelInitialization.zeros)),emptyLocalsHOLFinite ready) := by
      simp [guard,zeroReturn,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,zRead,
        GasBudget.U256Zero.resultWord,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,RlpWrite.U256Value.tuple,
        Main.BnAccelInitialization.zeros,shapeOfHOLExact,sizeOfShapeWithContextHOL,sizeOfShapesWithContextHOL]
    have tail : evaluateHOLFiniteState ready afterZero =
        (some (.returned (RlpWrite.U256Value.tuple Main.BnAccelInitialization.zeros)),emptyLocalsHOLFinite ready) := by
      rw [afterZero,evaluateHOLFiniteState_seq_line780,guarded]
    refine ⟨restore source "z" (emptyLocalsHOLFinite ready),Main.BnAccelInitialization.zeros,1,?_,by omega,rfl⟩
    rw [body_shape,called]
    change (let output := evaluateHOLFiniteState ready afterZero; (output.1,restore source "z" output.2)) = _
    rw [tail]
  · have guarded : evaluateHOLFiniteState ready guard = (none,ready) := by
      simp [guard,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,toExact,zRead,
        GasBudget.U256Zero.resultWord,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    obtain ⟨target,tailRun,frame⟩ := subtract_execute ready a aRead installed (by change 1 ≤ source.clock - 1; omega)
    have tail : evaluateHOLFiniteState ready afterZero =
        (some (.returned (RlpWrite.U256Value.tuple (GasBudget.U256Sub.result Main.BnAccelInitialization.modulus a))),target) := by
      rw [afterZero,StateSteps.next_sequence ready ready guard subtraction guarded (Nat.le_refl _)]
      exact tailRun
    refine ⟨restore source "z" target,GasBudget.U256Sub.result Main.BnAccelInitialization.modulus a,2,?_,by omega,?_⟩
    · rw [body_shape,called]
      change (let output := evaluateHOLFiniteState ready afterZero; (output.1,restore source "z" output.2)) = _
      rw [tail]
    · change emptyLocalsHOLFinite target = _
      rw [frame]
      have clock : source.clock - 1 - 1 = source.clock - 2 := by omega
      change emptyLocalsHOLFinite {source with clock := source.clock - 1 - 1} = _
      rw [clock]

end InitECandidate.Solver.Input.FqNeg

#print axioms InitECandidate.Solver.Input.FqNeg.execute
