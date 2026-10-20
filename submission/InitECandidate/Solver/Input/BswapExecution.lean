import InitECandidate.Solver.GasBudget.QuadWriterAssignments
import InitECandidate.Solver.Input.PureReturn

namespace InitECandidate.Solver.Input.BswapExecution
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def stage (value mask : BitVec 64) (bits : Nat) := ((value &&& mask) <<< bits) ||| ((value >>> bits) &&& mask)
def expression (mask : BitVec 64) (bits : Nat) : ExpHOL 64 := .op .or
  [.shift .lsl (.op .and [localVar "x",.const mask]) (.const (BitVec.ofNat 64 bits)),
   .op .and [.shift .lsr (localVar "x") (.const (BitVec.ofNat 64 bits)),.const mask]]
def lastExpression : ExpHOL 64 := .op .or [.shift .lsl (localVar "x") (.const 32#64),.shift .lsr (localVar "x") (.const 32#64)]
def result (value : BitVec 64) :=
  let first := stage value 71777214294589695#64 8
  let second := stage first 281470681808895#64 16
  (second <<< 32) ||| (second >>> 32)
def body := GasBudget.ArithmeticEffects.Kind.bswap64.body

theorem body_shape : body = .seq (.assign .local (ofString "x") (expression 71777214294589695#64 8))
    (.seq (.assign .local (ofString "x") (expression 281470681808895#64 16)) (.return lastExpression)) := by
  simp only [body,GasBudget.ArithmeticEffects.Kind.body,GasBudget.ArithmeticEffects.Kind.signature,GasBudget.ArithmeticEffects.Kind.original,
    Guest.guestFn_bswap64,progToHOL,expToHOL,List.map_cons,List.map_nil,expression,lastExpression,localVar]

theorem expression_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value mask : BitVec 64) (bits : Nat) (small : bits < 64)
    (binding : source.locals.lookup (ofString "x") = some (.val (.word value))) :
    QueryBranch.eval source (expression mask bits) = some (.val (.word (stage value mask bits))) := by
  have number : (BitVec.ofNat 64 bits).toNat = bits := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have masked : mask &&& (18446744073709551615#64 : BitVec 64) = mask := by
    change mask &&& BitVec.allOnes 64 = mask
    exact BitVec.and_allOnes
  simp [QueryBranch.eval,expression,localVar,evalHOLExact,evalListHOLExact,toExact,binding,valueIsWord,valueWord,wordOpHOL,wordOp,wordShiftHOL,number,small,stage,AndOp.and,OrOp.or,masked,show ¬ 64 ≤ bits by omega,show (18446744073709551615#64 : BitVec 64) = BitVec.allOnes 64 from rfl]

private theorem bind_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (word : BitVec 64) :
    (QueryBranch.bind source name word).clock = source.clock := rfl

private theorem assigned_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first second : BitVec 64) :
    emptyLocalsHOLFinite (emptyLocalsHOLFinite (QueryBranch.bind (QueryBranch.bind source "x" first) "x" second)) = emptyLocalsHOLFinite source := rfl

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64)
    (binding : source.locals.lookup (ofString "x") = some (.val (.word value))) :
    ∃ target,evaluateHOLFiniteState source body = (some (.returned (.val (.word (result value)))),target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite source := by
  let first := QueryBranch.bind source "x" (stage value 71777214294589695#64 8)
  have firstRun := StateSteps.assign_execute source "x" _ value _ binding (expression_read source value 71777214294589695#64 8 (by decide) binding)
  have firstClock : first.clock = source.clock := bind_clock source "x" (stage value 71777214294589695#64 8)
  have firstBinding : first.locals.lookup (ofString "x") = some (.val (.word (stage value 71777214294589695#64 8))) := by simp [first,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  let second := QueryBranch.bind first "x" (stage (stage value 71777214294589695#64 8) 281470681808895#64 16)
  have secondRun := StateSteps.assign_execute first "x" _ _ _ firstBinding (expression_read first _ 281470681808895#64 16 (by decide) firstBinding)
  have secondClock : second.clock = first.clock := bind_clock first "x" (stage (stage value 71777214294589695#64 8) 281470681808895#64 16)
  have secondBinding : second.locals.lookup (ofString "x") = some (.val (.word (stage (stage value 71777214294589695#64 8) 281470681808895#64 16))) := by simp [second,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have lastRead : QueryBranch.eval second lastExpression = some (.val (.word (result value))) := by
    simp [QueryBranch.eval,lastExpression,localVar,evalHOLExact,evalListHOLExact,toExact,secondBinding,valueIsWord,valueWord,wordOpHOL,wordOp,wordShiftHOL,result,AndOp.and,OrOp.or]
  refine ⟨emptyLocalsHOLFinite second,?_,assigned_frame source (stage value 71777214294589695#64 8) (stage (stage value 71777214294589695#64 8) 281470681808895#64 16)⟩
  rw [body_shape,StateSteps.next_sequence source first _ _ firstRun (Nat.le_of_eq firstClock),StateSteps.next_sequence first second _ _ secondRun (Nat.le_of_eq secondClock)]
  simp only [QueryBranch.eval] at lastRead
  rw [evaluateHOLFiniteState_return,lastRead]
  simp [shapeOfHOLExact,sizeOfShapeWithContextHOL]

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : BitVec 64) (name : String) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments = some [.val (.word value)])
    (installed : OriginalCode.Installed source.code) (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "bswap64") arguments tail) =
      (let output := evaluateHOLFiniteState (QueryBranch.bind {source with clock := source.clock - 1} name (result value)) tail
       (output.1,restore source name output.2)) := by
  obtain ⟨callee,called,binding⟩ := CallNormal.unary_environment source.code.lookup (ofString "bswap64") "x" body value (GasBudget.QuadWriter.bswap_code source.code installed)
  obtain ⟨target,run,frame⟩ := execute (callEntryStateHOLFinite source callee) value binding
  have actual := CallNormal.pure_return_execute source target name (ofString "bswap64") arguments [.val (.word value)] body tail callee (result value) 0 args called enough run frame
  simpa only [Nat.sub_zero] using actual

end InitECandidate.Solver.Input.BswapExecution

#print axioms InitECandidate.Solver.Input.BswapExecution.body_shape
#print axioms InitECandidate.Solver.Input.BswapExecution.expression_read
#print axioms InitECandidate.Solver.Input.BswapExecution.execute
#print axioms InitECandidate.Solver.Input.BswapExecution.call_execute
