import InitECandidate.Solver.Input.MainBnSuffix
import InitECandidate.Solver.Input.FqNegCall

namespace InitECandidate.Solver.Input.Main.BnInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
set_option maxRecDepth 100000

def negCall : ProgHOL 64 := .decCall (ofString "b2i") RlpWrite.U256Value.tupleShape (ofString "fq_neg") [.var .local (ofString "b2i0")] b2Stores
def imaginaryCall : ProgHOL 64 := .decCall (ofString "b2i0") RlpWrite.U256Value.tupleShape (ofString "fq_mul")
  [InitializerQuads.expression (quad 3#64 0#64 0#64 0#64),.var .local (ofString "inv82")] negCall
def realCall : ProgHOL 64 := .decCall (ofString "b2r") RlpWrite.U256Value.tupleShape (ofString "fq_mul")
  [InitializerQuads.expression (quad 27#64 0#64 0#64 0#64),.var .local (ofString "inv82")] imaginaryCall

theorem arithmetic_shape : afterB2Allocation = .dec (ofString "inv82") RlpWrite.U256Value.tupleShape (InitializerQuads.expression inverse82) realCall := rfl

private theorem globals_of_control (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (same : KeccakAbsorb.hashControl target = KeccakAbsorb.hashControl source) : target.globals = source.globals := congrArg (fun state => state.globals) same

/-- The two real field multiplications, actual negation, B2 stores and final
44-word exponent table all run. Its only premises describe the current entry. -/
theorem arithmetic_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer b2 : BitVec 64) (cursor : Nat)
    (entry : BnModmul.Environment source pointer) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (b2Binding : source.globals.lookup (ofString "bn_b2") = some (.val (.word b2)))
    (b2Arena : AllocatedBytes.Arena b2 64) (b2Aligned : b2.toNat % 8 = 0)
    (lower : 2701131776 ≤ cursor) (room : cursor + 352 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 10 ≤ source.clock) :
    ∃ target,evaluateHOLFiniteState source afterB2Allocation = (some (.returned (.val (.word 0#64))),target) ∧
      target.clock ≤ source.clock ∧ source.clock - 10 ≤ target.clock ∧
      KeccakAbsorb.hashControl target = KeccakAbsorb.hashControl (InitializerAllocations.template source cursor [exponentAction]) := by
  classical
  let inv := setVarHOLFinite (ofString "inv82") (RlpWrite.U256Value.tuple inverse82) source
  have invEnv : BnModmul.Environment inv pointer := entry.of_control source inv pointer rfl entry.modulus
  have invRead : inv.locals.lookup (ofString "inv82") = some (RlpWrite.U256Value.tuple inverse82) := by
    simp [inv,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have firstArgs : evalListHOLFinite inv (h := fun query => Classical.propDecidable (inv.memaddrs query))
      [InitializerQuads.expression (quad 27#64 0#64 0#64 0#64),.var .local (ofString "inv82")] = some (BnModmul.values (quad 27#64 0#64 0#64 0#64) inverse82) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,InitializerQuads.expression,quad,RlpWrite.U256Value.tuple,invRead,BnModmul.values]
  obtain ⟨firstTarget,real,firstCall,firstClock,firstControl,firstEnv,_⟩ := BnModmul.fq_call_execute inv pointer (quad 27#64 0#64 0#64 0#64) inverse82 "b2r" _ imaginaryCall invEnv firstArgs (by change 3 ≤ source.clock; omega)
  let first := CallNormal.continuationEntry inv firstTarget "b2r" (RlpWrite.U256Value.tuple real)
  have firstEntry : BnModmul.Environment first pointer := firstEnv.of_control firstTarget first pointer rfl firstEnv.modulus
  have firstSame : KeccakAbsorb.hashControl first = KeccakAbsorb.hashControl source := firstControl
  have firstInverse : first.locals.lookup (ofString "inv82") = some (RlpWrite.U256Value.tuple inverse82) := by
    simpa [first,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
      show ofString "b2r" ≠ ofString "inv82" by decide,show ofString "inv82" ≠ ofString "b2r" by decide] using invRead
  have secondArgs : evalListHOLFinite first (h := fun query => Classical.propDecidable (first.memaddrs query))
      [InitializerQuads.expression (quad 3#64 0#64 0#64 0#64),.var .local (ofString "inv82")] = some (BnModmul.values (quad 3#64 0#64 0#64 0#64) inverse82) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,InitializerQuads.expression,quad,RlpWrite.U256Value.tuple,BnModmul.values,firstInverse]
  obtain ⟨secondTarget,imaginary,secondCall,secondClock,secondControl,secondEnv,_⟩ := BnModmul.fq_call_execute first pointer (quad 3#64 0#64 0#64 0#64) inverse82 "b2i0" _ negCall firstEntry secondArgs
    (by change 3 ≤ firstTarget.clock; change firstTarget.clock = source.clock - 3 at firstClock; omega)
  let second := CallNormal.continuationEntry first secondTarget "b2i0" (RlpWrite.U256Value.tuple imaginary)
  have secondEntry : BnModmul.Environment second pointer := secondEnv.of_control secondTarget second pointer rfl secondEnv.modulus
  have secondSame : KeccakAbsorb.hashControl second = KeccakAbsorb.hashControl source := secondControl.trans firstSame
  have negArgs : evalListHOLFinite second (h := fun query => Classical.propDecidable (second.memaddrs query)) [.var .local (ofString "b2i0")] = some [RlpWrite.U256Value.tuple imaginary] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,second,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  obtain ⟨negative,paid,paidBound,negativeCall⟩ := FqNeg.call_execute second imaginary "b2i" _ b2Stores secondEntry.installed negArgs
    (by change 3 ≤ secondTarget.clock; change secondTarget.clock = firstTarget.clock - 3 at secondClock; change firstTarget.clock = source.clock - 3 at firstClock; omega)
  let third := setVarHOLFinite (ofString "b2i") (RlpWrite.U256Value.tuple negative) {second with clock := second.clock - paid}
  have thirdSame : KeccakAbsorb.hashControl third = KeccakAbsorb.hashControl source := secondSame
  have thirdGlobals := globals_of_control source third thirdSame
  have realLocal : third.locals.lookup (ofString "b2r") = some (RlpWrite.U256Value.tuple real) := by
    simp [third,second,first,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
  have imaginaryLocal : third.locals.lookup (ofString "b2i") = some (RlpWrite.U256Value.tuple negative) := by
    simp [third,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have currentBinding : third.globals.lookup (ofString "bn_b2") = some (.val (.word b2)) := by rw [thirdGlobals]; exact b2Binding
  have stored := b2_stores_execute third b2 real negative currentBinding realLocal imaginaryLocal secondEntry.domain b2Arena b2Aligned
  let written := b2Written third b2 real negative
  have writtenSame : KeccakAbsorb.hashControl written = KeccakAbsorb.hashControl source := thirdSame
  have currentScalars : OriginalScalarGlobals.Scalars written.globals := by change OriginalScalarGlobals.Scalars third.globals; rw [thirdGlobals]; exact scalars
  have currentHeap : written.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))) := by change third.globals.lookup _ = _; rw [thirdGlobals]; exact heap
  have funded : 1 ≤ written.clock := by
    change 1 ≤ secondTarget.clock - paid
    change secondTarget.clock = firstTarget.clock - 3 at secondClock
    change firstTarget.clock = source.clock - 3 at firstClock
    omega
  obtain ⟨target,tailRun,tailClock,tailControl⟩ := after_b2_stores_execute written cursor secondEntry.installed currentScalars currentHeap secondEntry.domain lower room aligned funded
  have negRun : evaluateHOLFiniteState second negCall = (some (.returned (.val (.word 0#64))),restore second "b2i" target) := by
    rw [negCall,negativeCall]
    change (let output := evaluateHOLFiniteState third b2Stores; (output.1,restore second "b2i" output.2)) = _
    rw [stored,tailRun]
  have imaginaryRun : evaluateHOLFiniteState first imaginaryCall = (some (.returned (.val (.word 0#64))),restore first "b2i0" (restore second "b2i" target)) := by
    rw [imaginaryCall,secondCall]
    change (let output := evaluateHOLFiniteState second negCall; (output.1,restore first "b2i0" output.2)) = _
    rw [negRun]
  have realRun : evaluateHOLFiniteState inv realCall = (some (.returned (.val (.word 0#64))),restore inv "b2r" (restore first "b2i0" (restore second "b2i" target))) := by
    rw [realCall,firstCall]
    change (let output := evaluateHOLFiniteState first imaginaryCall; (output.1,restore inv "b2r" output.2)) = _
    rw [imaginaryRun]
  have run : evaluateHOLFiniteState source afterB2Allocation =
      (some (.returned (.val (.word 0#64))),restore source "inv82" (restore inv "b2r" (restore first "b2i0" (restore second "b2i" target)))) := by
    rw [arithmetic_shape,evaluateHOLFiniteState_dec_total]
    have read : evalHOLFinite source (InitializerQuads.expression inverse82) = some (RlpWrite.U256Value.tuple inverse82) := rfl
    simp only [evalHOLFinite] at read
    dsimp only
    rw [read]
    simp only [RlpWrite.U256Value.tuple,RlpWrite.U256Value.tupleShape,shapeOfHOLExact,List.map_cons,List.map_nil,shapeEqHOL_eq_true,↓reduceIte]
    exact congrArg (fun output => (output.1,restore source "inv82" output.2)) realRun
  refine ⟨_,run,?_,?_,?_⟩
  · change target.clock ≤ source.clock
    change target.clock = secondTarget.clock - paid - 1 at tailClock
    change secondTarget.clock = firstTarget.clock - 3 at secondClock
    change firstTarget.clock = source.clock - 3 at firstClock
    omega
  · change source.clock - 10 ≤ target.clock
    change target.clock = secondTarget.clock - paid - 1 at tailClock
    change secondTarget.clock = firstTarget.clock - 3 at secondClock
    change firstTarget.clock = source.clock - 3 at firstClock
    omega
  · exact tailControl.trans (InitializerAllocations.template_hash_control source written cursor [exponentAction] writtenSame)

end InitECandidate.Solver.Input.Main.BnInitialization

#print axioms InitECandidate.Solver.Input.Main.BnInitialization.arithmetic_shape
#print axioms InitECandidate.Solver.Input.Main.BnInitialization.arithmetic_execute
