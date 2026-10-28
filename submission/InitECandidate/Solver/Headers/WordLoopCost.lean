import InitECandidate.Solver.Headers.WordProgram

namespace InitECandidate.Solver.Headers.WordField
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length index : BitVec 64)
    (fieldCell : source.locals.lookup (ofString "f")=some (.rStruct [.val (.word pointer),.val (.word length)]))
    (indexCell : source.locals.lookup (ofString "j")=some (.val (.word index))) (bounded : index.toNat≤length.toNat) :
    source.clock-(evaluateHOLFiniteState source loop).2.clock≤length.toNat-index.toNat := by
  rw [loop_shape]
  have price := Input.CounterFlow.loop_expression_cost source.code (ofString "j") (ofString "f")
    (.rStruct [.val (.word pointer),.val (.word length)]) (.rfield 1 (localVar "f")) loopBody 0 length.toNat length.isLt
    (loop_body_price source.code) loop_body_advance loop_body_snapshot ?_ source index rfl indexCell fieldCell bounded
  · simpa only [condition,localVar,Nat.zero_add,Nat.one_mul] using price
  · intro current cell
    simp [evalHOLFinite,evalHOLExact,localVar,toExact,cell,BitVec.ofNat_toNat,BitVec.setWidth_eq]

theorem after_guard_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (fieldCell : source.locals.lookup (ofString "f")=some (.rStruct [.val (.word pointer),.val (.word length)])) :
    source.clock-(evaluateHOLFiniteState source afterGuard).2.clock≤length.toNat := by
  rw [after_guard_shape]
  apply Input.ClockCost.declared_current source "v" (.const 0#64) 0#64 _ length.toNat rfl
  let initial := bind source "v" 0#64
  apply Input.ClockCost.declared_current initial "j" (.const 0#64) 0#64 _ length.toNat rfl
  let entered := bind initial "j" 0#64
  have currentIndex : entered.locals.lookup (ofString "j")=some (.val (.word 0#64)) := bind_lookup_same _ _ _
  have currentField : entered.locals.lookup (ofString "f")=some (.rStruct [.val (.word pointer),.val (.word length)]) :=
    (bind_lookup_other _ "j" "f" _ (by decide)).trans ((bind_lookup_other _ "v" "f" _ (by decide)).trans fieldCell)
  have cost := loop_cost entered pointer length 0#64 currentField currentIndex (by simp)
  exact Input.ClockCost.sequence_current entered loop (.return (localVar "v")) length.toNat 0
    (by simpa only [BitVec.toNat_zero,Nat.sub_zero] using cost) (Input.ClockCost.returned entered.code _)

/-- The actual original unsigned byte-count guard caps the reached word
loop at eight ticks, including all unmapped byte and exceptional outcomes. -/
theorem after_field_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (fieldCell : source.locals.lookup (ofString "f")=some (.rStruct [.val (.word pointer),.val (.word length)])) :
    source.clock-(evaluateHOLFiniteState source afterField).2.clock≤8 := by
  rw [field_shape]
  apply Input.ClockCost.stopping_guard_reached source guardTest (.raise (ofString "HdrErr") (.const 4#64)) afterGuard 0 8
    (Input.raise_ne_none source _ _) (Input.ClockCost.raised source.code _ _ source rfl)
  intro passed
  have bounded : length.toNat≤8 := by
    by_contra outside
    have large : 8<length.toNat := by omega
    have selected : evaluateHOLFiniteState source (.ite guardTest (.raise (ofString "HdrErr") (.const 4#64)) .skip)=
        evaluateHOLFiniteState source (.raise (ofString "HdrErr") (.const 4#64)) := by
      simp [guardTest,evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,fieldCell,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,large]
    rw [selected] at passed
    exact Input.raise_ne_none source (ofString "HdrErr") (.const 4#64) (congrArg Prod.fst passed)
  exact Nat.le_trans (after_guard_cost source pointer length fieldCell) bounded

end InitECandidate.Solver.Headers.WordField

#print axioms InitECandidate.Solver.Headers.WordField.loop_cost
#print axioms InitECandidate.Solver.Headers.WordField.after_guard_cost
#print axioms InitECandidate.Solver.Headers.WordField.after_field_cost
