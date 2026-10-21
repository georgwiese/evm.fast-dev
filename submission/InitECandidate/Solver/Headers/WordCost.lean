import InitECandidate.Solver.Headers.WordProgram
import InitECandidate.Solver.Headers.FieldCallCost

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
  exact (after_guard_cost source pointer length fieldCell).trans bounded

/-- Complete original hdr_word_field206, from its real selected RLP row and
normal uint-field result; the guarded byte loop adds at most eight ticks. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer cursor limit : BitVec 64) (bytes index : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (selected : items[index]?=some item) (model : Rlp.ListItems source pointer bytes items)
    (records : Rlp.Slices.Records source.memory array pointer items)
    (arena : Rlp.Validation.Arena source cursor limit) (allocation : AllocatedBytes.Arena array (16*items.length))
    (arrayAligned : array.toNat%8=0) (fits : pointer.toNat+bytes<2^64)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤60*item.total.toNat+51 := by
  obtain ⟨callee,called,calleeArray,calleeIndex,_⟩ := Field.environment source.code.lookup .uint array (BitVec.ofNat 64 index) 0#64 (Field.original_code source.code installed .uint)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Field.Kind.uint.values array (BitVec.ofNat 64 index) 0#64) := by
    simp [arguments,Field.Kind.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,arrayCell,indexCell]
  let entry := callEntryStateHOLFinite source callee
  have entryModel : Rlp.ListItems entry pointer bytes items := Rlp.ListItems.transport source entry pointer bytes items model (by omega) (by intro offset inside; rfl)
  have entryArena := Rlp.Validation.Arena.of_fields source entry cursor limit arena rfl rfl
  obtain ⟨rowArgs,positive,bounded,itemFits⟩ := Field.selected_arguments entry array pointer bytes index items item selected entryModel records entryArena.domain allocation arrayAligned fits calleeArray calleeIndex
  have fieldPrice := Field.body_cost entry .uint (Rlp.Slices.itemPointer pointer items index) item.total cursor limit rowArgs entryArena itemFits installed
  have cost := Input.ClockCost.scoped_reached_current source "f" (.comb [.one,.one]) (ofString "hdr_uint_field") arguments _ Field.Kind.uint.body afterField callee Field.Kind.uint.resultShape
    (60*item.total.toNat+42) 8 args called fieldPrice ?_
  · rw [body_shape]
    exact cost
  · intro parsed answer actual checked
    obtain ⟨header,payload,valid,valueEq⟩ := Field.body_normal_value entry parsed .uint (Rlp.Slices.itemPointer pointer items index) item.total cursor limit rowArgs entryArena itemFits installed answer actual
    rw [valueEq]
    exact after_field_cost (Input.CallNormal.continuationEntry source parsed "f" (Field.Kind.uint.returnValue (Rlp.Slices.itemPointer pointer items index+header) payload))
      (Rlp.Slices.itemPointer pointer items index+header) payload
      (by simp [Input.CallNormal.continuationEntry,Field.Kind.returnValue,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE])

end InitECandidate.Solver.Headers.WordField

#print axioms InitECandidate.Solver.Headers.WordField.loop_cost
#print axioms InitECandidate.Solver.Headers.WordField.after_guard_cost
#print axioms InitECandidate.Solver.Headers.WordField.after_field_cost
#print axioms InitECandidate.Solver.Headers.WordField.body_cost
