import InitECandidate.Solver.Headers.U256Syntax
import InitECandidate.Solver.Headers.CurrentFieldValue
import InitECandidate.Solver.Headers.FieldRowArguments
import InitECandidate.Solver.Headers.FieldCallSyntax
import InitECandidate.Solver.Input.CurrentU256.Price
import InitECandidate.Solver.Input.WordPairEnvironment
import InitECandidate.Solver.Input.ClockCostGuardReached

namespace InitECandidate.Solver.Headers.CurrentU256
open U256Field
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem after_guard_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (fieldCell : source.locals.lookup (ofString "f")=some (.rStruct [.val (.word pointer),.val (.word length)]))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterGuard).2.clock≤max 4 length.toNat+1 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) convertArguments=some [.val (.word pointer),.val (.word length)] := by
    simp [convertArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,fieldCell]
  obtain ⟨callee,called,pointerCell,lengthCell⟩ := Input.word_pair_environment source.code.lookup (ofString "u256_from_be") (ofString "p") (ofString "n")
    Input.CurrentU256.body Input.RlpWrite.U256Value.tupleShape pointer length (by decide) (Input.CurrentU256.original_code source.code installed)
  have currentLength : (callEntryStateHOLFinite source callee).locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length.toNat))) := by
    simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
    exact lengthCell
  have price := Input.ClockCost.scoped_current source (ofString "v") Input.RlpWrite.U256Value.tupleShape (ofString "u256_from_be") convertArguments _
    Input.CurrentU256.body (.return (localVar "v")) callee Input.RlpWrite.U256Value.tupleShape (max 4 length.toNat) 0 args called
    (Input.CurrentU256.body_price (callEntryStateHOLFinite source callee) installed length.toNat length.isLt currentLength)
    (Input.ClockCost.returned source.code _)
  rw [after_guard_shape]
  exact price

/-- The actual original unsigned byte-count guard caps the reached word
conversion at thirty-three ticks, including all unmapped byte and exceptional outcomes. -/
theorem after_field_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (fieldCell : source.locals.lookup (ofString "f")=some (.rStruct [.val (.word pointer),.val (.word length)])) :
    source.clock-(evaluateHOLFiniteState source afterField).2.clock≤33 := by
  rw [field_shape]
  apply Input.ClockCost.stopping_guard_reached source guardTest (.raise (ofString "HdrErr") (.const 5#64)) afterGuard 0 33
    (Input.raise_ne_none source _ _) (Input.ClockCost.raised source.code _ _ source rfl)
  intro passed
  have bounded : length.toNat≤32 := by
    by_contra outside
    have large : 32<length.toNat := by omega
    have selected : evaluateHOLFiniteState source (.ite guardTest (.raise (ofString "HdrErr") (.const 5#64)) .skip)=
        evaluateHOLFiniteState source (.raise (ofString "HdrErr") (.const 5#64)) := by
      simp [guardTest,evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,fieldCell,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,large]
    rw [selected] at passed
    exact Input.raise_ne_none source (ofString "HdrErr") (.const 5#64) (congrArg Prod.fst passed)
  have price := after_guard_cost source pointer length fieldCell installed
  omega

theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer maximum : BitVec 64) (bytes index : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (selected : items[index]?=some item) (model : Rlp.ListItems source pointer bytes items)
    (records : Rlp.Slices.Records source.memory array pointer items)
    (arena : Input.CurrentStartup.ArenaState source) (allocation : AllocatedBytes.Arena array (16*items.length))
    (arrayAligned : array.toNat%8=0) (fits : pointer.toNat+bytes<2^64)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (maximumCell : source.locals.lookup (ofString "maxb")=some (.val (.word maximum)))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤60*item.total.toNat+45 := by
  obtain ⟨callee,called,calleeArray,calleeIndex,_⟩ := Field.environment source.code.lookup .uint array (BitVec.ofNat 64 index) maximum (Field.original_code source.code installed .uint)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Field.Kind.uint.values array (BitVec.ofNat 64 index) maximum) := by
    simp [arguments,Field.Kind.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,arrayCell,indexCell,maximumCell]
  let entry := callEntryStateHOLFinite source callee
  have entryModel : Rlp.ListItems entry pointer bytes items := Rlp.ListItems.transport source entry pointer bytes items model (by omega) (by intro offset inside; rfl)
  have entryArena : Input.CurrentStartup.ArenaState entry := arena.of_frame rfl
  obtain ⟨rowArgs,positive,bounded,itemFits⟩ := Field.selected_arguments entry array pointer bytes index items item selected entryModel records entryArena.domain allocation arrayAligned fits calleeArray calleeIndex
  have fieldPrice := CurrentField.body_cost entry .uint (Rlp.Slices.itemPointer pointer items index) item.total rowArgs entryArena itemFits installed
  have cost := Input.ClockCost.scoped_reached_current source "f" (.comb [.one,.one]) (ofString "hdr_uint_field") arguments _ Field.Kind.uint.body afterField callee Field.Kind.uint.resultShape
    (60*item.total.toNat+11) 33 args called fieldPrice ?_
  · rw [body_shape]
    exact cost
  · intro parsed answer actual checked
    obtain ⟨header,payload,valid,valueEq⟩ := CurrentField.body_normal_value entry parsed .uint (Rlp.Slices.itemPointer pointer items index) item.total rowArgs entryArena itemFits answer actual
    have nextCode := (Input.evaluation_fields entry parsed Field.Kind.uint.body (some (.returned answer)) actual).2.2.2
    have nextInstalled : Input.OriginalCode.Installed parsed.code := by rw [nextCode]; exact installed
    rw [valueEq]
    exact after_field_cost (Input.CallNormal.continuationEntry source parsed "f" (Field.Kind.uint.returnValue (Rlp.Slices.itemPointer pointer items index+header) payload))
      (Rlp.Slices.itemPointer pointer items index+header) payload nextInstalled
      (by simp [Input.CallNormal.continuationEntry,Field.Kind.returnValue,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE])

end InitECandidate.Solver.Headers.CurrentU256

#print axioms InitECandidate.Solver.Headers.CurrentU256.after_guard_cost
#print axioms InitECandidate.Solver.Headers.CurrentU256.after_field_cost
#print axioms InitECandidate.Solver.Headers.CurrentU256.body_cost
