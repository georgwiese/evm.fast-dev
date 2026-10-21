import InitECandidate.Solver.Headers.FieldCallCost
import InitECandidate.Solver.Headers.FieldFrame

namespace InitECandidate.Solver.Headers.Field
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Compose the actual uint-field call with a local/read-only numerical
continuation. This is used for the original word/u256 wrappers; their real
selected row and normal memory/global frame are derived before composition. -/
theorem uint_scope_normal_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer cursor limit control : BitVec 64) (bytes index : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (selected : items[index]?=some item) (model : Rlp.ListItems source pointer bytes items)
    (records : Rlp.Slices.Records source.memory array pointer items)
    (arena : Rlp.Validation.Arena source cursor limit) (allocation : AllocatedBytes.Arena array (16*items.length))
    (arrayAligned : array.toNat%8=0) (fits : pointer.toNat+bytes<2^64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some (Kind.uint.values array (BitVec.ofNat 64 index) control))
    (installed : Input.OriginalCode.Installed source.code) (tail : Input.LocalEffects.Preserves source.code continuation)
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) (.comb [.one,.one]) (ofString "hdr_uint_field") expressions continuation)=(some (.returned value),post)) :
    Rlp.Validation.Arena post cursor limit ∧ Rlp.Validation.Above source post cursor.toNat ∧
      (∀ key,post.globals.lookup key=source.globals.lookup key) := by
  obtain ⟨callee,called,calleeArray,calleeIndex,_⟩ := environment source.code.lookup .uint array (BitVec.ofNat 64 index) control (original_code source.code installed .uint)
  obtain ⟨funded,parsed,answer,inner,actual,checked,continued,endpoint⟩ := Input.CallNormal.scoped_normal source post name (.comb [.one,.one]) (ofString "hdr_uint_field") expressions _ Kind.uint.body continuation callee Kind.uint.resultShape args called value normal
  let entry:=callEntryStateHOLFinite source callee
  have entryModel : Rlp.ListItems entry pointer bytes items := Rlp.ListItems.transport source entry pointer bytes items model (by omega) (by intro offset inside; rfl)
  have entryArena:=Rlp.Validation.Arena.of_fields source entry cursor limit arena rfl rfl
  obtain ⟨rowArgs,positive,bounded,itemFits⟩ := selected_arguments entry array pointer bytes index items item selected entryModel records entryArena.domain allocation arrayAligned fits calleeArray calleeIndex
  obtain ⟨parsedArena,above,globals,_⟩ := body_normal_frame entry parsed .uint (Rlp.Slices.itemPointer pointer items index) item.total cursor limit rowArgs entryArena itemFits installed answer actual
  have code : parsed.code=source.code := (Input.evaluation_fields entry parsed Kind.uint.body (some (.returned answer)) actual).2.2.2
  let ready:=Input.CallNormal.continuationEntry source parsed name answer
  have pure:=tail ready code
  rw [continued] at pure
  have domain:=congrArg PanSemStateFiniteExact.memaddrs pure
  have currentGlobals:=congrArg PanSemStateFiniteExact.globals pure
  have memory:=congrArg PanSemStateFiniteExact.memory pure
  have postArena:=Rlp.Validation.Arena.of_fields parsed post cursor limit parsedArena
    (by rw [endpoint]; exact domain) (by rw [endpoint]; exact currentGlobals)
  refine ⟨postArena,?_,?_⟩
  · intro query beyond
    rw [endpoint]
    exact (congrFun memory query).trans (above query beyond)
  · intro key
    rw [endpoint]
    have lookup:=congrArg (fun state : HolFiniteMapExact MlS (ValueHOL 64)=>state.lookup key) currentGlobals
    exact lookup.trans (globals key)

end InitECandidate.Solver.Headers.Field

#print axioms InitECandidate.Solver.Headers.Field.uint_scope_normal_frame
