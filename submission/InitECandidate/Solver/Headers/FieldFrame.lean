import InitECandidate.Solver.Headers.FieldCost
import InitECandidate.Solver.Rlp.DecodeGlobals

namespace InitECandidate.Solver.Headers.Field
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- All actual outcomes of the three original field helpers preserve every
global except the scratch cursor; the normal contract restores that too. -/
theorem globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code)
    (other : key≠ofString "scratch_ptr") (kind : Kind) : Input.GlobalEffects.Preserves key code kind.body := by
  rw [body_shape]
  exact Input.GlobalEffects.scoped_body key code (ofString "it") Rlp.Item.resultShape (ofString "rlp_item") arguments kind.afterItem
    Rlp.Header.formals Rlp.Item.body Rlp.Item.resultShape (Rlp.Item.original_code code installed) (Rlp.Item.globals key code installed other)
    (Input.GlobalEffects.of_readonly key code kind.afterItem (after_item_readonly code kind))

/-- A genuine normal helper return retains its original input region and
all globals, including the restored scratch cursor. There is no premise
about any future field result, digest or later caller execution. -/
theorem body_normal_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (pointer length cursor limit : BitVec 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Rlp.Header.values pointer length))
    (arena : Rlp.Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source kind.body=(some (.returned value),post)) :
    Rlp.Validation.Arena post cursor limit ∧ Rlp.Validation.Above source post cursor.toNat ∧
      (∀ key,post.globals.lookup key=source.globals.lookup key) ∧ source.clock-post.clock≤60*length.toNat+42 := by
  have price := body_cost source kind pointer length cursor limit args arena fits installed
  rw [normal] at price
  have run := normal
  rw [body_shape] at run
  obtain ⟨funded,parsed,header,payload,flag,inner,valid,nextArena,above,domain,endian,code,heap,cost,continued,endpoint⟩ :=
    Rlp.Item.scoped_normal_above source post pointer length cursor limit "it" arguments kind.afterItem args arena fits installed value run
  let ready := Input.CallNormal.continuationEntry source parsed "it" (Rlp.Item.result pointer header payload flag)
  have pure := after_item_readonly source.code kind ready code
  rw [continued] at pure
  have tailDomain := congrArg PanSemStateFiniteExact.memaddrs pure
  have tailGlobals := congrArg PanSemStateFiniteExact.globals pure
  have postArena : Rlp.Validation.Arena post cursor limit := Rlp.Validation.Arena.of_fields parsed post cursor limit nextArena
    (by rw [endpoint]; exact tailDomain)
    (by rw [endpoint]; exact tailGlobals)
  refine ⟨postArena,?_,?_,price⟩
  · intro query beyond
    rw [endpoint]
    have memory := congrArg PanSemStateFiniteExact.memory pure
    exact (congrFun memory query).trans (above query beyond)
  · intro key
    by_cases scratch : key=ofString "scratch_ptr"
    · rw [scratch,postArena.cursorGlobal,arena.cursorGlobal]
    · have same := globals key source.code installed scratch kind source rfl
      rw [normal] at same
      exact congrArg Prod.snd same

end InitECandidate.Solver.Headers.Field

#print axioms InitECandidate.Solver.Headers.Field.globals
#print axioms InitECandidate.Solver.Headers.Field.body_normal_frame
