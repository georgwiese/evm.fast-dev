import InitECandidate.Solver.Mpt.AccountFieldCost
import InitECandidate.Solver.Mpt.AccountDecodeTailCost
import InitECandidate.Solver.Rlp.ListItemsTotal

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def lastField : ProgHOL 64 := .decCall (ofString "f3") Rlp.Item.resultShape (ofString "rlp_item") (fieldArguments 3) afterFields
def lastTwo : ProgHOL 64 := .decCall (ofString "f2") Rlp.Item.resultShape (ofString "rlp_item") (fieldArguments 2) lastField
def lastThree : ProgHOL 64 := .decCall (ofString "f1") Rlp.Item.resultShape (ofString "rlp_item") (fieldArguments 1) lastTwo

theorem last_field_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer length cursor limit out : BitVec 64) (cutoff : Nat) (a b c d : Rlp.ListItem)
    (pointer0 header0 payload0 flag0 pointer1 header1 payload1 flag1 : BitVec 64)
    (view : FieldsView source array pointer length cursor limit out cutoff [a,b,c,d])
    (cell0 : source.locals.lookup (ofString "f0")=some (Rlp.Item.result pointer0 header0 payload0 flag0))
    (cell1 : source.locals.lookup (ofString "f1")=some (Rlp.Item.result pointer1 header1 payload1 flag1))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source lastField).2.clock≤60*d.size+86 := by
  rw [lastField]
  have priced := field_cost source array pointer length cursor limit out cutoff [a,b,c,d] 3 d "f3" afterFields 44 view
    (by rfl) (by decide) (by decide) installed ?_
  · omega
  · intro post header payload flag valid nextView codeEq
    let value := Rlp.Item.result (Rlp.Slices.itemPointer pointer [a,b,c,d] 3) header payload flag
    let ready := Input.CallNormal.continuationEntry source post "f3" value
    have next0 := (Input.CallNormal.continuation_lookup_other source post "f3" "f0" value (by decide)).trans cell0
    have next1 := (Input.CallNormal.continuation_lookup_other source post "f3" "f1" value (by decide)).trans cell1
    have currentInstalled : Input.OriginalCode.Installed ready.code := by change Input.OriginalCode.Installed post.code; rw [codeEq]; exact installed
    exact after_fields_cost ready out pointer0 header0 payload0 flag0 pointer1 header1 payload1 flag1
      nextView.outputCell next0 next1 nextView.output nextView.arena.domain currentInstalled

theorem last_two_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer length cursor limit out : BitVec 64) (cutoff : Nat) (a b c d : Rlp.ListItem)
    (pointer0 header0 payload0 flag0 pointer1 header1 payload1 flag1 : BitVec 64)
    (view : FieldsView source array pointer length cursor limit out cutoff [a,b,c,d])
    (cell0 : source.locals.lookup (ofString "f0")=some (Rlp.Item.result pointer0 header0 payload0 flag0))
    (cell1 : source.locals.lookup (ofString "f1")=some (Rlp.Item.result pointer1 header1 payload1 flag1))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source lastTwo).2.clock≤60*(c.size+d.size)+128 := by
  rw [lastTwo]
  have priced := field_cost source array pointer length cursor limit out cutoff [a,b,c,d] 2 c "f2" lastField (60*d.size+86) view
    (by rfl) (by decide) (by decide) installed ?_
  · omega
  · intro post header payload flag valid nextView codeEq
    let value := Rlp.Item.result (Rlp.Slices.itemPointer pointer [a,b,c,d] 2) header payload flag
    let ready := Input.CallNormal.continuationEntry source post "f2" value
    have next0 := (Input.CallNormal.continuation_lookup_other source post "f2" "f0" value (by decide)).trans cell0
    have next1 := (Input.CallNormal.continuation_lookup_other source post "f2" "f1" value (by decide)).trans cell1
    have currentInstalled : Input.OriginalCode.Installed ready.code := by change Input.OriginalCode.Installed post.code; rw [codeEq]; exact installed
    exact last_field_cost ready array pointer length cursor limit out cutoff a b c d
      pointer0 header0 payload0 flag0 pointer1 header1 payload1 flag1 nextView next0 next1 currentInstalled

theorem last_three_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer length cursor limit out : BitVec 64) (cutoff : Nat) (a b c d : Rlp.ListItem)
    (pointer0 header0 payload0 flag0 : BitVec 64)
    (view : FieldsView source array pointer length cursor limit out cutoff [a,b,c,d])
    (cell0 : source.locals.lookup (ofString "f0")=some (Rlp.Item.result pointer0 header0 payload0 flag0))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source lastThree).2.clock≤60*(b.size+c.size+d.size)+170 := by
  rw [lastThree]
  have priced := field_cost source array pointer length cursor limit out cutoff [a,b,c,d] 1 b "f1" lastTwo (60*(c.size+d.size)+128) view
    (by rfl) (by decide) (by decide) installed ?_
  · omega
  · intro post header payload flag valid nextView codeEq
    let fieldPointer := Rlp.Slices.itemPointer pointer [a,b,c,d] 1
    let value := Rlp.Item.result fieldPointer header payload flag
    let ready := Input.CallNormal.continuationEntry source post "f1" value
    have next0 := (Input.CallNormal.continuation_lookup_other source post "f1" "f0" value (by decide)).trans cell0
    have next1 := Input.CallNormal.continuation_lookup_same source post "f1" value
    have currentInstalled : Input.OriginalCode.Installed ready.code := by change Input.OriginalCode.Installed post.code; rw [codeEq]; exact installed
    exact last_two_cost ready array pointer length cursor limit out cutoff a b c d
      pointer0 header0 payload0 flag0 fieldPointer header payload flag nextView next0 next1 currentInstalled

/-- All four original account field calls, followed by the complete actual
post-field decoder, are linear in their jointly covered input bytes. Failed
record reads and helper outcomes remain included. -/
theorem fields_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer length cursor limit out : BitVec 64) (cutoff : Nat) (a b c d : Rlp.ListItem)
    (view : FieldsView source array pointer length cursor limit out cutoff [a,b,c,d])
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source fields).2.clock≤60*length.toNat+212 := by
  rw [fields_shape]
  change source.clock-(evaluateHOLFiniteState source (.decCall (ofString "f0") Rlp.Item.resultShape (ofString "rlp_item") (fieldArguments 0) lastThree)).2.clock≤60*length.toNat+212
  have extent := Rlp.ListItems.total_size source pointer length.toNat [a,b,c,d] view.itemsModel
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at extent
  have priced := field_cost source array pointer length cursor limit out cutoff [a,b,c,d] 0 a "f0" lastThree (60*(b.size+c.size+d.size)+170) view
    (by rfl) (by decide) (by decide) installed ?_
  · omega
  · intro post header payload flag valid nextView codeEq
    let fieldPointer := Rlp.Slices.itemPointer pointer [a,b,c,d] 0
    let value := Rlp.Item.result fieldPointer header payload flag
    let ready := Input.CallNormal.continuationEntry source post "f0" value
    have next0 := Input.CallNormal.continuation_lookup_same source post "f0" value
    have currentInstalled : Input.OriginalCode.Installed ready.code := by change Input.OriginalCode.Installed post.code; rw [codeEq]; exact installed
    exact last_three_cost ready array pointer length cursor limit out cutoff a b c d
      fieldPointer header payload flag nextView next0 currentInstalled

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.last_field_cost
#print axioms InitECandidate.Solver.Mpt.AccountDecode.last_two_cost
#print axioms InitECandidate.Solver.Mpt.AccountDecode.last_three_cost
#print axioms InitECandidate.Solver.Mpt.AccountDecode.fields_cost
