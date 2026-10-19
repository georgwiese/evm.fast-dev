import InitECandidate.Solver.Rlp.SlicesLoopNormal
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.Input.SequenceReturned

namespace InitECandidate.Solver.Rlp.Slices
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def result (array count : BitVec 64) : ValueHOL 64 := .rStruct [.val (.word array),.val (.word count)]
def seeded (source : PanSemStateFiniteExact 64 Guest.HostMemory) := bind (bind source "i" 0#64) "off" 0#64

theorem after_alloc_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length array count : BitVec 64) (items : List ListItem)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (countCell : source.locals.lookup (ofString "count")=some (.val (.word count)))
    (model : ListItems source pointer length.toNat items) (countEq : count.toNat=items.length)
    (before : pointer.toNat+length.toNat≤array.toNat) (arrayFits : array.toNat+16*count.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterAlloc=(some (.returned value),target)) :
    value=result array count ∧ Records target.memory array pointer items ∧ target.globals=source.globals ∧
      Window source target array.toNat (array.toNat+16*count.toNat) := by
  rw [after_alloc_shape] at normal
  obtain ⟨indexInner,indexRun,indexRestore⟩ := Input.declaration_return_word source target "i" (.const 0#64) 0#64 _ value rfl normal
  let indexed := bind source "i" 0#64
  obtain ⟨offsetInner,offsetRun,offsetRestore⟩ := Input.declaration_return_word indexed indexInner "off" (.const 0#64) 0#64 _ value rfl indexRun
  have safe : Input.LocalPrefix (ofString "count") loop := by rw [loop_shape]; exact .loop condition loop_body_safe
  obtain ⟨middle,loopRun,returnRun,preserved⟩ := safe.normal_continue (seeded source) offsetInner returnArray value offsetRun
  have entry : Locals (seeded source) pointer array 0#64 0#64 count :=
    ⟨(bind_lookup_other _ "off" "p" _ (by decide)).trans ((bind_lookup_other _ "i" "p" _ (by decide)).trans pointerCell),
      (bind_lookup_other _ "off" "arr" _ (by decide)).trans ((bind_lookup_other _ "i" "arr" _ (by decide)).trans arrayCell),
      (bind_lookup_other _ "off" "i" _ (by decide)).trans (bind_lookup_same _ _ _),bind_lookup_same _ _ _,
      (bind_lookup_other _ "off" "count" _ (by decide)).trans ((bind_lookup_other _ "i" "count" _ (by decide)).trans countCell)⟩
  have currentItems := ListItems.transport source (seeded source) pointer length.toNat items model length.isLt (by intro offset inside; rfl)
  obtain ⟨records,finalView,globals,frame⟩ := loop_records (seeded source) middle pointer length array 0#64 0#64 count items entry
    (by simpa using currentItems) (by simp) (by simpa using countEq) before arrayFits installed loopRun
  have expected : eval middle (.rstruct [localVar "arr",localVar "count"])=some (result array count) := by
    simp [result,eval,evalHOLExact,evalListHOLExact,localVar,toExact,finalView.arrayCell,finalView.countCell]
  obtain ⟨actual,returned⟩ := Input.return_normal middle offsetInner _ value returnRun
  refine ⟨Option.some.inj (actual.symm.trans expected),?_,?_,?_⟩
  · rw [indexRestore,offsetRestore,returned]
    change Records middle.memory array pointer items
    simpa [row] using records
  · rw [indexRestore,offsetRestore,returned]
    exact globals
  · intro query outside
    rw [indexRestore,offsetRestore,returned]
    exact frame query (by simpa using outside)

end InitECandidate.Solver.Rlp.Slices

#print axioms InitECandidate.Solver.Rlp.Slices.after_alloc_normal
