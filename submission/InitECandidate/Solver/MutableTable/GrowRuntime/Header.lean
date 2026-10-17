import InitECandidate.Solver.MutableTable.GrowRuntime.Allocations
import InitECandidate.Solver.MutableTable.GrowRuntime.Reads

namespace InitECandidate.Solver.MutableTable.GrowRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix

def headerState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan) (count : Nat) :=
  WitnessRadix.QueryBranch.bind (WitnessRadix.QueryBranch.bind (WitnessRadix.QueryBranch.bind (WitnessRadix.QueryBranch.bind
    (WitnessRadix.QueryBranch.bind (WitnessRadix.QueryBranch.bind (WitnessRadix.QueryBranch.bind source "cap" (BitVec.ofNat 64 old.capacity))
      "stride" (BitVec.ofNat 64 (NaturalLayout.stride kind))) "keys" (cell old .keys 0)) "vals" (cell old .values 0))
    "order" (cell old .order 0)) "nitems" (BitVec.ofNat 64 count)) "ncap" (BitVec.ofNat 64 (2 * old.capacity))

theorem header_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (valid : Valid kind old) (domain : source.memaddrs = InitE.ordinaryDomain) (count : Nat)
    (header : MemoryModel.Header source.memory kind old (BitVec.ofNat 64 count))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell old .header 0)))) :
    ∃ restoreStack, Executes source (Grow.actions.take 7) (headerState source kind old count) restoreStack := by
  let sc := WitnessRadix.QueryBranch.bind source "cap" (BitVec.ofNat 64 old.capacity)
  let ss := WitnessRadix.QueryBranch.bind sc "stride" (BitVec.ofNat 64 (NaturalLayout.stride kind))
  let sk := WitnessRadix.QueryBranch.bind ss "keys" (cell old .keys 0)
  let sv := WitnessRadix.QueryBranch.bind sk "vals" (cell old .values 0)
  let so := WitnessRadix.QueryBranch.bind sv "order" (cell old .order 0)
  let sn := WitnessRadix.QueryBranch.bind so "nitems" (BitVec.ofNat 64 count)
  have tC : sc.locals.lookup (ofString "t") = some (.val (.word (cell old .header 0))) := (bind_lookup_other _ "cap" "t" _ (by decide)).trans tableLocal
  have tS : ss.locals.lookup (ofString "t") = some (.val (.word (cell old .header 0))) := (bind_lookup_other _ "stride" "t" _ (by decide)).trans tC
  have tK : sk.locals.lookup (ofString "t") = some (.val (.word (cell old .header 0))) := (bind_lookup_other _ "keys" "t" _ (by decide)).trans tS
  have tV : sv.locals.lookup (ofString "t") = some (.val (.word (cell old .header 0))) := (bind_lookup_other _ "vals" "t" _ (by decide)).trans tK
  have tO : so.locals.lookup (ofString "t") = some (.val (.word (cell old .header 0))) := (bind_lookup_other _ "order" "t" _ (by decide)).trans tV
  have read (target : PanSemStateFiniteExact 64 Guest.HostMemory) (memory : target.memory = source.memory) (mapping : target.memaddrs = source.memaddrs)
      (table : target.locals.lookup (ofString "t") = some (.val (.word (cell old .header 0)))) (offset : Nat) (aligned : offset % 8 = 0) (inside : offset < 72)
      (value : BitVec 64) (member : (offset, value) ∈ MemoryModel.headerEntries kind old (BitVec.ofNat 64 count)) :
      eval target (Find.tableLoad (BitVec.ofNat 64 offset)) = some (.val (.word value)) := by
    apply Find.table_read target (cell old .header 0) _ value table
    · rw [mapping, domain, constant_cell]
      exact mapped kind old valid .header offset inside aligned
    · rw [memory, constant_cell]
      exact header offset value member
  have capRead := read source rfl rfl tableLocal 16 (by decide) (by decide) (BitVec.ofNat 64 old.capacity) (by simp [MemoryModel.headerEntries])
  have strideRead := read sc rfl rfl tC 8 (by decide) (by decide) (BitVec.ofNat 64 (NaturalLayout.stride kind)) (by simp [MemoryModel.headerEntries])
  have keysRead := read ss rfl rfl tS 32 (by decide) (by decide) (cell old .keys 0) (by simp [MemoryModel.headerEntries])
  have valuesRead := read sk rfl rfl tK 40 (by decide) (by decide) (cell old .values 0) (by simp [MemoryModel.headerEntries])
  have orderRead := read sv rfl rfl tV 56 (by decide) (by decide) (cell old .order 0) (by simp [MemoryModel.headerEntries])
  have countRead := read so rfl rfl tO 24 (by decide) (by decide) (BitVec.ofNat 64 count) (by simp [MemoryModel.headerEntries])
  have capN : sn.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 old.capacity))) :=
    (bind_lookup_other _ "nitems" "cap" _ (by decide)).trans ((bind_lookup_other _ "order" "cap" _ (by decide)).trans
      ((bind_lookup_other _ "vals" "cap" _ (by decide)).trans ((bind_lookup_other _ "keys" "cap" _ (by decide)).trans
        ((bind_lookup_other _ "stride" "cap" _ (by decide)).trans (bind_lookup_same _ _ _)))))
  have doubleRead : eval sn (Grow.times (localVar "cap") (.const 2#64)) = some (.val (.word (BitVec.ofNat 64 (2 * old.capacity)))) := by
    simp [eval, Grow.times, localVar, evalHOLExact, evalListHOLExact, toExact, capN, valueIsWord, valueWord, panOpHOL,
      ← BitVec.ofNat_mul, Nat.mul_comm old.capacity 2]
  refine ⟨(fun target => restore source "cap" (restore sc "stride" (restore ss "keys" (restore sk "vals" (restore sv "order" (restore so "nitems" (restore sn "ncap" target))))))), ?_⟩
  simp only [Grow.actions, List.take, List.take_zero]
  exact .declare _ capRead (.declare _ strideRead (.declare _ keysRead (.declare _ valuesRead
    (.declare _ orderRead (.declare _ countRead (.declare _ doubleRead (.done _)))))))

end InitECandidate.Solver.MutableTable.GrowRuntime

#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.header_execute
