import InitECandidate.Solver.MutableTable.WitnessDatabaseLookup
import InitECandidate.Solver.MutableTable.WitnessDatabaseFields
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Every actual normal lookup at arbitrary funding returns the genuine
bounded witness slice and preserves all nonlocal state. Padding transports a
known execution; it adds no premise about the caller's available clock. -/
theorem Database.body_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (array table : BitVec 64) (count maximum : Nat)
    (slices : Nat→Graph.Slice) (scratch queryPointer : BitVec 64)
    (actual : Database source array table count maximum slices scratch)
    (installed : Input.OriginalCode.Installed source.code)
    (query : Find.Key32) (view : MemoryBytes.ByteView source queryPointer query) (fits : queryPointer.toNat+32<2^64)
    (dbLocal : source.locals.lookup (ofString "db")=some (.val (.word table)))
    (hashLocal : source.locals.lookup (ofString "hash")=some (.val (.word queryPointer)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source NodeDb.body=(some (.returned value),post)) :
    ∃ answer,value=NodeDb.output answer ∧ Input.LocalEffects.erase post=Input.LocalEffects.erase source ∧
      source.clock-post.clock≤6*count+3 ∧
      (∀ slice,answer=some slice→∃ index<count,slice=slices index ∧ slice.2.toNat≤maximum ∧
        AllocatedBytes.Arena slice.1 slice.2.toNat ∧ 2713731432≤slice.1.toNat ∧ slice.1.toNat+slice.2.toNat≤table.toNat) := by
  let padding:=6*count+3
  let funded:={source with clock:=source.clock+padding}
  have paddedRun:=panPropsEvaluateAddClockEq NodeDb.body source (some (.returned value)) post padding ⟨normal,by intro impossible; cases impossible⟩
  have ready:=actual.of_fields source funded array table count maximum slices scratch rfl rfl rfl
  have queryView:=MemoryBytes.byteView_of_fields source funded rfl rfl rfl queryPointer query view
  obtain ⟨answer,paid,target,price,known,frame,hit⟩ := ready.execute funded array table count maximum slices scratch queryPointer installed query queryView fits dbLocal hashLocal
    (by change padding≤source.clock+padding; omega)
  have resultEq:=congrArg Prod.fst (known.symm.trans paddedRun)
  have valueEq : value=NodeDb.output answer := by
    simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using resultEq.symm
  have targetEq : target={post with clock:=post.clock+padding} := congrArg Prod.snd (known.symm.trans paddedRun)
  have pure:=congrArg Input.LocalEffects.erase frame
  change Input.LocalEffects.erase target=Input.LocalEffects.erase source at pure
  rw [targetEq] at pure
  have price:=actual.body_cost source array table count maximum slices scratch queryPointer installed query view fits dbLocal hashLocal
  rw [normal] at price
  exact ⟨answer,valueEq,pure,price,hit⟩

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Database.body_returned
