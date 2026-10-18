import InitECandidate.Solver.MutableTable.TableRuntime.Locals
import InitECandidate.Solver.WitnessRadix.AllocationNormalExpected
import InitECandidate.Solver.Input.NormalDeclarationEntry
import InitECandidate.Solver.Input.StoreNormal

namespace InitECandidate.Solver.MutableTable.TableRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix

def afterHeader : ProgHOL 64 := program (TableNew.actions.drop 6) TableNew.returnTable
def headerEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (start : Nat) :=
  bind (PersistentAlloc.nextState source "t" start (start + 72)) "stride" (BitVec.ofNat 64 (stride kind))

/-- Successful original constructor execution derives the first allocation's
room and reaches all four initial stores. Their mapping is not assumed. -/
theorem normal_header (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (start capacity : Nat)
    (startBound : start ≤ 33806089496) (startAligned : start % 8 = 0)
    (keyLocal : source.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 (KeyHash.keySize kind)))))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 capacity))))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (code : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source TableNew.body = (some (.returned value), target)) :
    start + 72 ≤ 33806089496 ∧ ∃ memory inner,
      evaluateHOLFiniteState {headerEntry source kind start with memory := memory} afterHeader = (some (.returned value), inner) := by
  rw [TableNew.body_shape] at normal
  change evaluateHOLFiniteState source (.decCall (ofString "t") .one (ofString "alloc") [.const 72#64]
    (.dec (ofString "stride") .one TableNew.stride (program TableNew.headerActions afterHeader))) = _ at normal
  obtain ⟨_, headerBound, _, headerTarget, headerRun, _⟩ := PersistentAlloc.call_normal_expected source target "t" _ _ start 72 (start + 72)
    startBound (by decide) (Nat.le_refl _) (by omega) (by omega) rfl code trapCode heap value normal
  let allocated := PersistentAlloc.nextState source "t" start (start + 72)
  have allocatedKey : allocated.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 (KeyHash.keySize kind)))) :=
    (bind_lookup_other _ "t" "key_len" _ (by decide)).trans keyLocal
  have strideRead : eval allocated TableNew.stride = some (.val (.word (BitVec.ofNat 64 (stride kind)))) := by
    cases kind <;> simp [eval, TableNew.stride, localVar, evalHOLExact, evalListHOLExact, toExact, allocatedKey,
      valueIsWord, valueWord, wordOpHOL, wordOp, AndOp.and, stride, KeyHash.keySize]
  obtain ⟨declared, inner, read, _, rest, _⟩ := Input.CallNormal.declaration_normal_entry allocated headerTarget "stride" .one TableNew.stride
    (program TableNew.headerActions afterHeader) value headerRun
  have declaredEq : declared = .val (.word (BitVec.ofNat 64 (stride kind))) := Option.some.inj (read.symm.trans strideRead)
  subst declared
  change evaluateHOLFiniteState (headerEntry source kind start) (program TableNew.headerActions afterHeader) = _ at rest
  simp only [TableNew.headerActions, program] at rest
  obtain ⟨first, rest⟩ := Input.store_normal_continue (headerEntry source kind start) inner _ _ _ value rest
  obtain ⟨second, rest⟩ := Input.store_normal_continue {headerEntry source kind start with memory := first} inner _ _ _ value rest
  obtain ⟨third, rest⟩ := Input.store_normal_continue {headerEntry source kind start with memory := second} inner _ _ _ value rest
  obtain ⟨fourth, rest⟩ := Input.store_normal_continue {headerEntry source kind start with memory := third} inner _ _ _ value rest
  exact ⟨headerBound, fourth, inner, rest⟩

theorem header_entry_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (start capacity : Nat)
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 capacity)))) (memory : WordWrites.Memory) :
    Locals {headerEntry source kind start with memory := memory} kind (BitVec.ofNat 64 start) capacity := by
  refine ⟨(bind_lookup_other _ "stride" "t" _ (by decide)).trans (bind_lookup_same _ _ _), ?_, bind_lookup_same _ _ _⟩
  exact (bind_lookup_other _ "stride" "cap" _ (by decide)).trans ((bind_lookup_other _ "t" "cap" _ (by decide)).trans capLocal)

end InitECandidate.Solver.MutableTable.TableRuntime

#print axioms InitECandidate.Solver.MutableTable.TableRuntime.normal_header
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.header_entry_locals
