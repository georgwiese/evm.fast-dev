import InitECandidate.Solver.MutableTable.TableState
import Mathlib.Logic.Function.Basic

namespace InitECandidate.Solver.MutableTable.TableFamily
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout

structure Object where
  kind : KeyHash.Kind
  plan : Plan
  slots : List Nat
  floor : Nat

def Object.pointer (object : Object) : BitVec 64 := cell object.plan .header 0

def Apart (first second : Object) : Prop := ∀ left right,
  first.plan.base left + size first.kind first.plan left ≤ second.plan.base right ∨
    second.plan.base right + size second.kind second.plan right ≤ first.plan.base left

theorem Apart.symm {first second : Object} (apart : Apart first second) : Apart second first := by
  intro left right
  exact (apart right left).symm

/-- Physical models for every live table at one actual heap cursor. The
index tracks stable table identity even when any array is relocated. -/
structure Model {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → Object) : Prop where
  tables : ∀ index, TableState source (objects index).kind (objects index).plan (objects index).slots cursor (objects index).floor
  apart : ∀ first second, first ≠ second → Apart (objects first) (objects second)

theorem Model.pointer_injective {ι : Type} {source : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor : Nat} {objects : ι → Object}
    (model : Model source cursor objects) : Function.Injective (fun index => (objects index).pointer) := by
  intro first second same
  by_contra different
  have separation := model.apart first second different .header .header
  have numbers := congrArg BitVec.toNat same
  change (cell (objects first).plan .header 0).toNat = (cell (objects second).plan .header 0).toNat at numbers
  rw [base_number (objects first).kind (objects first).plan (model.tables first).valid .header,
    base_number (objects second).kind (objects second).plan (model.tables second).valid .header] at numbers
  change (objects first).plan.base .header + 72 ≤ (objects second).plan.base .header ∨
    (objects second).plan.base .header + 72 ≤ (objects first).plan.base .header at separation
  omega

end InitECandidate.Solver.MutableTable.TableFamily

#print axioms InitECandidate.Solver.MutableTable.TableFamily.Apart.symm
#print axioms InitECandidate.Solver.MutableTable.TableFamily.Model.pointer_injective
