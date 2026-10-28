import InitECandidate.Solver.Input.CurrentTable.FirstDiff.ByteReads
import InitECandidate.Solver.Input.CurrentTable.FirstDiff.ByteStepNormal
import InitECandidate.Solver.Input.CurrentTable.FirstDiff.ByteAnswer

namespace InitECandidate.Solver.Input.CurrentTable.FirstDiff
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Flapjack.Compiler.Encoders.Asm

structure Scan (origin source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (a b : BitVec 64) (left right : KeyBits.Key) (index : Nat) : Prop where
  frame : LocalEffects.erase source = LocalEffects.erase origin
  aCell : source.locals.lookup (ofString "a") = some (.val (.word a))
  bCell : source.locals.lookup (ofString "b") = some (.val (.word b))
  lengthCell : source.locals.lookup (ofString "key_len") = some (.val (.word 32#64))
  indexCell : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index)))
  earlier : ∀ prior : Fin 32,prior.val < index → left prior = right prior

theorem Scan.at_tick {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {a b : BitVec 64} {left right : KeyBits.Key} {index : Nat} (ready : Scan origin source a b left right index) :
    Scan origin (decClockHOLFinite source) a b left right index :=
  ⟨ready.frame,ready.aCell,ready.bCell,ready.lengthCell,ready.indexCell,ready.earlier⟩

theorem Scan.read {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {a b : BitVec 64} {left right : KeyBits.Key} {index : Nat}
    (ready : Scan origin source a b left right index) (inside : index < 32)
    (aView : ByteView origin a left) (bView : ByteView origin b right) :
    eval source readX = some (.val (.word ((left ⟨index,inside⟩ ^^^ right ⟨index,inside⟩).setWidth 64))) :=
  read_x source a b left right ⟨index,inside⟩ ready.aCell ready.bCell ready.indexCell
    (aView.of_frame ready.frame) (bView.of_frame ready.frame)

/-- Real continuation consumes one equal byte and preserves the physical
key images and actual caller bindings. -/
theorem scan_step {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {a b : BitVec 64} {left right : KeyBits.Key} {index : Nat}
    (ready : Scan origin source a b left right index) (inside : index < 32)
    (aView : ByteView origin a left) (bView : ByteView origin b right)
    (normal : evaluateHOLFiniteState source step = (none,post)) : Scan origin post a b left right (index+1) := by
  have read := ready.read inside aView bView
  have zero := step_none_zero source post _ read normal
  have equal : left ⟨index,inside⟩ = right ⟨index,inside⟩ := BitVec.xor_eq_zero_iff.mp zero
  have frame := step_readonly source.code source rfl
  rw [normal] at frame
  have saved (key : MlS) (notX : key ≠ ofString "x") (notI : key ≠ ofString "i") (notJ : key ≠ ofString "j") :=
    (step_flow key notX notI notJ).none_preserves source post normal
  have next := step_advance source post (BitVec.ofNat 64 index) ready.indexCell normal
  refine ⟨frame.trans ready.frame,(saved _ (by decide) (by decide) (by decide)).trans ready.aCell,
    (saved _ (by decide) (by decide) (by decide)).trans ready.bCell,
    (saved _ (by decide) (by decide) (by decide)).trans ready.lengthCell,?_,?_⟩
  · simpa only [BitVec.ofNat_add] using next
  · intro prior earlier
    by_cases old : prior.val < index
    · exact ready.earlier prior old
    · have same : prior = ⟨index,inside⟩ := by apply Fin.ext; change prior.val = index; omega
      simpa only [same] using equal

theorem scan_test_read {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {a b : BitVec 64} {left right : KeyBits.Key} {index : Nat}
    (ready : Scan origin source a b left right index) (bounded : index ≤ 32) :
    evalHOLFinite source (h:=fun query => Classical.propDecidable (source.memaddrs query)) test =
      some (.val (.word (if index < 32 then 1#64 else 0#64))) := by
  have number : (BitVec.ofNat 64 index).toNat = index := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp [test,localVar,evalHOLFinite,evalHOLExact,ready.indexCell,ready.lengthCell,wordCmpHOL,BitVec.lt_def,number]

end InitECandidate.Solver.Input.CurrentTable.FirstDiff

#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.scan_step
#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.scan_test_read
