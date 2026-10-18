import InitECandidate.Solver.MutableTable.DeleteHashExecution
import InitECandidate.Solver.MutableTable.MaskedPath

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure ScanLocals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (hole slot : Nat)
    : Prop extends Move.Locals source kind plan hole slot where
  cap : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 plan.capacity)))
  used : source.locals.lookup (ofString "used") = some (.val (.word (cell plan .used 0)))

theorem next_j_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cap index : BitVec 64)
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (indexLocal : source.locals.lookup (ofString "j") = some (.val (.word index))) :
    eval source nextJ = some (.val (.word ((index + 1#64) &&& (cap - 1#64)))) := by
  have fold (first second : BitVec 64) : AndOp.and first (AndOp.and second (18446744073709551615#64)) = first &&& second := by
    change first &&& (second &&& BitVec.allOnes 64) = first &&& second
    rw [BitVec.and_allOnes]
  simp [eval, nextJ, Find.mask, localVar, evalHOLExact, evalListHOLExact, toExact, capLocal, indexLocal,
    valueIsWord, valueWord, wordOpHOL, wordOp, fold]

theorem scan_advance (bits start cursor : Nat) (small : bits < 64) :
    ((Find.pathIndex bits start cursor + 1#64) &&& (BitVec.ofNat 64 (2 ^ bits) - 1#64)) = Find.pathIndex bits start (cursor + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [Probe.increment _ bits small (by rw [Find.path_number bits start cursor small]; exact Nat.mod_lt _ (Nat.two_pow_pos bits)),
    Find.path_number bits start cursor small, Find.path_number bits start (cursor + 1) small]
  simp only [Probe.slot, Nat.mod_add_mod, Nat.add_assoc]

theorem increment_j_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (bits start cursor : Nat)
    (small : bits < 64)
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 (2 ^ bits)))))
    (indexLocal : source.locals.lookup (ofString "j") = some (.val (.word (Find.pathIndex bits start cursor)))) :
    evaluateHOLFiniteState source incrementJ = (none, WitnessRadix.QueryBranch.bind source "j" (Find.pathIndex bits start (cursor + 1))) := by
  have read := next_j_read source _ _ capLocal indexLocal
  rw [scan_advance bits start cursor small] at read
  exact StateSteps.assign_execute source "j" nextJ _ _ indexLocal read

theorem empty_test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (index : BitVec 64) (byte : UInt8)
    (usedLocal : source.locals.lookup (ofString "used") = some (.val (.word (cell plan .used 0))))
    (indexLocal : source.locals.lookup (ofString "j") = some (.val (.word index)))
    (loaded : Find.usedByte source (parameters kind plan 0#64) index = some byte) :
    eval source emptyTest = some (.val (.word (if byte.toNat = 0 then 1#64 else 0#64))) := by
  classical
  have zero : BitVec.ofNat 64 byte.toNat = 0#64 ↔ byte.toNat = 0 := by
    have small : byte.toNat < 2 ^ 64 := by have bound : byte.toNat < 256 := byte.toNat_lt_size; omega
    constructor
    · intro same
      have number := congrArg BitVec.toNat same
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] using number
    · intro same; simp [same]
  change @panMemLoadByteHOL 64 _ source.memory source.memaddrs (fun address => Classical.propDecidable (source.memaddrs address))
    source.be (cell plan .used 0 + index) = some byte at loaded
  simp [eval, emptyTest, usedLoad, localVar, evalHOLExact, evalListHOLExact, toExact, usedLocal, indexLocal,
    valueIsWord, valueWord, wordOpHOL, wordOp, loaded, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, zero]

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.next_j_read
#print axioms InitECandidate.Solver.MutableTable.Delete.scan_advance
#print axioms InitECandidate.Solver.MutableTable.Delete.increment_j_execute
#print axioms InitECandidate.Solver.MutableTable.Delete.empty_test_read
