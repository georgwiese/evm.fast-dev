import InitECandidate.Solver.WitnessRadix.Graph
import InitECandidate.Solver.MutableTable.WitnessBuildSetStep

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def recordCell (plan : AllocatedLayout.Plan) (index offset : Nat) : BitVec 64:=
  BitVec.ofNat 64 (plan.records+16*index+offset)

theorem record_address (plan : AllocatedLayout.Plan) (index offset : Nat) :
    recordAddress plan index+BitVec.ofNat 64 offset=recordCell plan index offset := by
  simp only [recordAddress,recordCell,BitVec.ofNat_add,BitVec.ofNat_mul]
  ac_rfl

theorem record_backing (plan : AllocatedLayout.Plan) (index offset : Nat) :
    recordCell plan index offset=BackingLayout.cell (AllocatedLayout.layout plan) .records (16*index+offset) := by
  simp only [recordCell,BackingLayout.cell,BackingLayout.base,AllocatedLayout.layout,byteAddress,BitVec.ofNat_add]
  rw [BitVec.add_assoc]

theorem record_number (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) (index offset : Nat)
    (inside : index<plan.count) (offsetInside : offset<16) :
    (recordCell plan index offset).toNat=plan.records+16*index+offset := by
  have fits:=ready.fits
  have before:=ready.recordsBefore
  rw [recordCell,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]

theorem record_earlier (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) (index offset : Nat)
    (inside : index<plan.count) (offsetInside : offset<16) : (recordCell plan index offset).toNat<plan.table := by
  rw [record_number plan ready index offset inside offsetInside]
  have before:=ready.recordsBefore
  omega

structure Records (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan) (slices : Nat→Graph.Slice) : Prop where
  pointers : ∀ i<plan.count,source.memory (recordCell plan i 0)=.word (slices i).1
  lengths : ∀ i<plan.count,source.memory (recordCell plan i 8)=.word (slices i).2

theorem Records.of_earlier (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (slices : Nat→Graph.Slice)
    (frame : ∀ query,query.toNat<plan.table→target.memory query=source.memory query) (records : Records source plan slices) :
    Records target plan slices := by
  constructor
  · intro i inside
    exact (frame _ (record_earlier plan ready i 0 inside (by decide))).trans (records.pointers i inside)
  · intro i inside
    exact (frame _ (record_earlier plan ready i 8 inside (by decide))).trans (records.lengths i inside)

theorem Records.after_hash (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (slices : Nat→Graph.Slice)
    (stp pointer scratch out : BitVec 64) (length : Nat) (buffers : Keccak256.Buffers stp pointer scratch out length)
    (before : stp.toNat+200≤plan.records ∧ scratch.toNat+136≤plan.records ∧ out.toNat+32≤plan.records)
    (frame : ∀ query,Keccak256.Protected stp scratch out query→target.memory query=source.memory query)
    (records : Records source plan slices) : Records target plan slices := by
  have kept (i offset : Nat) (inside : i<plan.count) (offsetInside : offset<16) :
      target.memory (recordCell plan i offset)=source.memory (recordCell plan i offset) := by
    apply frame
    have number:=record_number plan ready i offset inside offsetInside
    apply AllocatedBytes.protected_above stp pointer scratch out _ length buffers <;> rw [number] <;> omega
  exact ⟨by intro i inside;exact (kept i 0 inside (by decide)).trans (records.pointers i inside),
    by intro i inside;exact (kept i 8 inside (by decide)).trans (records.lengths i inside)⟩

/-- Actual slice-pointer/length loads and scratch-global read supply the
literal original builder's keccak arguments, from concrete record words. -/
theorem hash_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs=InitE.ordinaryDomain)
    (slices : Nat→Graph.Slice) (records : Records source plan slices) (index : Nat) (inside : index<plan.count)
    (locals : Locals source plan index) (scratch : BitVec 64)
    (global : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word scratch))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) Constructor.hashArguments=
      some (Keccak256.values (slices index).1 scratch (slices index).2.toNat) := by
  classical
  have first : recordAddress plan index=recordCell plan index 0:=by simpa only [BitVec.add_zero] using record_address plan index 0
  have second:=record_address plan index 8
  have mapped (offset : Nat) (high : offset+8≤16) (aligned : offset%8=0) : source.memaddrs (recordCell plan index offset) := by
    rw [record_backing]
    exact AllocatedLayout.mapped source plan ready domain .records (16*index+offset) (by omega) (by change 16*index+offset+8≤16*plan.count;omega)
  have pointerMapped : source.memaddrs (recordAddress plan index):=by rw [first];exact mapped 0 (by decide) (by decide)
  have lengthMapped : source.memaddrs (recordAddress plan index+8#64):=by rw [second];exact mapped 8 (by decide) (by decide)
  have pointerWord : source.memory (recordAddress plan index)=.word (slices index).1:=by rw [first];exact records.pointers index inside
  have lengthWord : source.memory (recordAddress plan index+8#64)=.word (slices index).2:=by rw [second];exact records.lengths index inside
  simp only [recordAddress] at pointerMapped lengthMapped pointerWord lengthWord
  simp only [BitVec.add_assoc] at lengthMapped lengthWord
  simp [Constructor.hashArguments,Constructor.scaled,Constructor.scratch,localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,
    locals.records,locals.index,global,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,memLoadHOLExact,isWfShapeExactHOL,
    pointerMapped,lengthMapped,pointerWord,lengthWord,BitVec.add_assoc,Keccak256.values]

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.record_earlier
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Records.after_hash
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.hash_arguments
