import InitECandidate.Solver.MutableTable.DeleteScanReads

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem ScanLocals.of_locals (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (hole slot : Nat)
    (locals : ScanLocals source kind plan hole slot) (same : source.locals = target.locals) : ScanLocals target kind plan hole slot := by
  exact ⟨Move.Locals.of_locals source target kind plan hole slot locals.toLocals same, same ▸ locals.cap, same ▸ locals.used⟩

theorem ScanLocals.advance (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (hole slot next : Nat)
    (locals : ScanLocals source kind plan hole slot) : ScanLocals (WitnessRadix.QueryBranch.bind source "j" (BitVec.ofNat 64 next)) kind plan hole next := by
  refine ⟨?_, (bind_lookup_other _ "j" "cap" _ (by decide)).trans locals.cap, (bind_lookup_other _ "j" "used" _ (by decide)).trans locals.used⟩
  exact ⟨(bind_lookup_other _ "j" "keys" _ (by decide)).trans locals.keys,
    (bind_lookup_other _ "j" "vals" _ (by decide)).trans locals.values,
    (bind_lookup_other _ "j" "order" _ (by decide)).trans locals.order,
    (bind_lookup_other _ "j" "order_pos" _ (by decide)).trans locals.position,
    (bind_lookup_other _ "j" "klen" _ (by decide)).trans locals.length,
    (bind_lookup_other _ "j" "stride" _ (by decide)).trans locals.stride,
    (bind_lookup_other _ "j" "i" _ (by decide)).trans locals.hole,
    bind_lookup_same _ _ _⟩

theorem ScanLocals.after_hash (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (hole slot nextHole : Nat)
    (locals : ScanLocals source kind plan hole slot) (memory : WordWrites.Memory) (paid : Nat) :
    ScanLocals (WitnessRadix.QueryBranch.bind {source with memory := memory, clock := source.clock - paid} "i" (BitVec.ofNat 64 nextHole)) kind plan nextHole slot := by
  refine ⟨?_, (bind_lookup_other _ "i" "cap" _ (by decide)).trans locals.cap, (bind_lookup_other _ "i" "used" _ (by decide)).trans locals.used⟩
  exact ⟨(bind_lookup_other _ "i" "keys" _ (by decide)).trans locals.keys,
    (bind_lookup_other _ "i" "vals" _ (by decide)).trans locals.values,
    (bind_lookup_other _ "i" "order" _ (by decide)).trans locals.order,
    (bind_lookup_other _ "i" "order_pos" _ (by decide)).trans locals.position,
    (bind_lookup_other _ "i" "klen" _ (by decide)).trans locals.length,
    (bind_lookup_other _ "i" "stride" _ (by decide)).trans locals.stride,
    bind_lookup_same _ _ _,
    (bind_lookup_other _ "i" "j" _ (by decide)).trans locals.slot⟩

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.ScanLocals.of_locals
#print axioms InitECandidate.Solver.MutableTable.Delete.ScanLocals.advance
#print axioms InitECandidate.Solver.MutableTable.Delete.ScanLocals.after_hash
