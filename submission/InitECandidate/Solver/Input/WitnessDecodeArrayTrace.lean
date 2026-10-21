import InitECandidate.Solver.Input.WitnessDecodeArrayEntry
import InitECandidate.Solver.Input.WitnessDecodeSliceTrace

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The unchanged decode body reaches its actual two-versus-seventeen-item
decision with real arr/sl bindings, bounded input spans and preserved physical
databases. All preceding failure outcomes retain the same prefix allowance. -/
theorem decode_array_trace (input : Guest.InputBlob)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (db pointer length cursor limit : BitVec 64)
    (boundary : RootBoundary input source)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (arena : Rlp.Validation.Arena source cursor limit)
    (before : pointer.toNat+length.toNat≤db.toNat) (small : length.toNat≤1024)
    (inputAbove : 2713731432≤pointer.toNat) (below : cursor.toNat≤2713717616)
    (installed : OriginalCode.Installed source.code) (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (Mpt.WitnessStep.body .decode)=(outcome,post)) :
    source.clock-post.clock≤131*length.toNat+79 ∨
      ∃ origin current header payload heap count items inner,
        DecodeSliceEntry input origin (bind current "arr" heap) db pointer length heap cursor limit header payload count items ∧
        Rlp.Validation.Above source origin cursor.toNat ∧
        (∀ key,origin.globals.lookup key=source.globals.lookup key) ∧
        current.clock≤source.clock ∧ source.clock-current.clock≤131*length.toNat+79 ∧
        evaluateHOLFiniteState (bind current "arr" heap) Mpt.WitnessDecode.afterArray=(outcome,inner) ∧
        post=restore source "it" (restore (Mpt.WitnessStep.tupleEntry source) "e" (restore origin "sl" (restore current "arr" inner))) := by
  rcases decode_slices_trace input source post db pointer length cursor limit boundary dbCell pointerCell lengthCell arena before small inputAbove below installed outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨origin,header,payload,heap,count,items,current,middle,entry,above,globals,forward,price,continued,endpoint⟩:=reached
    obtain ⟨inner,arrayRun,restored⟩:=entry.array_trace input origin current middle db pointer length heap cursor limit header payload count items outcome continued
    exact Or.inr ⟨origin,current,header,payload,heap,count,items,inner,entry.bind_array input origin current db pointer length heap cursor limit header payload count items,
      above,globals,forward,price,arrayRun,by rw [endpoint,restored]⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.decode_array_trace
