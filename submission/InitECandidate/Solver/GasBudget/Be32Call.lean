import InitECandidate.Solver.GasBudget.Be32Stores
import InitECandidate.Solver.Input.BinaryCallData
import InitECandidate.Solver.Input.IgnoredCallData

namespace InitECandidate.Solver.GasBudget.Be32Stores
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "st_be32") = some ([(ofString "p", .one), (ofString "v", .one)], MemoryWriter.Kind.be32.body, .one) := by
  simpa only [MemoryWriter.Kind.name, MemoryWriter.Kind.signature, MemoryWriter.Kind.original, Guest.guestFn_st_be32,
    MemoryWriter.Kind.body, paramToHOL, shapeToHOL, List.map_cons, List.map_nil]
    using MemoryWriter.original_code .be32 code installed

theorem call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer value : BitVec 64) (arguments : List (ExpHOL 64))
    (installed : Input.OriginalCode.Installed source.code)
    (argsRead : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments = some [.val (.word pointer), .val (.word value)])
    (mapped : ∀ clause ∈ clauses, source.memaddrs (panByteAlignHOL (width := 64) (pointer + BitVec.ofNat 64 clause.1)))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "st_be32") arguments) = (none, post)) :
    1 ≤ source.clock ∧ post = {source with memory := written source.memory source.be pointer value clauses, clock := source.clock - 1} := by
  obtain ⟨positive, values, actual, callee, shape, target, returned, args, called, bodyRun, checked, postEq, fields⟩ :=
    Input.CallNormal.ignored_data source post (ofString "st_be32") arguments normal
  have valuesEq := Option.some.inj (args.symm.trans argsRead)
  rw [valuesEq] at called
  obtain ⟨bodyEq, shapeEq, pointerCell, valueCell⟩ := Input.CallNormal.binary_lookup_known source.code.lookup (ofString "st_be32")
    (ofString "p") (ofString "v") .one .one MemoryWriter.Kind.be32.body .one (.val (.word pointer)) (.val (.word value))
    actual callee shape (by decide) (original_code source.code installed) called
  rw [bodyEq, original_body] at bodyRun
  have actualRun := execute (callEntryStateHOLFinite source callee) pointer value clauses pointerCell valueCell
    (by intro clause member; simp only [clauses, List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl | rfl <;> decide) mapped
  have targetEq : target = emptyLocalsHOLFinite {callEntryStateHOLFinite source callee with memory := written source.memory source.be pointer value clauses} :=
    congrArg Prod.snd (bodyRun.symm.trans actualRun)
  refine ⟨positive, ?_⟩
  rw [postEq, targetEq]
  rfl

end InitECandidate.Solver.GasBudget.Be32Stores

#print axioms InitECandidate.Solver.GasBudget.Be32Stores.original_code
#print axioms InitECandidate.Solver.GasBudget.Be32Stores.call_normal
