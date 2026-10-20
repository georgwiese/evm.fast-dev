import InitECandidate.Solver.Input.MainParsedByteBudget
import InitECandidate.Solver.Input.TerminatingProgramPrefix

namespace InitECandidate.Solver.Input.Main.RequestHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch ProgramPrefix

def actions : List Action := [.allocate "root" (.const 32#64)]
def entered (source : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64) :=
  bind (PersistentAlloc.post {source with clock:=source.clock-1} root 32#64) "root" root

theorem root_shape : DecoderCall.continuation=program actions afterRoot := by rw [original_shape.1]; rfl

private theorem setup (source : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word root)))
    (room : root.toNat+32≤33806089496) (enough : 1≤source.clock) :
    Executes source actions (entered source root) (restore source "root") :=
  Executes.allocate (restoreRest:=id) root 32#64 rfl (PersistentAlloc.original_code source.code installed) heap room enough (Executes.done _)

/-- Main's real root allocation follows its decoded heap, with actual funding
from the observed non-timeout run. No future hashing return is assumed. -/
theorem root_prefix (input : Guest.InputBlob) (before copiedSource current post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (copied : InputCopied input before copiedSource) (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) current)
    (bounded : input.length%2^64≤Guest.maxInputBytes) (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState current DecoderCall.continuation=(result,post)) (notTimeout : result≠some .timeOut) :
    ∃ root : BitVec 64,current.globals.lookup (ofString "heap_ptr")=some (.val (.word root)) ∧ root.toNat%8=0 ∧
      root.toNat≤DecoderSetup.cursor input+600+4*(input.length%2^64) ∧ AllocatedBytes.Arena root 32 ∧ 1≤current.clock ∧
      ∃ final,evaluateHOLFiniteState (entered current root) afterRoot=(result,final) ∧ post=restore current "root" final := by
  obtain ⟨root,heap,aligned,after,bound,arena⟩ := parsed_heap_shared input _ current actual bounded
  have context := DecoderSetup.entered_context copiedSource input
  have callerCode : (DecoderSetup.entered copiedSource input).code=copiedSource.code := by have h := congrArg PanSemStateFiniteExact.code context; exact h
  have code : current.code=copiedSource.code := actual.code.trans callerCode
  have installed : OriginalCode.Installed current.code := code.symm ▸ copied.code
  have padded := setup {current with clock:=current.clock+1} root installed heap arena.upper (by change 1≤current.clock+1; omega)
  rw [root_shape] at run
  have paid := terminating_program_prefix current post (entered {current with clock:=current.clock+1} root) actions afterRoot (restore {current with clock:=current.clock+1} "root") 1 padded result run notTimeout
  have funded : 1≤current.clock := by change 1≤current.clock+1-1 at paid; omega
  have actualSetup := setup current root installed heap arena.upper funded
  rw [ProgramPrefix.execute actualSetup afterRoot] at run
  let final := (evaluateHOLFiniteState (entered current root) afterRoot).2
  have observed := congrArg Prod.fst run
  exact ⟨root,heap,aligned,bound,arena,funded,final,Prod.ext observed rfl,(congrArg Prod.snd run).symm⟩

/-- Exact current root/SI bindings, heap update and full readonly data frame. -/
theorem entered_fields (input : Guest.InputBlob) (caller source : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (actual : DecoderCall.DecoderReady input caller source) :
    (entered source root).locals.lookup (ofString "root")=some (.val (.word root)) ∧
    (entered source root).locals.lookup (ofString "si")=some (.val (.word (RequestPrefix.cursor input))) ∧
    (entered source root).memory=source.memory ∧ InitializerAllocations.context (entered source root)=InitializerAllocations.context source ∧
    (entered source root).globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded root 32#64))) ∧
    (entered source root).clock=source.clock-1 := by
  refine ⟨bind_lookup_same _ _ _,(bind_lookup_other _ "root" "si" _ (by decide)).trans actual.si,rfl,rfl,?_,rfl⟩
  change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded root 32#64)))).lookup (ofString "heap_ptr")=_
  simp [HolFiniteMapExact.lookup_update,FUPDATE]

end InitECandidate.Solver.Input.Main.RequestHash

#print axioms InitECandidate.Solver.Input.Main.RequestHash.root_shape
#print axioms InitECandidate.Solver.Input.Main.RequestHash.root_prefix
#print axioms InitECandidate.Solver.Input.Main.RequestHash.entered_fields
