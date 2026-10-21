import InitECandidate.Solver.Mpt.StateInitBlockStepNormal

namespace InitECandidate.Solver.Mpt.StateInit.Block
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem program_cons (action : Action) (rest : List Action) (tail : Flapjack.Pancake.PanLang.ProgHOL 64) :
    program (action::rest) tail=program [action] (program rest tail):=by cases action <;> rfl

theorem cursor_cons (start : Nat) (action : Action) (rest : List Action) :
    cursor start (action::rest)=cursor (stepCursor start action) rest:=by cases action <;> rfl

/-- Compose every actual assigned constructor and mapped record store,
retaining all reached layouts and the true final suffix execution. -/
theorem prefix_normal (specs : List Action) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (block start : Nat) (tail : Flapjack.Pancake.PanLang.ProgHOL 64) (oldT : BitVec 64)
    (wellFormed : ∀ action∈specs,action.Valid) (recordValid : MemoryRegion.Valid ⟨block,80⟩)
    (lower : 2701131776≤start) (bounded : start≤33806089496) (aligned : start%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 start))))
    (bs : source.globals.lookup (ofString "bs")=some (.val (.word (MemoryRegion.pointer ⟨block,80⟩))))
    (t : source.locals.lookup (ofString "t")=some (.val (.word oldT)))
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (program specs tail)=(some (.returned returned),post)) :
    Layouts start specs ∧ price specs≤source.clock ∧ cursor start specs≤33806089496 ∧ cursor start specs%8=0 ∧
      evaluateHOLFiniteState (walk source block start specs) tail=(some (.returned returned),post) := by
  induction specs generalizing source start oldT with
  | nil=>exact ⟨True.intro,Nat.zero_le _,bounded,aligned,normal⟩
  | cons action rest ih=>
    rw [program_cons] at normal
    obtain ⟨layout,funded,nextBound,nextAligned,continued⟩:=step_normal action source post block start (program rest tail) oldT
      (wellFormed action List.mem_cons_self) recordValid lower bounded aligned domain heap bs t installed returned normal
    let next:=stepState source block start action
    have nextDomain : next.memaddrs=source.memaddrs:=by cases action <;> rfl
    have nextCode : next.code=source.code:=by cases action <;> rfl
    have grows : start≤stepCursor start action:=by cases action <;> dsimp only [stepCursor,NaturalLayout.freshEnd] <;> omega
    have nextLower : 2701131776≤stepCursor start action:=lower.trans grows
    have nextHeap:=step_heap source block start action heap
    have nextBs:=step_bs source block start action bs
    obtain ⟨nextT,nextTCell⟩:=step_t source block start action oldT t
    have nextInstalled : Input.OriginalCode.Installed next.code:=by rw [nextCode]; exact installed
    obtain ⟨restLayouts,restFunded,finalBound,finalAligned,tailRun⟩:=ih next (stepCursor start action) nextT
      (fun later member=>wellFormed later (List.mem_cons_of_mem _ member)) nextLower nextBound nextAligned (nextDomain.trans domain) nextHeap nextBs nextTCell nextInstalled continued
    have priceEq : price (action::rest)=stepPrice action+price rest:=by cases action <;> simp [price,stepPrice]
    have clockEq:=step_clock source block start action
    change price rest≤(stepState source block start action).clock at restFunded
    rw [clockEq] at restFunded
    refine ⟨⟨layout,restLayouts⟩,?_,?_,?_,tailRun⟩
    · rw [priceEq]; omega
    · rw [cursor_cons]; exact finalBound
    · rw [cursor_cons]; exact finalAligned

/-- Original322's entire seven-table/ancestor-field prefix reaches its
actual sk_buf suffix after exactly94source clocks, with70840fresh bytes.
These units omit straight-line target work. -/
theorem fields_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (block start : Nat) (oldT : BitVec 64) (recordValid : MemoryRegion.Valid ⟨block,80⟩)
    (lower : 2701131776≤start) (bounded : start≤33806089496) (aligned : start%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 start))))
    (bs : source.globals.lookup (ofString "bs")=some (.val (.word (MemoryRegion.pointer ⟨block,80⟩))))
    (t : source.locals.lookup (ofString "t")=some (.val (.word oldT)))
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterWorkspace=(some (.returned returned),post)) :
    Layouts start actions ∧ 94≤source.clock ∧ start+70840≤33806089496 ∧ (start+70840)%8=0 ∧
      (walk source block start actions).clock=source.clock-94 ∧
      evaluateHOLFiniteState (walk source block start actions) afterFields=(some (.returned returned),post) := by
  rw [shapes.2.2] at normal
  obtain ⟨layouts,funded,bound,endAligned,continued⟩:=prefix_normal actions source post block start afterFields oldT actions_valid recordValid
    lower bounded aligned domain heap bs t installed returned normal
  rw [price_all] at funded
  rw [cursor_all] at bound endAligned
  exact ⟨layouts,funded,bound,endAligned,by rw [walk_clock,price_all],continued⟩

end InitECandidate.Solver.Mpt.StateInit.Block

#print axioms InitECandidate.Solver.Mpt.StateInit.Block.program_cons
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.cursor_cons
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.prefix_normal
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.fields_normal
