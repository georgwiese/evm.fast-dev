import InitECandidate.Solver.Mpt.NodeRefLenProgram
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.WitnessRadix.BindingLookup

namespace InitECandidate.Solver.Mpt.NodeRefLen
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual unsigned short references return their cached length; longer
references return the literal33-byte hash reference. -/
theorem length_tail_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : BitVec 64)
    (cell : source.locals.lookup (ofString "rl")=some (.val (.word length))) :
    evaluateHOLFiniteState source lengthTail=(some (.returned (.val (.word (if length.toNat<32 then length else 33#64)))),emptyLocalsHOLFinite source) := by
  by_cases short : length.toNat<32 <;>
    simp [lengthTail,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_return,evaluateHOLFiniteState_skip,
      evalHOLExact,toExact,localVar,cell,short,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,shapeOfHOLExact,sizeOfShapeWithContextHOL]

def referenceWord (child tag length : BitVec 64) : BitVec 64:=
  if child=0#64 then 1#64 else if tag=0#64 then 33#64 else if length.toNat<32 then length else 33#64

theorem reference_bound (child tag length : BitVec 64) : (referenceWord child tag length).toNat≤33 := by
  unfold referenceWord
  split
  · decide
  · split
    · decide
    · split
      · omega
      · decide

/-- The real helper returns its exact null/hash/short/long reference size.
Its failure guard derives the populated-cache condition on normal return. -/
theorem body_normal_exact (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (child tag cached length : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (header : child≠0#64→source.memaddrs child ∧ source.memory child=.word tag)
    (cache : child≠0#64→tag≠0#64→source.memaddrs (child+8#64) ∧ source.memory (child+8#64)=.word cached)
    (size : child≠0#64→tag≠0#64→cached≠0#64→source.memaddrs (child+16#64) ∧ source.memory (child+16#64)=.word length)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    value=.val (.word (referenceWord child tag length)) ∧
      (child≠0#64→tag≠0#64→cached≠0#64) ∧ Input.LocalEffects.erase target=Input.LocalEffects.erase source := by
  have framed:=readonly source.code installed source rfl
  rw [normal] at framed
  by_cases childZero : child=0#64
  · have actual : evaluateHOLFiniteState source body=(some (.returned (.val (.word 1#64))),emptyLocalsHOLFinite source):=by
      simp [body_shape,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_return,evalHOLExact,toExact,localVar,childCell,childZero,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL,shapeOfHOLExact,sizeOfShapeWithContextHOL]
    have equal : value=.val (.word 1#64):=PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst (normal.symm.trans actual)))
    exact ⟨by simpa only [referenceWord,if_pos childZero] using equal,(by intro active; exact (active childZero).elim),framed⟩
  · obtain ⟨mapped,stored⟩:=header childZero
    by_cases tagZero : tag=0#64
    · have actual : evaluateHOLFiniteState source body=(some (.returned (.val (.word 33#64))),emptyLocalsHOLFinite source):=by
        simp [body_shape,readAt,NodeNeedsRlp.readAt,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_return,evaluateHOLFiniteState_skip,
          evalHOLExact,evalListHOLExact,toExact,localVar,childCell,childZero,tagZero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
          valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,mapped,stored,shapeOfHOLExact,sizeOfShapeWithContextHOL]
      have equal : value=.val (.word 33#64):=PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst (normal.symm.trans actual)))
      exact ⟨by simpa only [referenceWord,if_neg childZero,if_pos tagZero] using equal,(by intro _ active; exact (active tagZero).elim),framed⟩
    · obtain ⟨cacheMapped,cacheStored⟩:=cache childZero tagZero
      have selected : evaluateHOLFiniteState source body=evaluateHOLFiniteState source checkedTail:=by
        simp [body_shape,readAt,NodeNeedsRlp.readAt,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,
          evalHOLExact,evalListHOLExact,toExact,localVar,childCell,childZero,tagZero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
          valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,mapped,stored]
      have rest:=selected.symm.trans normal
      change evaluateHOLFiniteState source (.seq cacheGuard afterCache)=(some (.returned value),target) at rest
      obtain ⟨guardRun,continued⟩:=Fail.guard_return source target cacheTest [.const 13#64] afterCache value installed rest
      have cachedActive : cached≠0#64:=by
        intro zero
        have taken : evaluateHOLFiniteState source cacheGuard=evaluateHOLFiniteState source (.call (some (none,none)) (ofString "mpt_fail") [.const 13#64]):=by
          simp [cacheGuard,cacheTest,readAt,NodeNeedsRlp.readAt,evaluateHOLFiniteState_ite,evalHOLExact,evalListHOLExact,toExact,localVar,childCell,zero,
            Flapjack.Compiler.Encoders.Asm.wordCmpHOL,valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,cacheMapped,cacheStored]
        exact Fail.call_not_normal source source installed _ (taken.symm.trans guardRun)
      obtain ⟨sizeMapped,sizeStored⟩:=size childZero tagZero cachedActive
      have read : eval source (readAt 16)=some (.val (.word length)):=by
        simp [eval,readAt,NodeNeedsRlp.readAt,evalHOLExact,evalListHOLExact,toExact,localVar,childCell,valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,sizeMapped,sizeStored]
      obtain ⟨inner,tailRun,_endpoint⟩:=Input.declaration_return_word source target "rl" (readAt 16) length lengthTail value read continued
      have actual:=length_tail_execute (bind source "rl" length) length (bind_lookup_same _ _ _)
      have answer : value=.val (.word (if length.toNat<32 then length else 33#64)):=PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst (tailRun.symm.trans actual)))
      exact ⟨by simpa only [referenceWord,if_neg childZero,if_neg tagZero] using answer,(by intros; exact cachedActive),framed⟩

theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (child tag cached length : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (header : child≠0#64→source.memaddrs child ∧ source.memory child=.word tag)
    (cache : child≠0#64→tag≠0#64→source.memaddrs (child+8#64) ∧ source.memory (child+8#64)=.word cached)
    (size : child≠0#64→tag≠0#64→cached≠0#64→source.memaddrs (child+16#64) ∧ source.memory (child+16#64)=.word length)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ result : BitVec 64,value=.val (.word result) ∧ result.toNat≤33 ∧
      (child≠0#64→tag≠0#64→cached≠0#64) ∧ Input.LocalEffects.erase target=Input.LocalEffects.erase source := by
  obtain ⟨answer,populated,frame⟩:=body_normal_exact source target child tag cached length installed childCell header cache size value normal
  exact ⟨referenceWord child tag length,answer,reference_bound child tag length,populated,frame⟩

end InitECandidate.Solver.Mpt.NodeRefLen

#print axioms InitECandidate.Solver.Mpt.NodeRefLen.length_tail_execute
#print axioms InitECandidate.Solver.Mpt.NodeRefLen.body_normal
#print axioms InitECandidate.Solver.Mpt.NodeRefLen.body_normal_exact
#print axioms InitECandidate.Solver.Mpt.NodeRefLen.reference_bound
