import InitECandidate.Solver.Input.RlpWrite.WordWriteCall
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

namespace InitECandidate.Solver.Input.RlpWrite.WordWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every actual outcome costs at most eighteen source ticks. In particular,
the estimate does not require the incoming clock to fund that allowance. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst w : BitVec 64)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (value : source.locals.lookup (ofString "w")=some (.val (.word w)))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (RlpLength.Be.formals,RlpLength.Be.body,.one))
    (putCode : source.code.lookup (ofString "rlp_put_be")=some (PutBe.formals,PutBe.body,.one))
    (mapped : ∀ index<9,source.memaddrs (panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤18 := by
  by_cases enough : 18≤source.clock
  · obtain ⟨target,encoded,paid,lower,upper,bound,run,frame,memory⟩:=execute source dst w d value beCode putCode mapped enough
    have clock:=congrArg PanSemStateFiniteExact.clock frame
    change target.clock=source.clock-paid at clock
    rw [run]
    change source.clock-target.clock≤18
    omega
  · omega

/-- A genuine normal return determines a one-to-nine-byte key and its
memory frame even when the caller supplied less than the conservative budget. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst w : BitVec 64)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (value : source.locals.lookup (ofString "w")=some (.val (.word w)))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (RlpLength.Be.formals,RlpLength.Be.body,.one))
    (putCode : source.code.lookup (ofString "rlp_put_be")=some (PutBe.formals,PutBe.body,.one))
    (mapped : ∀ index<9,source.memaddrs (panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),target)) :
    ∃ encoded,1≤encoded ∧ encoded≤9 ∧ returned=.val (.word (BitVec.ofNat 64 encoded)) ∧
      source.clock-target.clock≤18 ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=target.clock} ∧
      (∀ query,(∀ index<9,query≠panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))→target.memory query=source.memory query) := by
  let padded:={source with clock:=source.clock+18}
  obtain ⟨post,encoded,paid,lower,upper,bound,run,frame,memory⟩:=execute padded dst w d value beCode putCode mapped
    (by change 18≤source.clock+18; omega)
  have lifted:=panPropsEvaluateAddClockEq body source (some (.returned returned)) target 18
    ⟨normal,by intro impossible; cases impossible⟩
  have same:=lifted.symm.trans run
  have returnedEq:=congrArg Prod.fst same
  have postEq:=congrArg Prod.snd same
  change {target with clock:=target.clock+18}=post at postEq
  have cost:=body_cost source dst w d value beCode putCode mapped
  rw [normal] at cost
  rw [←postEq] at frame memory
  have restored:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with clock:=target.clock}) frame
  change emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=target.clock} at restored
  have valueEq : returned=.val (.word (BitVec.ofNat 64 encoded)):=by
    change (some (PanSemResultExact.returned returned) : Option (PanSemResultExact 64))=
      some (PanSemResultExact.returned (.val (.word (BitVec.ofNat 64 encoded)))) at returnedEq
    exact PanSemResultExact.returned.inj (Option.some.inj returnedEq)
  exact ⟨encoded,lower,upper,valueEq,cost,restored,memory⟩

end InitECandidate.Solver.Input.RlpWrite.WordWrite

#print axioms InitECandidate.Solver.Input.RlpWrite.WordWrite.body_cost
#print axioms InitECandidate.Solver.Input.RlpWrite.WordWrite.body_normal
