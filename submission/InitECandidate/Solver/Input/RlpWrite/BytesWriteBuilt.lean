import InitECandidate.Solver.Input.RlpWrite.BytesWriteProgram

namespace InitECandidate.Solver.Input.RlpWrite.BytesWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Whole literal RLP byte-string encoder. The single-byte special case,
actual header stores, arbitrary-alignment copy, return and scopes are included. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst src : BitVec 64) (length : Nat) (byte : UInt8)
    (small : length≤134217712)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (s : source.locals.lookup (ofString "src")=some (.val (.word src)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (loaded : length=1→ @panMemLoadByteHOL 64 _ source.memory source.memaddrs (fun address=>Classical.propDecidable (source.memaddrs address)) source.be src=some byte)
    (headerCode : source.code.lookup (ofString "rlp_write_header")=some (HeaderWrite.formals,HeaderWrite.body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (RlpLength.Be.formals,RlpLength.Be.body,.one))
    (putCode : source.code.lookup (ofString "rlp_put_be")=some (PutBe.formals,PutBe.body,.one))
    (copyCode : source.code.lookup (ofString "memcpy")=some (WitnessRadix.CopyGeneral.formals,WitnessRadix.Copy32.body,.one))
    (mapped : ∀ index<9,source.memaddrs (panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index)))
    (copyMapped : ∀ header,1≤header→header≤9→WitnessRadix.CopyContext.Mapped source src (dst+BitVec.ofNat 64 header) length)
    (enough : length+20≤source.clock) :
    ∃ target encoded paid,length≤encoded ∧ 1≤encoded ∧ encoded≤length+9 ∧ paid≤length+20 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-paid} ∧
      (∀ query,Away dst query (length+9)→target.memory query=source.memory query) := by
  classical
  have casesOfGuard :
      (∃ target,length=1 ∧ evaluateHOLFiniteState source firstGuard=(some (.returned (.val (.word 1#64))),target) ∧
        emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory} ∧
        (∀ query,query≠panByteAlignHOL (width:=64) dst→target.memory query=source.memory query)) ∨
      evaluateHOLFiniteState source firstGuard=(none,source) := by
    by_cases one : length=1
    · have nOne : source.locals.lookup (ofString "n")=some (.val (.word 1#64)) := by simpa only [one] using n
      have mapZero : source.memaddrs (panByteAlignHOL (width:=64) dst) := by simpa using mapped 0 (by decide)
      obtain ⟨target,guardRun,frame,memory⟩:=first_guard_one source dst src byte d s nOne (loaded one) mapZero
      by_cases short : byte.toNat<128
      · exact Or.inl ⟨target,one,by simpa only [if_pos short] using guardRun,frame,memory⟩
      · exact Or.inr (by simpa only [if_neg short] using guardRun)
    · have number : (BitVec.ofNat 64 length).toNat=length := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
      have wordNotOne : BitVec.ofNat 64 length≠1#64 := by
        intro equal
        have native:=congrArg BitVec.toNat equal
        rw [number] at native
        exact one native
      have read : eval source oneTest=some (.val (.word 0#64)) := by
        simp [eval,oneTest,localVar,evalHOLExact,toExact,n,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,wordNotOne]
      simp only [eval] at read
      right
      rw [firstGuard,evaluateHOLFiniteState_ite,read]
      simp
  rcases casesOfGuard with short|normal
  · obtain ⟨target,one,guardRun,frame,memory⟩:=short
    have clock:=congrArg PanSemStateFiniteExact.clock frame
    change target.clock=source.clock at clock
    refine ⟨target,1,0,by omega,by decide,by omega,by omega,rfl,?_,by simpa using frame,?_⟩
    · rw [body_shape]
      exact WitnessRadix.StateSteps.stopped_sequence source target _ _ (.returned (.val (.word 1#64))) guardRun (by omega)
    · intro query away
      exact memory query (by simpa using (away 0 (by omega)).2)
  · obtain ⟨target,encoded,paid,lower,upper,bound,number,run,frame,memory⟩:=general_execute source dst src length small d s n
      headerCode beCode putCode copyCode mapped copyMapped enough
    refine ⟨target,encoded,paid,by omega,by omega,upper,bound,number,?_,frame,memory⟩
    rw [body_shape,WitnessRadix.StateSteps.next_sequence source source _ _ normal (Nat.le_refl _)]
    exact run

end InitECandidate.Solver.Input.RlpWrite.BytesWrite

#print axioms InitECandidate.Solver.Input.RlpWrite.BytesWrite.execute
