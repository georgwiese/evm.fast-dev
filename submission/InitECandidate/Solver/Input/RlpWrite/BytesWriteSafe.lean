import InitECandidate.Solver.Input.RlpWrite.BytesWriteBuilt

namespace InitECandidate.Solver.Input.RlpWrite.BytesWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual header/copy suffix for arbitrary safe physical lengths. Only
64-bit arithmetic and current mappings are needed, with no input-size cap. -/
theorem general_safe_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst src : BitVec 64) (length : Nat) (fits : length+32<2^64)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (s : source.locals.lookup (ofString "src")=some (.val (.word src)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (headerCode : source.code.lookup (ofString "rlp_write_header")=some (HeaderWrite.formals,HeaderWrite.body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (RlpLength.Be.formals,RlpLength.Be.body,.one))
    (putCode : source.code.lookup (ofString "rlp_put_be")=some (PutBe.formals,PutBe.body,.one))
    (copyCode : source.code.lookup (ofString "memcpy")=some (WitnessRadix.CopyGeneral.formals,WitnessRadix.Copy32.body,.one))
    (mapped : ∀ index<9,source.memaddrs (panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index)))
    (copyMapped : ∀ header,1≤header→header≤9→WitnessRadix.CopyContext.Mapped source src (dst+BitVec.ofNat 64 header) length)
    (enough : length+20≤source.clock) :
    ∃ target encoded paid,length+1≤encoded ∧ encoded≤length+9 ∧ paid≤length+20 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      evaluateHOLFiniteState source generalTail=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=target.memory,clock:=source.clock-paid} ∧
      (∀ query,Away dst query (length+9)→target.memory query=source.memory query) := by
  classical
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "dst",.const 128#64,localVar "n"]=
      some [.val (.word dst),.val (.word 128#64),.val (.word (BitVec.ofNat 64 length))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,d,n]
  obtain ⟨memory,header,headerPaid,headerLow,headerHigh,headerBound,headerRun,headerFrame⟩:=HeaderWrite.call_execute source dst 128#64 (BitVec.ofNat 64 length)
    "h" [localVar "dst",.const 128#64,localVar "n"] generalAfterHeader args headerCode beCode putCode mapped (by omega)
  let entry:=bind {source with memory:=memory,clock:=source.clock-1-headerPaid} "h" (BitVec.ofNat 64 header)
  have dEntry : entry.locals.lookup (ofString "dst")=some (.val (.word dst)):=
    (bind_lookup_other _ "h" "dst" _ (by decide)).trans d
  have sEntry : entry.locals.lookup (ofString "src")=some (.val (.word src)):=
    (bind_lookup_other _ "h" "src" _ (by decide)).trans s
  have nEntry : entry.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))):=
    (bind_lookup_other _ "h" "n" _ (by decide)).trans n
  have hEntry : entry.locals.lookup (ofString "h")=some (.val (.word (BitVec.ofNat 64 header))):=bind_lookup_same _ _ _
  have copyArgs : evalListHOLFinite entry (h:=fun address=>Classical.propDecidable (entry.memaddrs address))
      [.op .add [localVar "dst",localVar "h"],localVar "src",localVar "n"]=
      some (WitnessRadix.CopyGeneral.values (dst+BitVec.ofNat 64 header) src length) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,dEntry,sEntry,nEntry,hEntry,WitnessRadix.CopyGeneral.values,
      valueIsWord,valueWord,wordOpHOL,wordOp]
  have copyCost:=WitnessRadix.CopyGeneral.cost_le src (dst+BitVec.ofNat 64 header) length
  have mappedEntry : WitnessRadix.CopyContext.Mapped entry src (dst+BitVec.ofNat 64 header) length :=
    WitnessRadix.CopyContext.Mapped.of_domain source entry _ _ _ rfl (copyMapped header headerLow headerHigh)
  have copyRun:=WitnessRadix.CopyGeneral.call_execute entry _ src (dst+BitVec.ofNat 64 header) length copyArgs copyCode mappedEntry (by omega)
    (by change WitnessRadix.CopyGeneral.cost src (dst+BitVec.ofNat 64 header) length+1≤source.clock-1-headerPaid; omega)
  let copied:=WitnessRadix.CopyGeneral.callState entry src (dst+BitVec.ofNat 64 header) length
  have hCopied : copied.locals.lookup (ofString "h")=some (.val (.word (BitVec.ofNat 64 header))):=hEntry
  have nCopied : copied.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))):=nEntry
  have returnRun : evaluateHOLFiniteState copied (.return (.op .add [localVar "h",localVar "n"]))=
      (some (.returned (.val (.word (BitVec.ofNat 64 (length+header))))),emptyLocalsHOLFinite copied) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,localVar,hCopied,nCopied,valueIsWord,valueWord,
      wordOpHOL,wordOp,←BitVec.ofNat_add,Nat.add_comm,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have afterRun : evaluateHOLFiniteState entry generalAfterHeader=(some (.returned (.val (.word (BitVec.ofNat 64 (length+header))))),emptyLocalsHOLFinite copied) := by
    rw [generalAfterHeader,WitnessRadix.StateSteps.next_sequence entry copied _ _ copyRun (by change entry.clock-(WitnessRadix.CopyGeneral.cost src (dst+BitVec.ofNat 64 header) length+1)≤entry.clock; omega)]
    exact returnRun
  let target:=restore source "h" (emptyLocalsHOLFinite copied)
  let paid:=headerPaid+WitnessRadix.CopyGeneral.cost src (dst+BitVec.ofNat 64 header) length+2
  refine ⟨target,length+header,paid,by omega,by omega,by dsimp [paid]; omega,?_,?_,?_,?_⟩
  · rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  · rw [generalTail,headerRun,afterRun]
  · have subtract : source.clock-1-headerPaid-(WitnessRadix.CopyGeneral.cost src (dst+BitVec.ofNat 64 header) length+1)=source.clock-paid := by dsimp [paid]; omega
    change emptyLocalsHOLFinite {source with memory:=copied.memory,clock:=source.clock-1-headerPaid-(WitnessRadix.CopyGeneral.cost src (dst+BitVec.ofNat 64 header) length+1)}=
      emptyLocalsHOLFinite {source with memory:=copied.memory,clock:=source.clock-paid}
    rw [subtract]
  · intro query away
    have shiftedAddress (offset : Nat) : dst+BitVec.ofNat 64 header+BitVec.ofNat 64 offset=dst+BitVec.ofNat 64 (header+offset) := by
      rw [BitVec.ofNat_add,BitVec.add_assoc]
    have copiedFrame:=WitnessRadix.CopyGeneral.call_memory_away entry src (dst+BitVec.ofNat 64 header) query length (by
      intro offset inside
      simp only [WitnessRadix.byteAddress,shiftedAddress]
      exact away (header+offset) (by omega))
    have firstFrame:=headerFrame query (by intro index inside; exact (away index (by omega)).2)
    exact copiedFrame.trans firstFrame

/-- Whole unchanged byte-string writer, including its true single-byte
special case and arbitrary-alignment copy, for full stored compact paths. -/
theorem safe_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst src : BitVec 64) (length : Nat) (byte : UInt8)
    (fits : length+32<2^64)
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
  · obtain ⟨target,encoded,paid,lower,upper,bound,number,run,frame,memory⟩:=general_safe_execute source dst src length fits d s n
      headerCode beCode putCode copyCode mapped copyMapped enough
    refine ⟨target,encoded,paid,by omega,by omega,upper,bound,number,?_,frame,memory⟩
    rw [body_shape,WitnessRadix.StateSteps.next_sequence source source _ _ normal (Nat.le_refl _)]
    exact run

end InitECandidate.Solver.Input.RlpWrite.BytesWrite

#print axioms InitECandidate.Solver.Input.RlpWrite.BytesWrite.general_safe_execute
#print axioms InitECandidate.Solver.Input.RlpWrite.BytesWrite.safe_execute
