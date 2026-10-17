import InitECandidate.Solver.Input.HeaderEncoding.First
import InitECandidate.Solver.WitnessRadix.AllocationCall
import InitECandidate.Solver.WitnessRadix.AllocationExpected

namespace InitECandidate.Solver.Input.HeaderEncoding
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def post (source : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer : BitVec 64) (memory : Memory) (paid : Nat) :
    PanSemStateFiniteExact 64 Guest.HostMemory :=
  {source with globals:=source.globals.update (ofString "heap_ptr",.val (.word (cursor buffer))),memory:=memory,clock:=source.clock-paid}

/-- Complete literal encode_header, including allocation, both outer scopes,
all actual fields, optional fields, list header and pair return. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (header buffer : BitVec 64)
    (geometry : Geometry header buffer) (domain : source.memaddrs=InitE.ordinaryDomain)
    (headerLocal : source.locals.lookup (ofString "h")=some (.val (.word header)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word buffer)))
    (codes : Codes source) (tailCodes : TailCodes source)
    (allocCode : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one))
    (facts : ∀ field∈firstField::baseRest,FieldFacts source.memory header field)
    (optionalFacts : wordAt source.memory (address header 0)≠0#64→∀ field∈optionalFields,FieldFacts source.memory header field)
    (enough : 1345≤source.clock) :
    ∃ target start encoded paid,1≤encoded ∧ encoded≤916 ∧ paid≤1345 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      evaluateHOLFiniteState source body=(some (.returned (encodedPair start encoded)),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite (post source buffer target.memory paid) ∧
      OldMemory target.memory source.memory buffer := by
  classical
  have rounded : WitnessRadix.PersistentAlloc.rounded buffer 1024#64=cursor buffer := by
    have native:=WitnessRadix.PersistentAlloc.rounded_expected buffer 1024#64 (buffer.toNat+1024)
      (by have room:=geometry.room; change buffer.toNat+1024+7<2^64; omega)
      (by change buffer.toNat+1024≤buffer.toNat+1024; omega)
      (by change buffer.toNat+1024<buffer.toNat+1024+8; omega)
      (by rw [Nat.add_mod,geometry.bufferAligned])
    simpa [cursor,BitVec.ofNat_add] using native
  have allocation:=WitnessRadix.PersistentAlloc.call_execute source "buf" [.const 1024#64] afterBuffer buffer 1024#64
    (by rfl) allocCode heap (by change buffer.toNat+1024≤33806089496; have room:=geometry.room; omega) (by omega)
  let allocated:=bind (WitnessRadix.PersistentAlloc.post {source with clock:=source.clock-1} buffer 1024#64) "buf" buffer
  have bufA : allocated.locals.lookup (ofString "buf")=some (.val (.word buffer)):=bind_lookup_same _ _ _
  have pointerRead : eval allocated (.op .add [localVar "buf",.const 9#64])=some (.val (.word (address buffer 9))) := by
    simp [eval,localVar,evalHOLExact,evalListHOLExact,toExact,bufA,valueIsWord,valueWord,wordOpHOL,wordOp,address]
  let entered:=bind allocated "p" (address buffer 9)
  have bufE : entered.locals.lookup (ofString "buf")=some (.val (.word buffer)):=
    (bind_lookup_other _ "p" "buf" _ (by decide)).trans bufA
  have context : Context entered source.memory header buffer := by
    refine ⟨geometry,domain,by intro query before; rfl,?_,?_⟩
    · exact (bind_lookup_other _ "p" "h" _ (by decide)).trans ((bind_lookup_other _ "buf" "h" _ (by decide)).trans headerLocal)
    · change (source.globals.update (ofString "heap_ptr",.val (.word (WitnessRadix.PersistentAlloc.rounded buffer 1024#64)))).lookup (ofString "heap_ptr")=_
      rw [rounded]
      simp [HolFiniteMapExact.update,FUPDATE]
  obtain ⟨lastState,start,encoded,restPaid,positive,sizeBound,restBound,number,run,frame,memoryFrame⟩:=
    after_pointer_execute entered source.memory header buffer context (Codes.of_code source entered rfl codes)
      (TailCodes.of_code source entered rfl tailCodes) facts optionalFacts (bind_lookup_same _ _ _) bufE (by change 1344≤source.clock-1; omega)
  have pointerScope : evaluateHOLFiniteState allocated afterBuffer=
      (some (.returned (encodedPair start encoded)),restore allocated "p" lastState) :=
    ScalarScope.declare_execute allocated _ "p" _ _ afterPointer _ pointerRead run
  let target:=restore source "buf" (restore allocated "p" lastState)
  refine ⟨target,start,encoded,restPaid+1,positive,sizeBound,by omega,number,?_,?_,memoryFrame⟩
  · rw [body_shape,allocation,pointerScope]
  · change emptyLocalsHOLFinite lastState=emptyLocalsHOLFinite (post source buffer lastState.memory (restPaid+1))
    change emptyLocalsHOLFinite lastState=emptyLocalsHOLFinite
      {source with
        globals:=source.globals.update (ofString "heap_ptr",.val (.word (WitnessRadix.PersistentAlloc.rounded buffer 1024#64)))
        memory:=lastState.memory
        clock:=source.clock-1-restPaid} at frame
    have subtract : source.clock-1-restPaid=source.clock-(restPaid+1) := by omega
    simpa only [post,rounded,subtract] using frame

end InitECandidate.Solver.Input.HeaderEncoding

#print axioms InitECandidate.Solver.Input.HeaderEncoding.execute
