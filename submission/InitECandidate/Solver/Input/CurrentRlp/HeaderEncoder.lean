import InitECandidate.Solver.Input.CurrentRlp.HeaderFirst
import InitECandidate.Solver.WitnessRadix.AllocationRoundedExpected

namespace InitECandidate.Solver.Input.CurrentRlp.HeaderEncoder
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch HeaderEncoding

abbrev body:=Code.body .header

theorem current_body : body=HeaderEncoding.body:=rfl

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "encode_header")=some (HeaderEncoding.formals,body,HeaderEncoding.returnShape) := by
  apply Code.installed_as code installed .header
  simp only [Code.entry,Code.declaration,Code.body,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
    Guest.Software.guestFn_encode_header,HeaderEncoding.formals,HeaderEncoding.returnShape,paramToHOL,shapeToHOL,List.map_cons,List.map_nil]

theorem rounded (header buffer : BitVec 64) (geometry : Geometry header buffer) : PersistentAlloc.rounded buffer 1024#64=cursor buffer := by
  have native:=PersistentAlloc.rounded_expected buffer 1024#64 (buffer.toNat+1024)
    (by have room:=geometry.room; change buffer.toNat+1024+7<2^64; omega)
    (by change buffer.toNat+1024≤buffer.toNat+1024; omega)
    (by change buffer.toNat+1024<buffer.toNat+1024+8; omega)
    (by rw [Nat.add_mod,geometry.bufferAligned])
  simpa [cursor,BitVec.ofNat_add] using native

def allocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer : BitVec 64) :=
  bind (PersistentAlloc.post {source with clock:=source.clock-1} buffer 1024#64) "buf" buffer

def entered (source : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer : BitVec 64) :=bind (allocated source buffer) "p" (address buffer 9)

def heapPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer : BitVec 64) :=
  {source with globals:=source.globals.update (ofString "heap_ptr",.val (.word (cursor buffer)))}

/-- A genuine returning allocation derives its own persistent room and
actual caller restoration. It is never assumed to return in the cost bound. -/
theorem allocation_result (source child : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer : BitVec 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (installed : OriginalCode.Installed source.code)
    (amount : callee.lookup (ofString "n")=some (.val (.word 1024#64)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word buffer))) (bounded : buffer.toNat≤2952790016)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) PersistentAlloc.body=(some (.returned value),child)) :
    value=.val (.word buffer) ∧ buffer.toNat+1024≤2952790016 ∧ CallNormal.continuationEntry source child "buf" value=allocated source buffer := by
  obtain ⟨answer,room,frame⟩:=PersistentAlloc.post_of_normal (callEntryStateHOLFinite source callee) child buffer 1024#64 amount heap bounded
    (Trap.original_code source.code installed) value normal
  refine ⟨answer,room,?_⟩
  rw [answer]
  have updated:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>
    setVarHOLFinite (ofString "buf") (.val (.word buffer)) {state with locals:=source.locals}) frame
  simpa only [CallNormal.continuationEntry,emptyLocalsHOLFinite,PersistentAlloc.post,callEntryStateHOLFinite,allocated,QueryBranch.bind] using updated

theorem entry_facts (source : PanSemStateFiniteExact 64 Guest.HostMemory) (header buffer : BitVec 64) (geometry : Geometry header buffer)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (h : source.locals.lookup (ofString "h")=some (.val (.word header))) :
    Context (entered source buffer) source.memory header buffer ∧
      (entered source buffer).locals.lookup (ofString "p")=some (.val (.word (address buffer 9))) ∧
      (entered source buffer).locals.lookup (ofString "buf")=some (.val (.word buffer)) ∧
      eval (allocated source buffer) (.op .add [localVar "buf",.const 9#64])=some (.val (.word (address buffer 9))) ∧
      MemoryMetadata.erase (entered source buffer)=MemoryMetadata.erase (heapPost source buffer) := by
  have bufA : (allocated source buffer).locals.lookup (ofString "buf")=some (.val (.word buffer)):=bind_lookup_same _ _ _
  have hA : (allocated source buffer).locals.lookup (ofString "h")=some (.val (.word header)):=
    (bind_lookup_other _ "buf" "h" _ (by decide)).trans h
  have context : Context (entered source buffer) source.memory header buffer:=⟨geometry,domain,by intro query before; rfl,
    (bind_lookup_other _ "p" "h" _ (by decide)).trans hA,by
      change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded buffer 1024#64)))).lookup (ofString "heap_ptr")=_
      rw [rounded header buffer geometry]
      simp [HolFiniteMapExact.update,FUPDATE]⟩
  refine ⟨context,bind_lookup_same _ _ _,(bind_lookup_other _ "p" "buf" _ (by decide)).trans bufA,?_,?_⟩
  · simp [eval,localVar,evalHOLExact,evalListHOLExact,toExact,bufA,valueIsWord,valueWord,wordOpHOL,wordOp,address]
  · change MemoryMetadata.erase {source with globals:=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded buffer 1024#64)))}=_
    rw [rounded header buffer geometry]
    rfl

theorem after_buffer_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (header buffer : BitVec 64) (geometry : Geometry header buffer)
    (domain : source.memaddrs=InitE.ordinaryDomain) (installed : OriginalCode.Installed source.code)
    (h : source.locals.lookup (ofString "h")=some (.val (.word header))) (room : buffer.toNat+1024≤2952790016)
    (facts : ∀ field∈firstField::baseRest,FieldFacts source.memory header field) (optional : ∀ field∈optionalFields,FieldFacts source.memory header field) :
    (allocated source buffer).clock-(evaluateHOLFiniteState (allocated source buffer) afterBuffer).2.clock≤1344 := by
  obtain ⟨context,p,buf,read,metadata⟩:=entry_facts source header buffer geometry domain h
  have bounded:=(PersistentAlloc.guards buffer 1024#64 room).2.2.2.1
  rw [rounded header buffer geometry] at bounded
  exact ClockCost.declared_current (allocated source buffer) "p" (.op .add [localVar "buf",.const 9#64]) (address buffer 9) afterPointer 1344 read
    (HeaderFirst.cost (entered source buffer) source.memory header buffer context installed bounded facts optional p buf)

/-- Every actual outcome of the unchanged current header encoder costs
at most1346body source ticks. Its1024-byte request room is derived only in
the callback of an actual normal allocator return. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (header buffer : BitVec 64) (geometry : Geometry header buffer)
    (domain : source.memaddrs=InitE.ordinaryDomain) (installed : OriginalCode.Installed source.code)
    (h : source.locals.lookup (ofString "h")=some (.val (.word header)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word buffer))) (bounded : buffer.toNat≤2952790016)
    (facts : ∀ field∈firstField::baseRest,FieldFacts source.memory header field) (optional : ∀ field∈optionalFields,FieldFacts source.memory header field) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤1346 := by
  obtain ⟨callee,called,amount⟩:=PersistentAlloc.environment source.code.lookup 1024#64 (PersistentAlloc.original_code source.code installed)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [.const 1024#64]=some (PersistentAlloc.values 1024#64):=rfl
  rw [current_body,HeaderEncoding.body_shape]
  apply ClockCost.scoped_reached_current source "buf" .one (ofString "alloc") [.const 1024#64] _ PersistentAlloc.body afterBuffer callee .one 1 1344 args called
    (PersistentAlloc.body_price source.code installed (callEntryStateHOLFinite source callee) rfl)
  intro child value normal checked
  obtain ⟨answer,room,endpoint⟩:=allocation_result source child buffer callee installed amount heap bounded value normal
  have price:=after_buffer_cost source header buffer geometry domain installed h room facts optional
  rw [←endpoint] at price
  exact price

/-- An actual normal current header return derives its mapped length1..916,
the real final heap and all older physical input/header memory. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (header buffer : BitVec 64) (geometry : Geometry header buffer)
    (domain : source.memaddrs=InitE.ordinaryDomain) (installed : OriginalCode.Installed source.code)
    (h : source.locals.lookup (ofString "h")=some (.val (.word header)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word buffer))) (bounded : buffer.toNat≤2952790016)
    (facts : ∀ field∈firstField::baseRest,FieldFacts source.memory header field) (optional : ∀ field∈optionalFields,FieldFacts source.memory header field)
    (value : ValueHOL 64) (returned : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ start encoded,1≤encoded ∧ encoded≤916 ∧ value=encodedPair start encoded ∧ AllocatedBytes.Arena start encoded ∧
      MemoryMetadata.erase target=MemoryMetadata.erase (heapPost source buffer) ∧ OldMemory target.memory source.memory buffer := by
  obtain ⟨callee,called,amount⟩:=PersistentAlloc.environment source.code.lookup 1024#64 (PersistentAlloc.original_code source.code installed)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [.const 1024#64]=some (PersistentAlloc.values 1024#64):=rfl
  rw [current_body,HeaderEncoding.body_shape] at returned
  obtain ⟨funded,child,childValue,inner,bodyRun,checked,remaining,endpoint⟩:=CallNormal.scoped_normal source target "buf" .one (ofString "alloc")
    [.const 1024#64] _ PersistentAlloc.body afterBuffer callee .one args called value returned
  obtain ⟨answer,room,childEndpoint⟩:=allocation_result source child buffer callee installed amount heap bounded childValue bodyRun
  rw [childEndpoint] at remaining
  obtain ⟨context,p,buf,read,metadata⟩:=entry_facts source header buffer geometry domain h
  obtain ⟨last,afterPointerRun,innerEndpoint⟩:=declaration_return_word (allocated source buffer) inner "p" (.op .add [localVar "buf",.const 9#64])
    (address buffer 9) afterPointer value read remaining
  have cursorBound:=(PersistentAlloc.guards buffer 1024#64 room).2.2.2.1
  rw [rounded header buffer geometry] at cursorBound
  obtain ⟨start,encoded,positive,size,answer,arena,frame,memory⟩:=HeaderFirst.normal (entered source buffer) last source.memory header buffer
    context installed cursorBound facts optional p buf value afterPointerRun
  rw [endpoint,innerEndpoint]
  exact ⟨start,encoded,positive,size,answer,arena,frame.trans metadata,memory⟩

end InitECandidate.Solver.Input.CurrentRlp.HeaderEncoder

#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderEncoder.current_body
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderEncoder.original_code
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderEncoder.rounded
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderEncoder.allocation_result
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderEncoder.entry_facts
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderEncoder.after_buffer_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderEncoder.body_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderEncoder.body_normal
