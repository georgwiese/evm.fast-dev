import InitECandidate.Solver.WitnessRadix.CopyFreshFrame
import InitECandidate.Solver.Input.ScalarArgumentsLookup
import InitECandidate.Solver.Input.CurrentRlp.HeaderWriteFrame
import InitECandidate.Solver.Input.RlpWrite.WordWriteCall

namespace InitECandidate.Solver.Input.CurrentRlp.WordWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch RlpWrite

abbrev body:=Code.body .writeWord

theorem current_body : body=RlpWrite.WordWrite.body:=rfl

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "rlp_encode_word")=some (RlpWrite.WordWrite.formals,body,.one) := by
  have known:=Code.installed code installed .writeWord
  simpa only [Code.name,Code.formals,Code.shape,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_rlp_encode_word,RlpWrite.WordWrite.formals,paramToHOL,shapeToHOL,List.map_cons,List.map_nil] using known

/-- Both early-return guards and the genuine long form are covered for
arbitrary output memory and every entry clock. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst word : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (w : source.locals.lookup (ofString "w")=some (.val (.word word))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤18 := by
  have tailPrice:=ClockCost.stopping_guard_current source RlpWrite.WordWrite.shortTest (shortForm (localVar "w"))
    (longForm "w" RlpWrite.WordWrite.longTag) 0 18 (HeaderWrite.short_stops source _)
    (HeaderWrite.short_cost source.code _ source rfl) (HeaderWrite.long_cost source dst word "w" RlpWrite.WordWrite.longTag installed d w (by decide) (by decide))
  have total:=ClockCost.stopping_guard_current source RlpWrite.WordWrite.zeroTest (shortForm (.const 128#64))
    (.seq RlpWrite.WordWrite.shortGuard (longForm "w" RlpWrite.WordWrite.longTag)) 0 18 (HeaderWrite.short_stops source _)
    (HeaderWrite.short_cost source.code _ source rfl) (by simpa only [RlpWrite.WordWrite.shortGuard,Nat.max_eq_right (show 0≤18 by omega)] using tailPrice)
  rw [current_body,RlpWrite.WordWrite.body_shape,RlpWrite.WordWrite.zeroGuard]
  simpa only [Nat.max_eq_right (show 0≤18 by omega)] using total

/-- An actual current scalar-word return gives its true1..9-byte size,
complete runtime metadata and writes confined to that real destination. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst word : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (w : source.locals.lookup (ofString "w")=some (.val (.word word)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ encoded,1≤encoded ∧ encoded≤9 ∧ value=.val (.word (BitVec.ofNat 64 encoded)) ∧
      source.clock-target.clock≤18 ∧ WriteFrame source target dst 9 := by
  have priced:=body_cost source dst word installed d w
  rw [normal] at priced
  have zeroRead : eval source RlpWrite.WordWrite.zeroTest=some (.val (.word (if word=0#64 then 1#64 else 0#64))):=by
    simp [eval,RlpWrite.WordWrite.zeroTest,evalHOLExact,toExact,localVar,w,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have shortRead : eval source RlpWrite.WordWrite.shortTest=some (.val (.word (if word.toNat<128 then 1#64 else 0#64))):=by
    simp [eval,RlpWrite.WordWrite.shortTest,evalHOLExact,toExact,localVar,w,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
  have afterZero (run : evaluateHOLFiniteState source (.seq RlpWrite.WordWrite.shortGuard (longForm "w" RlpWrite.WordWrite.longTag))=(some (.returned value),target)) :
      ∃ encoded,1≤encoded ∧ encoded≤9 ∧ value=.val (.word (BitVec.ofNat 64 encoded)) ∧ WriteFrame source target dst 9 := by
    rw [RlpWrite.WordWrite.shortGuard] at run
    exact HeaderWrite.guarded_normal source target dst RlpWrite.WordWrite.shortTest (localVar "w") (longForm "w" RlpWrite.WordWrite.longTag)
      (word.toNat<128) d shortRead value (fun tailRun=>HeaderWrite.long_normal source target dst word "w" RlpWrite.WordWrite.longTag installed d w (by decide) (by decide) value tailRun) run
  have shaped:=normal
  rw [current_body,RlpWrite.WordWrite.body_shape,RlpWrite.WordWrite.zeroGuard] at shaped
  obtain ⟨encoded,lower,upper,answer,frame⟩:=HeaderWrite.guarded_normal source target dst RlpWrite.WordWrite.zeroTest (.const 128#64)
    (.seq RlpWrite.WordWrite.shortGuard (longForm "w" RlpWrite.WordWrite.longTag)) (word=0#64) d zeroRead value afterZero shaped
  exact ⟨encoded,lower,upper,answer,priced,frame⟩

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64))
    (dst word : BitVec 64) (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word dst),.val (.word word)]) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "rlp_encode_word") arguments)).2.clock≤19 := by
  obtain ⟨callee,called,d,w⟩:=RlpWrite.WordWrite.environment source.code.lookup dst word (original_code source.code installed)
  exact ClockCost.call_current source (some none) (ofString "rlp_encode_word") arguments _ body callee .one 18 args called
    (body_cost (callEntryStateHOLFinite source callee) dst word installed d w)

theorem call_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64))
    (dst word : BitVec 64) (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word dst),.val (.word word)])
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "rlp_encode_word") arguments)=(none,post)) : WriteFrame source post dst 9 := by
  obtain ⟨callee,called,d,w⟩:=RlpWrite.WordWrite.environment source.code.lookup dst word (original_code source.code installed)
  apply WriteFrame.ignored source post (ofString "rlp_encode_word") arguments _ body callee .one dst 9 args called
  · intro target value run
    obtain ⟨encoded,lower,upper,answer,price,frame⟩:=body_normal (callEntryStateHOLFinite source callee) target dst word installed d w value run
    exact frame
  · exact normal

end InitECandidate.Solver.Input.CurrentRlp.WordWrite

#print axioms InitECandidate.Solver.Input.CurrentRlp.WordWrite.current_body
#print axioms InitECandidate.Solver.Input.CurrentRlp.WordWrite.original_code
#print axioms InitECandidate.Solver.Input.CurrentRlp.WordWrite.body_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.WordWrite.body_normal
#print axioms InitECandidate.Solver.Input.CurrentRlp.WordWrite.call_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.WordWrite.call_frame

namespace InitECandidate.Solver.Input.CurrentRlp.WordWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Resolve only the actual dynamic field reads and original scalar ABI. -/
theorem current_argument_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (first second : ExpHOL 64) (values : List (ValueHOL 64)) (actual : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [first,second]=some values)
    (called : lookupCodeHOLFinite source.code.lookup (ofString "rlp_encode_word") values=some (actual,callee,shape)) :
    ∃ dst word : BitVec 64,values=[.val (.word dst),.val (.word word)] ∧
      eval source first=some (.val (.word dst)) ∧ eval source second=some (.val (.word word)) ∧
      actual=body ∧ callee.lookup (ofString "dst")=some (.val (.word dst)) ∧ callee.lookup (ofString "w")=some (.val (.word word)) := by
  obtain ⟨left,right,firstRead,secondRead,valuesEq⟩:=CallNormal.two_argument_values source first second values args
  rw [valuesEq] at called
  obtain ⟨dst,word,firstEq,secondEq⟩:=CallNormal.two_scalar_words source.code.lookup (ofString "rlp_encode_word")
    (ofString "dst") (ofString "w") body actual .one shape (original_code source.code installed) left right callee called
  subst left
  subst right
  obtain ⟨expected,expectedCall,d,w⟩:=RlpWrite.WordWrite.environment source.code.lookup dst word (original_code source.code installed)
  have same:=Option.some.inj (called.symm.trans expectedCall)
  have bodyEq : actual=body:=congrArg Prod.fst same
  have calleeEq : callee=expected:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
  rw [←calleeEq] at d w
  exact ⟨dst,word,valuesEq,firstRead,secondRead,bodyEq,d,w⟩

theorem dynamic_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (destination : Option (Option MlS))
    (first second : ExpHOL 64) (installed : OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "rlp_encode_word") [first,second])).2.clock≤19 := by
  apply ClockCost.call_arguments_current source destination (ofString "rlp_encode_word") [first,second] 18
  intro values actual callee shape args called
  obtain ⟨dst,word,valuesEq,firstRead,secondRead,bodyEq,d,w⟩:=current_argument_entry source first second values actual callee shape installed args called
  rw [bodyEq]
  exact body_cost (callEntryStateHOLFinite source callee) dst word installed d w

/-- The actual assigned scalar field call returns its small encoded word,
retains caller bindings and protects all memory below the output frontier. -/
theorem assigned_current_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : MlS)
    (arguments : List (ExpHOL 64)) (dst word : BitVec 64) (floor : Nat)
    (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word dst),.val (.word word)])
    (headerFits : dst.toNat+9<2^64) (aligned : floor%8=0) (afterFloor : floor≤dst.toNat)
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,name),none)) (ofString "rlp_encode_word") arguments)=(none,post)) :
    ∃ encoded,1≤encoded ∧ encoded≤9 ∧ post.locals.lookup name=some (.val (.word (BitVec.ofNat 64 encoded))) ∧
      MemoryMetadata.erase post=MemoryMetadata.erase source ∧
      (∀ query : BitVec 64,query.toNat<floor→post.memory query=source.memory query) ∧
      ∀ key : MlS,key≠name→post.locals.lookup key=source.locals.lookup key := by
  obtain ⟨callee,called,d,w⟩:=RlpWrite.WordWrite.environment source.code.lookup dst word (original_code source.code installed)
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,child,returned,actualArgs,actualCalled,run,checked,endpoint⟩:=
    CallNormal.local_data source post name (ofString "rlp_encode_word") arguments normal
  have sameValues : actualValues=[.val (.word dst),.val (.word word)]:=Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have same : (actualBody,actualCallee,actualShape)=(body,callee,.one):=Option.some.inj (actualCalled.symm.trans called)
  cases same
  obtain ⟨encoded,positive,upper,answer,cost,frame⟩:=body_normal (callEntryStateHOLFinite source callee) child dst word installed d w returned run
  refine ⟨encoded,positive,upper,?_,?_,?_,?_⟩
  · rw [endpoint,answer]
    simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  · rw [endpoint]
    exact frame.metadata
  · intro query before
    rw [endpoint]
    exact frame.memory query (CopyGeneral.Away.after_floor dst query 9 floor aligned afterFloor headerFits before)
  · intro key different
    rw [endpoint]
    simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different,Ne.symm different]

end InitECandidate.Solver.Input.CurrentRlp.WordWrite

#print axioms InitECandidate.Solver.Input.CurrentRlp.WordWrite.current_argument_entry
#print axioms InitECandidate.Solver.Input.CurrentRlp.WordWrite.dynamic_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.WordWrite.assigned_current_normal
