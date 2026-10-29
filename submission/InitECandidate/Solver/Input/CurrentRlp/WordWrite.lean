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
