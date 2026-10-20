import InitECandidate.Solver.Input.Be64CallExecution

namespace InitECandidate.Solver.Input.AddressFromWords
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch GasBudget.MemoryWriter

def body : ProgHOL 64 := match Guest.guestFn_addr_from_words with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "out",.one),(ofString "hi4",.one),(ofString "mid8",.one),(ofString "lo8",.one)]
def values (pointer hi mid lo : BitVec 64) : List (ValueHOL 64) := [.val (.word pointer),.val (.word hi),.val (.word mid),.val (.word lo)]
def rawLocals (pointer hi mid lo : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "lo8" then some (.val (.word lo)) else if name = ofString "mid8" then some (.val (.word mid))
  else if name = ofString "hi4" then some (.val (.word hi)) else if name = ofString "out" then some (.val (.word pointer)) else none
def highArgs : List (ExpHOL 64) := [localVar "out",localVar "hi4"]
def midArgs : List (ExpHOL 64) := [.op .add [localVar "out",.const 4#64],localVar "mid8"]
def lowArgs : List (ExpHOL 64) := [.op .add [localVar "out",.const 12#64],localVar "lo8"]
def tail : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "st_be64") midArgs)
  (.seq (.call (some (none,none)) (ofString "st_be64") lowArgs) (.return (.const 0#64)))

theorem body_shape : body = .seq (.call (some (none,none)) (ofString "st_be32") highArgs) tail := by
  simp only [body,tail,highArgs,midArgs,lowArgs,Guest.guestFn_addr_from_words,progToHOL,expToHOL,List.map_cons,List.map_nil,Option.map_none,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "addr_from_words") = some (formals,body,.one) := by
  have checked := OriginalCode.indexed code installed 797 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_addr_from_words) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,Guest.guestFn_addr_from_words,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (pointer hi mid lo : BitVec 64)
    (code : codeFn (ofString "addr_from_words") = some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "addr_from_words") (values pointer hi mid lo) = some (body,callee,.one) ∧
      callee.lookup (ofString "out") = some (.val (.word pointer)) ∧ callee.lookup (ofString "hi4") = some (.val (.word hi)) ∧
      callee.lookup (ofString "mid8") = some (.val (.word mid)) ∧ callee.lookup (ofString "lo8") = some (.val (.word lo)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values pointer hi mid lo).length ∧
      ((formals.zip (values pointer hi mid lo)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "addr_from_words") (values pointer hi mid lo) = some (body,rawLocals pointer hi mid lo,.one) := by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ body _ .one raw
  refine ⟨callee,called,?_,?_,?_,?_⟩
  all_goals rw [locals]
  all_goals simp [rawLocals,show ofString "out" ≠ ofString "lo8" from by decide,show ofString "out" ≠ ofString "mid8" from by decide,
    show ofString "out" ≠ ofString "hi4" from by decide,show ofString "hi4" ≠ ofString "lo8" from by decide,
    show ofString "hi4" ≠ ofString "mid8" from by decide,show ofString "mid8" ≠ ofString "lo8" from by decide]

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer hi mid lo : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (out : source.locals.lookup (ofString "out") = some (.val (.word pointer)))
    (high : source.locals.lookup (ofString "hi4") = some (.val (.word hi)))
    (middle : source.locals.lookup (ofString "mid8") = some (.val (.word mid)))
    (low : source.locals.lookup (ofString "lo8") = some (.val (.word lo)))
    (mapped : BytesMapped source pointer 20) (enough : 7 ≤ source.clock) :
    ∃ post,evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))),post) ∧
      post.clock ≤ source.clock ∧ source.clock - 7 ≤ post.clock ∧ KeccakAbsorb.hashControl post = KeccakAbsorb.hashControl source := by
  have argsHigh : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) highArgs = some [.val (.word pointer),.val (.word hi)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,highArgs,localVar,out,high]
  have highMapped : BytesMapped source pointer 4 := by simpa only [BitVec.add_zero] using mapped.subrange 0 4 (by decide)
  have highRun := MemoryWordCalls.be32_execute source pointer hi highArgs installed argsHigh (be32_mapped highMapped) (by omega)
  let first := {source with memory := GasBudget.Be32Stores.written source.memory source.be pointer hi GasBudget.Be32Stores.clauses,clock := source.clock - 1}
  have argsMid : evalListHOLFinite first (h := fun query => Classical.propDecidable (first.memaddrs query)) midArgs = some [.val (.word (pointer + 4#64)),.val (.word mid)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,midArgs,localVar,first,out,middle,valueIsWord,valueWord,wordOpHOL,wordOp]
  obtain ⟨second,midRun,midLocals,midUpper,midLower,midControl⟩ := MemoryWordCalls.be64_execute first (pointer + 4#64) mid midArgs installed argsMid
    (mapped.subrange 4 8 (by decide)) (by change 3 ≤ source.clock - 1; omega)
  have argsLow : evalListHOLFinite second (h := fun query => Classical.propDecidable (second.memaddrs query)) lowArgs = some [.val (.word (pointer + 12#64)),.val (.word lo)] := by
    have currentOut : second.locals.lookup (ofString "out") = some (.val (.word pointer)) := by rw [midLocals]; exact out
    have currentLow : second.locals.lookup (ofString "lo8") = some (.val (.word lo)) := by rw [midLocals]; exact low
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,lowArgs,localVar,currentOut,currentLow,valueIsWord,valueWord,wordOpHOL,wordOp]
  have secondCode : second.code = first.code := by have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.code) midControl; exact h
  have secondDomain : second.memaddrs = source.memaddrs := by have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) midControl; exact h
  have secondInstalled : OriginalCode.Installed second.code := secondCode.symm ▸ installed
  have lowMapped : BytesMapped second (pointer + 12#64) 8 := by
    intro offset bound
    rw [secondDomain]
    exact mapped.subrange 12 8 (by decide) offset bound
  change source.clock - 1 - 3 ≤ second.clock at midLower
  obtain ⟨third,lowRun,_,lowUpper,lowLower,lowControl⟩ := MemoryWordCalls.be64_execute second (pointer + 12#64) lo lowArgs secondInstalled argsLow lowMapped (by omega)
  have actual : evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite third) := by
    rw [body_shape,StateSteps.next_sequence source first _ _ highRun (Nat.sub_le _ _),tail,
      StateSteps.next_sequence first second _ _ midRun midUpper,StateSteps.next_sequence second third _ _ lowRun lowUpper]
    exact BuildEntry.zero_return third
  refine ⟨emptyLocalsHOLFinite third,actual,?_,?_,?_⟩
  · change third.clock ≤ source.clock
    change second.clock ≤ source.clock - 1 at midUpper
    omega
  · change source.clock - 7 ≤ third.clock
    omega
  · exact lowControl.trans midControl

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer hi mid lo : BitVec 64) (arguments : List (ExpHOL 64))
    (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments = some (values pointer hi mid lo))
    (mapped : BytesMapped source pointer 20) (enough : 8 ≤ source.clock) :
    ∃ post,evaluateHOLFiniteState source (.call (some (none,none)) (ofString "addr_from_words") arguments) = (none,post) ∧
      post.locals = source.locals ∧ post.clock ≤ source.clock ∧ source.clock - 8 ≤ post.clock ∧ KeccakAbsorb.hashControl post = KeccakAbsorb.hashControl source := by
  obtain ⟨callee,called,out,high,middle,low⟩ := environment source.code.lookup pointer hi mid lo (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨target,run,upper,lower,control⟩ := execute entry pointer hi mid lo installed out high middle low mapped (by change 7 ≤ source.clock - 1; omega)
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "addr_from_words") arguments (values pointer hi mid lo) body callee .one
    (.val (.word 0#64)) target args called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨{target with locals := source.locals},actual,rfl,?_,?_,control⟩
  · change target.clock ≤ source.clock
    change target.clock ≤ source.clock - 1 at upper
    omega
  · change source.clock - 8 ≤ target.clock
    change source.clock - 1 - 7 ≤ target.clock at lower
    omega

end InitECandidate.Solver.Input.AddressFromWords

#print axioms InitECandidate.Solver.Input.AddressFromWords.body_shape
#print axioms InitECandidate.Solver.Input.AddressFromWords.original_code
#print axioms InitECandidate.Solver.Input.AddressFromWords.environment
#print axioms InitECandidate.Solver.Input.AddressFromWords.execute
#print axioms InitECandidate.Solver.Input.AddressFromWords.call_execute
