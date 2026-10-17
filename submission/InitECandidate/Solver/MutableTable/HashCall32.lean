import InitECandidate.Solver.MutableTable.HashAligned32

namespace InitECandidate.Solver.MutableTable.Hash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem aligned32_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (words : Fin 4→BitVec 64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (length : source.locals.lookup (ofString "key_len")=some (.val (.word 32#64)))
    (aligned : pointer &&& 7#64=0#64)
    (mapped : ∀ i : Fin 4,source.memaddrs (pointer+BitVec.ofNat 64 (8*i.val)))
    (stored : ∀ i : Fin 4,source.memory (pointer+BitVec.ofNat 64 (8*i.val))=.word (words i)) :
    ∃ target,evaluateHOLFiniteState source body=(some (.returned (.val (.word (resultWord words)))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite source := by
  let hs:=bind source "h" 14695981039346656037#64
  let ws:=bind hs "w" 0#64
  have pW : ws.locals.lookup (ofString "p")=some (.val (.word pointer)):=
    (bind_lookup_other _ "w" "p" _ (by decide)).trans ((bind_lookup_other _ "h" "p" _ (by decide)).trans p)
  have lengthW : ws.locals.lookup (ofString "key_len")=some (.val (.word 32#64)):=
    (bind_lookup_other _ "w" "key_len" _ (by decide)).trans ((bind_lookup_other _ "h" "key_len" _ (by decide)).trans length)
  have hW : ws.locals.lookup (ofString "h")=some (.val (.word 14695981039346656037#64)):=
    (bind_lookup_other _ "w" "h" _ (by decide)).trans (bind_lookup_same _ _ _)
  have run:=aligned32_core ws pointer words pW lengthW hW (bind_lookup_same _ _ _) aligned mapped stored
  have wScope:=Input.ScalarScope.declare_execute hs _ "w" (.const 0#64) 0#64 afterLocals _ rfl run
  let target:=restore source "h" (restore hs "w" (emptyLocalsHOLFinite ws))
  refine ⟨target,?_,rfl⟩
  rw [body_shape]
  exact Input.ScalarScope.declare_execute source _ "h" (.const 14695981039346656037#64) 14695981039346656037#64 _ _ rfl wScope

def rawLocals (pointer : BitVec 64) (name : MlS) : Option (ValueHOL 64):=
  if name=ofString "key_len" then some (.val (.word 32#64))
  else if name=ofString "p" then some (.val (.word pointer)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (pointer : BitVec 64)
    (code : codeFn (ofString "htab_hash")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "htab_hash") [.val (.word pointer),.val (.word 32#64)]=some (body,callee,.one) ∧
      callee.lookup (ofString "p")=some (.val (.word pointer)) ∧ callee.lookup (ofString "key_len")=some (.val (.word 32#64)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=([.val (.word pointer),.val (.word 32#64)] : List (ValueHOL 64)).length ∧
      ((formals.zip [.val (.word pointer),.val (.word 32#64)]).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,shapeOfHOLExact,shapeEqHOL]
  have raw : lookupCodeHOLExact codeFn (ofString "htab_hash") [.val (.word pointer),.val (.word 32#64)]=some (body,rawLocals pointer,.one) := by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "p"≠ofString "key_len" from by decide]
  · simp [rawLocals]

/-- Actual aligned32-byte hash caller, with canonical continuation and one
call clock. No hash-distribution property or successful-call premise is used. -/
theorem aligned32_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (words : Fin 4→BitVec 64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word pointer),.val (.word 32#64)])
    (code : source.code.lookup (ofString "htab_hash")=some (formals,body,.one))
    (aligned : pointer &&& 7#64=0#64)
    (mapped : ∀ i : Fin 4,source.memaddrs (pointer+BitVec.ofNat 64 (8*i.val)))
    (stored : ∀ i : Fin 4,source.memory (pointer+BitVec.ofNat 64 (8*i.val))=.word (words i)) (enough : 1≤source.clock) :
    evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_hash") expressions continuation)=
      (let output:=evaluateHOLFiniteState (bind {source with clock:=source.clock-1} name (resultWord words)) continuation
      (output.1,restore source name output.2)) := by
  obtain ⟨callee,called,p,len⟩:=environment source.code.lookup pointer code
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨target,run,frame⟩:=aligned32_execute entry pointer words p len aligned mapped stored
  have actual:=Input.CallNormal.pure_return_execute source target name (ofString "htab_hash") expressions _ body continuation callee (resultWord words) 0 args called enough run frame
  simpa only [Nat.sub_zero] using actual

end InitECandidate.Solver.MutableTable.Hash

#print axioms InitECandidate.Solver.MutableTable.Hash.aligned32_execute
#print axioms InitECandidate.Solver.MutableTable.Hash.environment
#print axioms InitECandidate.Solver.MutableTable.Hash.aligned32_call
