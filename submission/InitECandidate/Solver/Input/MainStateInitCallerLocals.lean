import InitECandidate.Solver.Input.MainRunAttemptConstructorReached

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure CallerLocals (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  si : source.locals.lookup (ofString "si")=some (.val (.word (RequestPrefix.cursor input)))
  payload : source.locals.lookup (ofString "pl")=some (.val (.word (PayloadPrefix.cursor input)))

def callerState (input : Guest.InputBlob) (source headerTarget nodeTarget codeTarget : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root heap codeTable : BitVec 64) (parent : ValueHOL 64):=
  let afterHeader:=parentSource source headerTarget input root
  let ready:=RunAttempt.constructorEntry afterHeader (countWord input) (hashArray input root) parent
  CallNormal.continuationEntry (RunAttempt.codeEntry ready nodeTarget heap) codeTarget "codedb" (.val (.word codeTable))

/-- Genuine header/database scope restoration retains the original SI and
actual payload local, despite arbitrary callee-local changes. -/
theorem caller_locals (input : Guest.InputBlob) (source headerTarget nodeTarget codeTarget : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root heap codeTable : BitVec 64) (parent : ValueHOL 64)
    (siCell : source.locals.lookup (ofString "si")=some (.val (.word (RequestPrefix.cursor input)))) :
    CallerLocals input (callerState input source headerTarget nodeTarget codeTarget root heap codeTable parent):=by
  let afterHeader:=parentSource source headerTarget input root
  let ready:=RunAttempt.constructorEntry afterHeader (countWord input) (hashArray input root) parent
  let codeSource:=RunAttempt.codeEntry ready nodeTarget heap
  have firstSI:=(CallNormal.continuation_lookup_other (validatorEntry source input) headerTarget "vh" "si"
    (Headers.Validate.result (initialHeap root) (hashArray input root)) (by decide)).trans
      (RunAttempt.headerEntry_si source (PayloadPrefix.cursor input) (RequestPrefix.cursor input) siCell)
  have readySI:=RunAttempt.constructor_si afterHeader (countWord input) (hashArray input root) (RequestPrefix.cursor input) parent firstSI
  have nextSI:=(CallNormal.continuation_lookup_other ready nodeTarget "nodedb" "si" (.val (.word heap)) (by decide)).trans readySI
  have lastSI:=(CallNormal.continuation_lookup_other codeSource codeTarget "codedb" "si" (.val (.word codeTable)) (by decide)).trans nextSI
  have firstPL:=(CallNormal.continuation_lookup_other (validatorEntry source input) headerTarget "vh" "pl"
    (Headers.Validate.result (initialHeap root) (hashArray input root)) (by decide)).trans
      (bind_lookup_same source "pl" (PayloadPrefix.cursor input))
  have readyPL : ready.locals.lookup (ofString "pl")=some (.val (.word (PayloadPrefix.cursor input))):=by
    simpa [ready,RunAttempt.constructorEntry,putGlobal,RunAttempt.parentEntry,RunAttempt.countEntry,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
      show ofString "parent"≠ofString "pl" from by decide,show ofString "nh"≠ofString "pl" from by decide] using firstPL
  have nextPL:=(CallNormal.continuation_lookup_other ready nodeTarget "nodedb" "pl" (.val (.word heap)) (by decide)).trans readyPL
  have lastPL:=(CallNormal.continuation_lookup_other codeSource codeTarget "codedb" "pl" (.val (.word codeTable)) (by decide)).trans nextPL
  exact ⟨lastSI,lastPL⟩

theorem CallerLocals.of_locals (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (locals : CallerLocals input source) (same : target.locals=source.locals) : CallerLocals input target:=by
  constructor <;> rewrite [same]
  · exact locals.si
  · exact locals.payload

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.caller_locals
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.CallerLocals.of_locals
