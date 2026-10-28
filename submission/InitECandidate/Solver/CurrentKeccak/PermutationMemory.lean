import InitECandidate.Solver.CurrentKeccak.PermutationCost
import InitECandidate.Solver.Input.ScalarLocals
import InitECandidate.Solver.Input.LocalEffectsLoop
import InitECandidate.Solver.Input.LocalEffectsScoped
import InitECandidate.Solver.Input.NormalDeclarationEntry
import InitECandidate.Solver.Input.StoreWordsNormal
import InitECandidate.Solver.Input.StoreNormal
import InitECandidate.Solver.Input.WordStoreNormal
import InitECandidate.Solver.Input.SequenceReturned

namespace InitECandidate.Solver.CurrentKeccak.Permutation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def lanes : List (String×Nat) := [("a00",0),("a10",8),("a20",16),("a30",24),("a40",32),("a01",40),("a11",48),("a21",56),("a31",64),("a41",72),("a02",80),("a12",88),("a22",96),("a32",104),("a42",112),("a03",120),("a13",128),("a23",136),("a33",144),("a43",152),("a04",160),("a14",168),("a24",176),("a34",184),("a44",192)]
def laneAddress (offset : Nat) : ExpHOL 64 := .op .add [localVar "stp",.const (BitVec.ofNat 64 offset)]
def loadLanes : List (String×Nat)→ProgHOL 64→ProgHOL 64
  | [],tail=>tail
  | (name,offset)::rest,tail=>.dec (ofString name) .one (.load .one (laneAddress offset)) (loadLanes rest tail)
def storeLanes : List (String×Nat)→ProgHOL 64
  | []=>.return (.const 0#64)
  | (name,offset)::rest=>.seq (.store (laneAddress offset) (localVar name)) (storeLanes rest)

theorem loads_shape : body=loadLanes lanes afterLanes := by
  simp only [body,loadLanes,lanes,afterLanes,ClockCost.dropDeclarations,Guest.Software.guestFn_keccak_f1600,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,laneAddress,localVar]

theorem stores_shape : storeTail=storeLanes lanes := by
  simp only [storeTail,afterLanes,ClockCost.dropDeclarations,body,Guest.Software.guestFn_keccak_f1600,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,storeLanes,lanes,laneAddress,localVar]

theorem round_words : ScalarLocals.Preserves roundBody := by
  simp only [roundBody,afterLanes,ClockCost.dropDeclarations,body,Guest.Software.guestFn_keccak_f1600,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  repeat first
    | apply ScalarLocals.declared
    | apply ScalarLocals.sequence
    | exact ScalarLocals.assign _ _

theorem round_frame (code) : LocalEffects.Preserves code roundBody := by
  simp only [roundBody,afterLanes,ClockCost.dropDeclarations,body,Guest.Software.guestFn_keccak_f1600,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  repeat first
    | apply LocalEffects.declared
    | apply LocalEffects.sequence
    | exact LocalEffects.assign code _ _

private theorem loads_memory (entries : List (String×Nat)) (tail : ProgHOL 64) (stp query : BitVec 64)
    (different : ∀ entry∈entries,ofString entry.1≠ofString "stp")
    (tailFrame : ∀ source post : PanSemStateFiniteExact 64 Guest.HostMemory,ScalarLocals.Words source →
      source.locals.lookup (ofString "stp")=some (.val (.word stp)) → ∀ value,
      evaluateHOLFiniteState source tail=(some (.returned value),post) → post.memory query=source.memory query)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ready : ScalarLocals.Words source)
    (cell : source.locals.lookup (ofString "stp")=some (.val (.word stp))) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (loadLanes entries tail)=(some (.returned value),post)) :
    post.memory query=source.memory query := by
  induction entries generalizing source post with
  | nil=>exact tailFrame source post ready cell value run
  | cons entry rest ih=>
    obtain ⟨name,offset⟩:=entry
    obtain ⟨declared,inner,read,checked,continued,endpoint⟩:=CallNormal.declaration_normal_entry source post name .one _ _ value run
    have shape : shapeOfHOLExact declared=.one := ((shapeEqHOL_eq_true _ _).mp checked).symm
    obtain ⟨word,rfl⟩:=scalar_word_of_shape declared shape
    have nextWords:=ready.set source (ofString name) word
    have notStp : ofString name≠ofString "stp" := different (name,offset) (by simp)
    have nextCell : (setVarHOLFinite (ofString name) (.val (.word word)) source).locals.lookup (ofString "stp")=some (.val (.word stp)) := by
      simpa [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notStp] using cell
    have later:=ih (by intro entry member; exact different entry (by simp [member])) _ inner nextWords nextCell continued
    rw [endpoint]
    exact later

private theorem stores_memory (entries : List (String×Nat)) (stp query : BitVec 64)
    (away : ∀ entry∈entries,query≠stp+BitVec.ofNat 64 entry.2)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ready : ScalarLocals.Words source)
    (cell : source.locals.lookup (ofString "stp")=some (.val (.word stp))) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (storeLanes entries)=(some (.returned value),post)) :
    post.memory query=source.memory query := by
  induction entries generalizing source post with
  | nil=>
    have frame:=LocalEffects.returned source.code (.const 0#64) source rfl
    change evaluateHOLFiniteState source (.return (.const 0#64))=(some (.returned value),post) at run
    rw [run] at frame
    exact congrFun (LocalEffects.memory_of_erase source post frame) query
  | cons entry rest ih=>
    obtain ⟨name,offset⟩:=entry
    have safe : LocalPrefix (ofString "stp") (.store (laneAddress offset) (localVar name)) := .store _ _
    obtain ⟨middle,front,back⟩:=Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 run
    have addressRead : eval source (laneAddress offset)=some (.val (.word (stp+BitVec.ofNat 64 offset))) := by
      simp [eval,laneAddress,evalHOLExact,evalListHOLExact,toExact,localVar,cell,valueIsWord,valueWord,wordOpHOL,wordOp]
    obtain ⟨actual,memory,read,stored,endpoint⟩:=Input.store_at_normal source middle _ _ (stp+BitVec.ofNat 64 offset) addressRead front
    have found : source.locals.lookup (ofString name)=some actual := by simpa [eval,evalHOLExact,toExact,localVar] using read
    obtain ⟨word,rfl⟩:=ready (ofString name) actual found
    have first:=Input.word_store_normal source middle _ _ (stp+BitVec.ofNat 64 offset) word addressRead read front
    have locals : middle.locals=source.locals := by rw [Input.store_none_frame source middle _ _ front]
    have nextWords : ScalarLocals.Words middle := by intro name value found; apply ready name value; rwa [←locals]
    have nextCell : middle.locals.lookup (ofString "stp")=some (.val (.word stp)) := by rw [locals]; exact cell
    have later:=ih (by intro entry member; exact away entry (by simp [member])) middle post nextWords nextCell back
    rw [later,first.2]
    exact if_neg (away (name,offset) (by simp))

/-- Real software permutation writes only its25 state lanes. Scalar store
sizes are derived from the reached checked local declarations/assignments. -/
theorem body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp query : BitVec 64)
    (ready : ScalarLocals.Words source) (cell : source.locals.lookup (ofString "stp")=some (.val (.word stp)))
    (away : ∀ offset : Nat,offset<200 → offset%8=0 → query≠stp+BitVec.ofNat 64 offset)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    post.memory query=source.memory query := by
  rw [loads_shape] at run
  apply loads_memory lanes afterLanes stp query (by decide) ?_ source post ready cell value run
  intro current target words currentCell returned normal
  rw [after_lanes_shape] at normal
  obtain ⟨declared,inner,read,checked,continued,endpoint⟩:=CallNormal.declaration_normal_entry current target "r" .one (.const 0#64) _ returned normal
  have shape : shapeOfHOLExact declared=.one := ((shapeEqHOL_eq_true _ _).mp checked).symm
  obtain ⟨counter,rfl⟩:=scalar_word_of_shape declared shape
  let entry:=setVarHOLFinite (ofString "r") (.val (.word counter)) current
  have entryWords : ScalarLocals.Words entry := words.set current _ counter
  have entryCell : entry.locals.lookup (ofString "stp")=some (.val (.word stp)) := by
    simpa [entry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "r"≠ofString "stp" from by decide] using currentCell
  have safe : LocalPrefix (ofString "stp") (.while condition roundBody) := .loop _ round_safe
  obtain ⟨middle,front,back⟩:=Input.sequence_returned entry inner _ _ returned (safe.summary_full entry).2.1 continued
  have nextWords:=ScalarLocals.loop condition roundBody round_words entry entryWords
  rw [front] at nextWords
  have nextCell:=(safe.summary_full entry).1
  rw [front] at nextCell
  have middleCell:= (nextCell rfl).trans entryCell
  have loopFrame:=LocalEffects.loop entry.code condition roundBody (round_frame entry.code) entry rfl
  rw [front] at loopFrame
  rw [stores_shape] at back
  have later:=stores_memory lanes stp query (by
    intro item member
    simp [lanes] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact away _ (by decide) (by decide)) middle inner nextWords middleCell returned back
  rw [endpoint]
  exact later.trans (congrFun (LocalEffects.memory_of_erase entry middle loopFrame) query)

end InitECandidate.Solver.CurrentKeccak.Permutation

#print axioms InitECandidate.Solver.CurrentKeccak.Permutation.round_words
#print axioms InitECandidate.Solver.CurrentKeccak.Permutation.round_frame
#print axioms InitECandidate.Solver.CurrentKeccak.Permutation.body_memory
