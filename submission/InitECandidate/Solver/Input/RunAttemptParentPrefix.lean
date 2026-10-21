import InitECandidate.Solver.Input.RunAttemptRead
import InitECandidate.Solver.Input.DeclarationTrace

namespace InitECandidate.Solver.Input.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def countEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count : BitVec 64) := bind source "nh" count

def parentEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count : BitVec 64) (parent : ValueHOL 64) :=
  setVarHOLFinite (ofString "parent") parent (countEntry source count)

def constructorEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count hashes : BitVec 64) (parent : ValueHOL 64) :=
  putGlobal (putGlobal (parentEntry source count parent) "block_hashes" hashes) "block_hashes_n" count

def restoreConstructor (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count : BitVec 64) (target : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  restore source "nh" (restore (countEntry source count) "parent" target)

/-- The actual nonempty guard, parent read and two existing global writes
reach the real constructor scopes without source call/loop ticks. Invalid
parent reads or the empty-header guard stop within that same zero allowance. -/
theorem parent_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (si hs hashes count oldHashes oldCount : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena si 96) (aligned : si.toNat%8=0)
    (siCell : source.locals.lookup (ofString "si")=some (.val (.word si)))
    (pairCell : source.locals.lookup (ofString "vh")=some (Headers.Validate.result hs hashes))
    (countCell : source.memory (byteAddress si 80)=.word count)
    (hashesCell : source.globals.lookup (ofString "block_hashes")=some (.val (.word oldHashes)))
    (globalCount : source.globals.lookup (ofString "block_hashes_n")=some (.val (.word oldCount)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterHeaders=(outcome,post)) :
    source.clock-post.clock≤0 ∨ ∃ parent inner,count≠0#64 ∧
      evaluateHOLFiniteState (constructorEntry source count hashes parent) constructors=(outcome,inner) ∧
      post=restoreConstructor source count inner := by
  have read:=field_read source si count 80 domain arena aligned (by decide) (by decide) siCell countCell
  rw [shapes.2.2.2.1] at run
  obtain ⟨first,continued,endpoint⟩ := ScalarScope.declare_trace source post "nh" (field 80) count afterCount outcome read run
  let counted:=countEntry source count
  change evaluateHOLFiniteState counted afterCount=(outcome,first) at continued
  have currentCount : counted.locals.lookup (ofString "nh")=some (.val (.word count)) := bind_lookup_same source "nh" count
  have dispatch : evaluateHOLFiniteState counted emptyGuard=
      if count=0#64 then evaluateHOLFiniteState counted (.raise (ofString "BlockErr") (.const 3#64)) else (none,counted) := by
    by_cases zero : count=0#64
    · simp [emptyGuard,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,localVar,toExact,currentCount,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero]
    · simp [emptyGuard,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,localVar,toExact,currentCount,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero]
  have choice:=Input.sequence_choice counted emptyGuard (.raise (ofString "BlockErr") (.const 3#64))
    (.dec (ofString "parent") .one parentExpression afterParent) (count=0#64) dispatch
    (fun current=>Input.raise_ne_none current (ofString "BlockErr") (.const 3#64))
  rw [shapes.2.2.2.2.1,choice] at continued
  by_cases zero : count=0#64
  · rw [if_pos zero] at continued
    have price:=Input.ClockCost.raised counted.code (ofString "BlockErr") (.const 3#64) counted rfl
    rw [continued] at price
    have clock : post.clock=first.clock := by rw [endpoint]; rfl
    change source.clock-first.clock≤0 at price
    exact Or.inl (by rw [clock]; exact price)
  · rw [if_neg zero] at continued
    rcases declaration_trace counted first "parent" .one parentExpression afterParent outcome continued with stopped|reached
    · have clock : post.clock=first.clock := by rw [endpoint]; rfl
      change source.clock-first.clock≤0 at stopped
      exact Or.inl (by rw [clock]; exact stopped)
    · obtain ⟨parent,inner,parentRead,parentShape,remaining,restored⟩ := reached
      let entered:=parentEntry source count parent
      change evaluateHOLFiniteState entered afterParent=(outcome,inner) at remaining
      have pair : entered.locals.lookup (ofString "vh")=some (Headers.Validate.result hs hashes) := by
        simp [entered,parentEntry,countEntry,WitnessRadix.QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
        exact pairCell
      have countBinding : entered.locals.lookup (ofString "nh")=some (.val (.word count)) := by
        simp [entered,parentEntry,countEntry,WitnessRadix.QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "parent"≠ofString "nh" from by decide]
      have hashesRead : eval entered (.rfield 1 (localVar "vh"))=some (.val (.word hashes)) := by
        simp [eval,evalHOLExact,localVar,toExact,pair,Headers.Validate.result]
      have hashesRun:=global_assign_execute entered "block_hashes" oldHashes hashes (.rfield 1 (localVar "vh")) hashesCell hashesRead
      let updated:=putGlobal entered "block_hashes" hashes
      have countRead : eval updated (localVar "nh")=some (.val (.word count)) := by simp [eval,evalHOLExact,localVar,toExact]; exact countBinding
      have oldCountCell : updated.globals.lookup (ofString "block_hashes_n")=some (.val (.word oldCount)) :=
        (putGlobal.lookup_other entered "block_hashes" hashes (ofString "block_hashes_n") (by decide)).trans globalCount
      have countRun:=global_assign_execute updated "block_hashes_n" oldCount count (localVar "nh") oldCountCell countRead
      dsimp only [updated] at countRun
      simp only [shapes.2.2.2.2.2.1,evaluateHOLFiniteState_seq_line780,hashesRun,countRun,evaluateHOLFiniteState_skip] at remaining
      exact Or.inr ⟨parent,inner,zero,remaining,by rw [endpoint,restored]; rfl⟩

end InitECandidate.Solver.Input.RunAttempt

#print axioms InitECandidate.Solver.Input.RunAttempt.parent_prefix
