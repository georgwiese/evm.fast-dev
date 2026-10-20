import InitECandidate.Solver.Mpt.AccountCodeNonempty
import InitECandidate.Solver.Mpt.AccountMutationControl
import InitECandidate.Solver.Mpt.AccountMutationMonotone

namespace InitECandidate.Solver.Mpt.AccountCode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix MutableTable NaturalLayout GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def codeBranch : ProgHOL 64 := .ite (.cmp .equal (localVar "eq") (.const 0#64)) nonemptyBranch .skip

def branchPrice (population : Nat) (created : Bool) : Nat :=
  if created then Journal.Append.setPrice .word population + 2 else 0

theorem nonempty_safe (key : MlS) (different : key ≠ ofString "sl") : Input.LocalPrefix key nonemptyBranch :=
  .decCall _ _ _ _ different (.seq (.store _ _) (.seq (.store _ _) (.call none _ _ (by intro name impossible; cases impossible))))

theorem branch_safe (key : MlS) (different : key ≠ ofString "sl") : Input.LocalPrefix key codeBranch :=
  .ite _ (nonempty_safe key different) .skip

theorem branch_dispatch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (answer : BitVec 64)
    (binding : source.locals.lookup (ofString "eq") = some (.val (.word answer))) :
    evaluateHOLFiniteState source codeBranch = if answer = 0#64 then evaluateHOLFiniteState source nonemptyBranch else (none,source) := by
  classical
  by_cases zero : answer = 0#64
  all_goals simp [codeBranch,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,localVar,toExact,binding,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero]

theorem branch_prefix {ι : Type} [Fintype ι] [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor cutoff protectedCursor population : Nat)
    (objects : ι → TableFamily.Object) (writer outer : ι) (kind : (objects writer).kind = .word) (different : writer ≠ outer)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι) (accounts : List (BitVec 64)) (property : ι → BitVec 64 → Prop)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap) (before : protectedCursor ≤ cursor)
    (journalAbove : cutoff ≤ base) (populations : ∀ index,(objects index).slots.length ≤ population)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (values : TableFamily.ValuesHave source objects property) (savedValues : Journal.EntryValues entries count property)
    (accountApart : ∀ account,account ∈ accounts → account.toNat + 56 ≤ base ∨ base + 32 * cap ≤ account.toNat)
    (code hashValue transaction : BitVec 64) (length : Nat)
    (codeArena : AllocatedBytes.Arena code length) (hashArena : AllocatedBytes.Arena hashValue 32)
    (codeLocal : source.locals.lookup (ofString "code") = some (.val (.word code)))
    (lengthLocal : source.locals.lookup (ofString "code_len") = some (.val (.word (BitVec.ofNat 64 length))))
    (hashLocal : source.locals.lookup (ofString "h") = some (.val (.word hashValue)))
    (transactionGlobal : source.globals.lookup (ofString "ts") = some (.val (.word transaction)))
    (mapped : source.memaddrs (transaction + 48#64)) (storedTable : source.memory (transaction + 48#64) = .word (objects writer).pointer)
    (tableBefore : (transaction + 48#64).toNat < cursor)
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (answer : BitVec 64) (answerLocal : source.locals.lookup (ofString "eq") = some (.val (.word answer)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterCompare = (some (.returned returned),post)) :
    ∃ (ready : PanSemStateFiniteExact 64 Guest.HostMemory) (created : Bool), ∃ nextCursor nextEntries next nextProperty nextCount,
      (∀ key : MlS,key ≠ ofString "sl" → ready.locals.lookup key = source.locals.lookup key) ∧
      evaluateHOLFiniteState ready afterBranch = (some (.returned returned),post) ∧
      (if created then cursor + 16 ≤ nextCursor ∧ CodeSlice.Image ready (BitVec.ofNat 64 cursor) code length ∧
        (∀ offset : Nat,offset < 16 → TableFamily.Outside next (BitVec.ofNat 64 cursor + BitVec.ofNat 64 offset)) else True) ∧
      AccountMutation.Result source ready cursor nextCursor cutoff protectedCursor objects next outer base cap count nextCount nextEntries accounts accounts property nextProperty
        (branchPrice (objects writer).slots.length created) 1 (population + 1) := by
  classical
  obtain ⟨ready,branchRun,tailRun,_⟩ := (branch_safe (ofString "addr") (by decide)).normal_continue source post afterBranch returned normal
  have keep (key : MlS) (other : key ≠ ofString "sl") : ready.locals.lookup key = source.locals.lookup key := by
    have summary := (branch_safe key other).summary source
    rw [branchRun] at summary
    exact summary.1 rfl
  rw [branch_dispatch source answer answerLocal] at branchRun
  by_cases zero : answer = 0#64
  · rw [if_pos zero] at branchRun
    obtain ⟨nextCursor,nextEntries,next,sliceBefore,sliceImage,outside,data⟩ := nonempty_normal source ready cursor cutoff protectedCursor population objects writer outer kind different base cap count entries accounts property
      family image zone countBound before journalAbove populations environment installed registry values savedValues accountApart code hashValue transaction length codeArena hashArena codeLocal lengthLocal hashLocal transactionGlobal mapped storedTable tableBefore journal capacity counter branchRun
    exact ⟨ready,true,nextCursor,nextEntries,next,AccountValueExtension.added property writer (BitVec.ofNat 64 cursor),count + 1,keep,tailRun,⟨sliceBefore,sliceImage,outside⟩,data⟩
  · rw [if_neg zero] at branchRun
    have same : ready = source := (congrArg Prod.snd branchRun).symm
    subst ready
    have data := AccountMutation.control source cursor cutoff protectedCursor population objects outer base cap count entries accounts property family image zone countBound before populations environment registry values savedValues counter 0 (Nat.zero_le _) source.locals
    have exactData : AccountMutation.Result source source cursor cursor cutoff protectedCursor objects objects outer base cap count count entries accounts accounts property property 0 0 population := by simpa only [Nat.sub_zero] using data
    exact ⟨source,false,cursor,entries,objects,property,count,keep,tailRun,True.intro,exactData.relax 0 1 (population + 1) (Nat.le_refl _) (by omega) (by omega)⟩

end InitECandidate.Solver.Mpt.AccountCode

#print axioms InitECandidate.Solver.Mpt.AccountCode.nonempty_safe
#print axioms InitECandidate.Solver.Mpt.AccountCode.branch_safe
#print axioms InitECandidate.Solver.Mpt.AccountCode.branch_dispatch
#print axioms InitECandidate.Solver.Mpt.AccountCode.branch_prefix
