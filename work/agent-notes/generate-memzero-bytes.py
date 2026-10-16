#!/usr/bin/env python3
"""Instantiate the checked word-loop proof layout for the fixed eight-byte body.

Generate a linear sequence of memory-store result splits: a failed store exits
immediately, and only a successful memory value is passed to the next store.
Generated proofs still require an ordinary Lean build and axiom check.
"""
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'submission/InitECandidate/Solver/GuestWork'
s = (OUT / 'MemzeroWord.lean').read_text()
s = s.replace('MemzeroWord','MemzeroBytes').replace('aligned eight-byte','unaligned eight-byte')
s = s.replace('def body : HolProg 64 := NamedBody78_100','def body : HolProg 64 := NamedBody78_202')
s = s.replace('nodes body = 29','nodes body = 83').replace('Work body source 31','Work body source 85')
a = s.index('  by_cases less :')
b = s.index('\nend InitECandidate',a)
body_names = ', '.join(f'NamedBody78_{n}' for n in range(120,203))
semantics = '''evaluateSeq, evaluate_skip, evaluate_ite, evaluate_tick,
      evaluate_inst, evaluate_continue, evaluate_break,
      StackSemStateOps.getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
      hbase, hlength, hindex, less, zero, wordSemWordCmp, wordCmpHOL,
      StackSemInst.instHOL, instInteger, assign, wordExp, wordOpHOL, wordOp,
      setVar, decClock, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL'''
def finish(indent, stores=()):
    facts = ', '.join([body_names, semantics] + list(stores))
    lines = f'''simp [body, {facts}] at execution
rcases execution with ⟨rfl, rfl⟩
simp_all [StackSemControl.contLoop, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]'''
    return '\n'.join(' '*indent + line for line in lines.splitlines()) + '\n'
proof = '  by_cases less : length < index + 8#64\n'
proof += '  · by_cases zero : source.clock = 0\n'
proof += '    all_goals\n' + finish(6)
proof += '  · by_cases zero : source.clock = 0\n'
proof += '    ·\n' + finish(6)
def stores(n, indent):
    memory = 'source.memory' if n == 0 else f'memory{n-1}'
    address = '(index + base)' if n == 0 else f'(index + base + {n}#64)'
    out = ' '*indent + f'cases store{n} : memStoreByteAuxExact {memory} source.mdomain source.be {address} 0#8 with\n'
    out += ' '*indent + '| none =>\n' + finish(indent+2, [f'store{k}' for k in range(n+1)])
    out += ' '*indent + f'| some memory{n} =>\n'
    if n == 7:
        out += finish(indent+2,[f'store{k}' for k in range(8)])
    else:
        out += stores(n+1,indent+2)
    return out
proof += '    ·\n' + stores(0,6)
s = s[:a]+proof+s[b:]
(OUT/'MemzeroBytes.lean').write_text(s)
print('Generated actual NamedBody78_202 register-outcome proof; requires Lean checking')
