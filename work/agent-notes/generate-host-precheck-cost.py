#!/usr/bin/env python3
"""Generate a cost proof from the fixed precheck AST; Lean must check the result.

This reads syntax to select composition lemmas and candidate prices. It neither
changes the guest nor supplies proof premises or a whole-program bound.
"""
from collections import Counter
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
source = (ROOT / 'Guest/SoftwareAst.lean').read_text()
fragment = source.split('def guestFn_precheck_host_ssz_header :', 1)[1]
fragment = fragment.split('\ndef guestFn_', 1)[0]
tokens = re.findall(r'"(?:\\.|[^"\\])*"|[()[\],]|[^\s()[\],]+', fragment.split('body :=', 1)[1])


def parse(index):
    token = tokens[index]
    if token not in ('(', '['):
        return token, index + 1
    closing = ')' if token == '(' else ']'
    children = []
    index += 1
    while tokens[index] != closing:
        node, index = parse(index)
        children.append(node)
    return (token, children), index + 1


def items(node):
    assert isinstance(node, tuple), node
    return node[1]


calls = Counter()


def proof(node):
    if node == 'Prog.skip':
        return 0, '(ClockCost.skip code)'
    values = items(node)
    head = values[0]
    if head == 'Prog.seq':
        a, left = proof(values[1])
        b, right = proof(values[2])
        return a + b, f'(ClockCost.sequence code _ _ {a} {b}\n  {left}\n  {right})'
    if head == 'Prog.ite':
        a, left = proof(values[2])
        b, right = proof(values[3])
        return max(a, b), f'(ClockCost.conditional code _ _ _ {a} {b}\n  {left}\n  {right})'
    if head == 'Prog.dec':
        price, term = proof(values[-1])
        return price, f'(ClockCost.declared code _ _ _ _ {price}\n  {term})'
    if head == 'Prog.return':
        return 0, '(ClockCost.returned code _)'
    if head == 'Prog.store':
        return 0, '(ClockCost.store code _ _)'
    if head == 'Prog.shMemLoad':
        return 0, '(ClockCost.shared_load code _ _ _ _)'
    if head == 'Prog.call':
        function = json.loads(values[2])
        calls[function] += 1
        if function == 'ssz_fail':
            return 1, ('(ClockCost.call_body code (some none) _ _ SszFail.formals SszFail.body .one 0\n'
                       '  (SszCurrentCode.fail_installed code installed) (Offsets.failure_body_cost code))')
        assert function == 'ssz_check_offsets', function
        arguments = [v for v in items(values[3]) if v != ',']
        count_arg = items(arguments[1])
        assert count_arg[0] == 'Exp.const', count_arg
        literal = items(count_arg[1])
        assert literal[:2] == ['BitVec.ofNat', '64'], literal
        count = int(literal[2])
        assert count in (2, 3, 4), count
        return 3 * count + 2, f'(Offsets.call_fixed_count_cost code installed {count} (by decide) _ _ _)'
    if head == 'Prog.decCall':
        function = json.loads(values[3])
        calls[function] += 1
        price, term = proof(values[-1])
        if function == 'host_input_byte':
            callee, body_price, entry, bound = 'Byte', 0, 'byte_installed code installed', 'Byte.body_cost code'
        else:
            assert function == 'host_input_le32', function
            callee, body_price, entry, bound = 'Le32', 4, 'le32_installed code installed', 'Le32.body_cost code installed'
        return body_price + price + 1, (
            f'(ClockCost.scoped_body code _ _ _ _ _ {callee}.formals {callee}.body .one {body_price} {price}\n'
            f'  ({entry}) ({bound})\n  {term})')
    raise ValueError(f'Unsupported fixed precheck statement: {head}')


tree, end = parse(0)
price, term = proof(tree)
output = ROOT / 'submission/InitECandidate/Solver/Input/HostPrecheckCost.lean'
content = f'''import InitECandidate.Solver.Input.HostInputCost
import InitECandidate.Solver.Input.OffsetsFixedCountCall

-- Generated from the actual software precheck by generate-host-precheck-cost.py.
-- The candidate price is justified only by a successful Lean build of this file.
namespace InitECandidate.Solver.Input.HostPrecheck
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString GasBudget.OriginalCodeEnvironment

def body : ProgHOL 64 := match Guest.Software.guestFn_precheck_host_ssz_header with
  | .function fn => progToHOL fn.body | _ => .skip

set_option maxRecDepth 100000 in
theorem precheck_installed (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "precheck_host_ssz_header") = some ([], body, .one) := by
  have found := OriginalCode.indexed code installed 182
    (originalEntry Guest.Software.guestFn_precheck_host_ssz_header) (by rfl)
  simpa only [originalEntry, declToHOL, funDeclToHOL, body,
    Guest.Software.guestFn_precheck_host_ssz_header, shapeToHOL, List.map_nil] using found

set_option maxRecDepth 100000 in
/-- All actual precheck outcomes, including failed host reads, failed stores
and decoder exceptions. This counts source call/loop ticks, not target steps. -/
theorem body_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code body {price} := by
  simp only [body, Guest.Software.guestFn_precheck_host_ssz_header, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  exact {term}

theorem call_cost (code) (installed : OriginalCode.Installed code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    ClockCost.Bound code (.call (LocalEffects.callInfo destination)
      (ofString "precheck_host_ssz_header") arguments) {price + 1} :=
  ClockCost.call_body code destination _ arguments [] body .one {price}
    (precheck_installed code installed) (body_cost code installed)

end InitECandidate.Solver.Input.HostPrecheck

#print axioms InitECandidate.Solver.Input.HostPrecheck.precheck_installed
#print axioms InitECandidate.Solver.Input.HostPrecheck.body_cost
#print axioms InitECandidate.Solver.Input.HostPrecheck.call_cost
'''
if not output.exists() or output.read_text() != content:
    output.write_text(content)
report = {'source': 'Guest/SoftwareAst.lean', 'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
          'function': 'precheck_host_ssz_header', 'candidate_source_clock_price': price,
          'syntax_call_occurrences': dict(calls), 'lean_build_required': True,
          'scope': 'Proof generation only; not proof validation or a whole-program bound.'}
(ROOT / 'work/agent-notes/host-precheck-cost-generation.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
