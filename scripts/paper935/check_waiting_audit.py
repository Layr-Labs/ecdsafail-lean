"""Validate the separate temporary audit; the strict whitelist is unchanged."""
from pathlib import Path
import re
import sys

text = Path(sys.argv[1]).read_text()
source = Path(__file__).with_name('WaitingAudit.lean').read_text()
entries = re.findall(r'^#print axioms (.+)$', source, re.M)
waiting = re.findall(r'^#waiting_prop (.+)$', source, re.M)
assert waiting and len(set(waiting)) == len(waiting)
assert len(set(entries)) == len(entries) and set(waiting) <= set(entries)
actual = re.findall(r"^'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])", text, re.M)
assert [name for name, _ in actual] == entries, 'Missing/reordered temporary axiom entries'
deps = re.findall(r'^WAITING_DEPS ([^ ]+) : (.*)$', text, re.M)
assert [name for name, _ in deps] == entries, 'Missing/reordered dependency entries'
direct = re.findall(r'^ADMITTED_DEPS ([^ ]+) : (.*)$', text, re.M)
assert [name for name, _ in direct] == entries, 'Missing direct-admission entries'
directmap = {name: set(filter(None, body.split(','))) for name, body in direct}
allowed = {'propext', 'Classical.choice', 'Quot.sound', 'sorryAx'}
depmap = {name: set(filter(None, body.split(','))) for name, body in deps}
axiommap = {}
for name, body in actual:
    axioms = set(filter(None, re.split(r'[\s,]+', body)))
    axiommap[name] = axioms
    assert axioms <= allowed, (name, axioms - allowed)
    assert depmap[name] <= set(waiting), (name, depmap[name])
    assert directmap[name] <= set(waiting), (name, 'unregistered admitted proof', directmap[name])
    assert ('sorryAx' in axioms) == bool(directmap[name]), (name, 'unattributed admission')
    assert directmap[name] <= depmap[name], (name, 'missing waiting dependency')
for suffix in ('unparkRecords2', 'unparkPre2', 'unparkPhaseDebt2', 'forward2Prefix', 'forward2Tail', 'forward2Legal', 'forward2PhaseDebt', 'forward6Prefix', 'forward6Tail', 'forward6Legal', 'forward6PhaseDebt', 'eraseRecords6', 'erasePre6', 'erasePhaseDebt6'):
    name = 'ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.' + suffix
    assert 'sorryAx' not in axiommap[name], (name, 'admitted data definition')
# Discharged finite facts must stay free of every admission.
for suffix in ("unpark2_support", "forward2_support", "forward6_support", "erase6_support",
               "forward2_wellFormed", "forward6_wellFormed", "erase6_wellFormed"):
    name = 'ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.' + suffix
    assert 'sorryAx' not in axiommap[name], (name, 'regressed finite data proof')
print('Temporary audit: entry | waiting proof dependencies | sorryAx')
for name in entries:
    print(name + ' | ' + ','.join(sorted(depmap[name])) + ' | ' + str('sorryAx' in axiommap[name]))
print('Temporary entries:', len(entries), '; registered Prop obligations:', len(waiting),
      '; admitted obligations:', sum('sorryAx' in axiommap[n] for n in waiting))
