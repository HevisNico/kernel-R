"""Offline consistency checks for published phase-0 summaries, not raw validation."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

from price import analyze as price
from probe import CIRCUIT, HERE, deck, digest


def main():
    subprocess.run([sys.executable, '-B', str(HERE/'saved_evidence.py'), '--check'], check=True)
    subprocess.run([sys.executable, '-B', '-m', 'unittest', 'discover', '-s', str(HERE), '-p', 'test_*.py', '-v'], check=True)
    r = json.loads((HERE/'RESULTS.json').read_text())
    cases = []
    for name in ('probe', 'map', 'timing', 'threshold', 'leak'):
        cases.extend(json.loads((HERE/(name+'-cases.json')).read_text()))
    assert len(cases) == 16 and len({x['name'] for x in cases}) == 16
    done = [x for x in r['attempts'] if x['status'] == 'complete']
    failed = [x for x in r['attempts'] if x['status'] == 'failed']
    assert len(done) == 16 and len(failed) == 3 and len(r['attempts']) == 19
    assert sorted((x['case'] for x in done),key=lambda x:x['name']) == sorted(cases,key=lambda x:x['name'])
    for item in done:
        text, starts, stop = deck(item['case'])
        assert hashlib.sha256(text.encode()).hexdigest() == item['deck_sha256']
        assert item['source_sha256'] == {p.name:digest(p) for p in (CIRCUIT/'cell.spice',CIRCUIT/'blocks.spice',HERE/'probe.py')}
        assert item['result']['simulated_s'] == stop
        assert len(item['result']['actions']) == len(starts)
        for a in item['result']['actions']:
            assert 'gross_write_C' not in a and 'gross_write_mV' not in a
            assert a['native_slot_charge']['covered_s'] > 0
            assert a['native_slot_charge']['omitted_s'] >= -1e-15
            assert a['requested_service'] == (a['amplitude'] == 1.0)
            assert a['service_success'] == (a['pulse_fired_in_window'] if a['requested_service'] else None)
    expected = {'generated/'+x['case']['name']+'/trace.txt.gz':x['trace_sha256'] for x in done}
    assert len(r['raw_files']) == len(expected)
    assert {x['path']:x['sha256'] for x in r['raw_files']} == expected
    assert all(re.fullmatch('[0-9a-f]{64}',x['sha256']) and x['bytes']>0 for x in r['raw_files'])
    assert price(json.loads((HERE/'PRICE_INPUT.json').read_text())) == json.loads((HERE/'PRICE.json').read_text())
    print('PASS: source/deck identities, all 19 attempts, 16 waveform fingerprints and exact conditional price arithmetic')
    print('Raw waveform verification requires analyze_saved.py --check; CI does not simulate or certify physical bounds.')


if __name__ == '__main__':
    main()
