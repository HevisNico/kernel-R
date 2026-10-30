#!/usr/bin/env python3
"""Untrusted emitter: Lean checks the resulting exact rational comparisons.

This does not prove that Python's transcendental intervals enclose the model.
Input hashes are for provenance; they are not a substitute for that soundness proof.
"""
from pathlib import Path
from fractions import Fraction
import json,hashlib,re,argparse,sys,tempfile
from cadence_evidence import generate_cadence

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parents[1]
sys.path.insert(0,str(REPO/'tools'))
from prepare_recordings import verify_bundle
OUTPUT=ROOT

def write(relative, text):
    path=OUTPUT/relative
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(text,encoding='utf-8')

def rational(x):
    if not isinstance(x,str):
        raise ValueError('certificate endpoints must be exact decimal strings')
    q=Fraction(x)
    return f'({q.numerator} / {q.denominator} : ℚ)'

def ident(x):return re.sub('[^A-Za-z0-9_]','_',x)

def certificates():
    provenance={}
    for kind in ['local','entry']:
        for box in ['eps3e-3','eps1e-1']:
            source=REPO/'results'/('reciprocal_learning' if kind=='local' else 'reciprocal_entry')/box/'certificate.json'
            data=json.loads(source.read_text())
            if len({ident(k) for k in data['bounds']}) != len(data['bounds']):
                raise ValueError('bound names collide after Lean identifier conversion')
            names=[ident(o['name']) for o in data['obligations']]
            if len(set(names)) != len(names):
                raise ValueError('obligation names collide')
            module=('Local' if kind=='local' else 'Entry')+('003' if box=='eps3e-3' else '010')
            lines=['import KernelR.Intervals','',
              '/-! Generated exact endpoint checks. Analytic enclosure soundness is NOT asserted. -/',
              f'namespace KernelR.Certificates.{module}',
              'set_option maxRecDepth 20000','set_option maxHeartbeats 4000000','']
            for name,(lo,hi) in data['bounds'].items():
                n=ident(name)
                lines.extend([f'def {n} : RationalBox := ⟨{rational(lo)}, {rational(hi)}⟩',
                  f'theorem {n}_valid : {n}.Valid := by norm_num [RationalBox.Valid, {n}]',''])
            statements=[];proofs=[]
            for ob in data['obligations']:
                if ob['relation'] not in ['strict_lt','le']:
                    raise ValueError('unsupported certificate relation')
                if ob['left'] not in data['bounds'] or ob['right'] not in data['bounds']:
                    raise ValueError('obligation refers to an unknown bound')
                n=ident(ob['name']);l=ident(ob['left']);r=ident(ob['right'])
                rel='StrictBefore' if ob['relation']=='strict_lt' else 'Before'
                prop=f'RationalBox.{rel} {l} {r}'
                statements.append(prop);proofs.append(n+'_verified')
                lines.extend([f'theorem {n}_verified : {prop} := by',
                  f'  norm_num [RationalBox.{rel}, {l}, {r}]',''])
            lines.extend(['def Obligations : Prop :=','  '+' ∧\n  '.join(statements),
              'theorem obligations_verified : Obligations := by',
              '  exact ⟨'+', '.join(proofs)+'⟩','',
              'def AllBoundsValid : Prop :=','  '+' ∧\n  '.join(ident(k)+'.Valid' for k in data['bounds']),
              'theorem all_bounds_valid : AllBoundsValid := by',
              '  exact ⟨'+', '.join(ident(k)+'_valid' for k in data['bounds'])+'⟩','',
              f'end KernelR.Certificates.{module}',
              f'#print axioms KernelR.Certificates.{module}.obligations_verified',
              f'#print axioms KernelR.Certificates.{module}.all_bounds_valid',''])
            write(f'KernelR/Certificates/{module}.lean','\n'.join(lines))
            provenance[str(source.relative_to(REPO))]={'sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
              'obligations':len(proofs),'bounds':len(data['bounds']),'module':module}
    return provenance

def adaptive():
    member='08_Adaptive_Lessons/evaluation.json'
    raw=verify_bundle()[member]
    lots=json.loads(raw)
    lines=['import KernelR.Adaptive','','/-! Exact replay of recorded finite outcomes, not a proof of their ODE origin. -/',
      'namespace KernelR.Recorded','open Adaptive','set_option maxRecDepth 100000',
      'set_option maxHeartbeats 0','',
      'structure Pupil where','  observations : List Context','  grades : List Bool','  deriving DecidableEq','',
      'def successes (xs : List Pupil) : Nat :=',
      '  ((xs.map fun x => (episode x.observations x.grades).2).filter id).length',
      'def pulses (xs : List Pupil) : Nat :=',
      '  (xs.map fun x => studentPulses (stopAfter x.observations)).sum',
      'def fixedSuccesses (xs : List Pupil) (blocks : Nat) : Nat :=',
      '  ((xs.map fun x => x.grades[blocks - 1]?.getD false).filter id).length','']
    counts={}
    for lot in lots:
        name=lot['lot'];rows=[];score=0;pulse=0
        for student in lot['students']:
            path=student['path'];contexts=[x['context'] for x in path]
            if len(path)!=4 or not all(c in [0,1,2] for c in contexts):
                raise ValueError('expected four known observation categories')
            # Check that the recorded success flag agrees with the retained probe data.
            for row in path:
                windows=row['retained']['latencies']
                correct=sum(len(w)==1 and .22<=w[0]<=.5 for w in windows)
                if len(windows)!=8 or type(row['retained']['success']) is not bool or (correct==8)!=row['retained']['success']:
                    raise ValueError('recorded grade does not match the saved probe windows')
            grades=[x['retained']['success'] for x in path]
            obs=', '.join(['.missing','.late','.notLate'][c] for c in contexts)
            rows.append('  ⟨['+obs+'], ['+', '.join(str(b).lower() for b in grades)+']⟩')
            k=contexts.index(2)+1 if 2 in contexts else 4
            score+=grades[k-1];pulse+=3*k
        lines.extend([f'def {name} : List Pupil := [',',\n'.join(rows)+']','',
          f'theorem {name}_shape : {name}.length = 160 ∧',
          f'    (∀ x ∈ {name}, x.observations.length = 4 ∧ x.grades.length = 4) := by decide',
          f'theorem {name}_successes : successes {name} = {score} := by decide',
          f'theorem {name}_pulses : pulses {name} = {pulse} := by decide',''])
        for k in range(1,5):
            v=sum(s['path'][k-1]['retained']['success'] for s in lot['students'])
            lines.append(f'theorem {name}_fixed_{k} : fixedSuccesses {name} {k} = {v} := by decide')
        counts[name]={'successful':score,'student_pulses':pulse}
    lines.extend(['','end KernelR.Recorded',
      '#print axioms KernelR.Recorded.test_successes',
      '#print axioms KernelR.Recorded.confirmation_successes',''])
    write('KernelR/Recorded.lean','\n'.join(lines))
    return {'downloads/R_Reciprocal_Prototype.zip!/'+member:{'sha256':hashlib.sha256(raw).hexdigest(),'counts':counts}}

def generate():
    info=certificates();info.update(adaptive())
    info.update(generate_cadence(REPO,write,rational,ident))
    write('evidence/GENERATED_FROM.json',json.dumps(info,indent=2)+'\n')
    return info

def main():
    global OUTPUT
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true',help='regenerate in a temporary directory and compare')
    args=parser.parse_args()
    if args.check:
        with tempfile.TemporaryDirectory() as tmp:
            OUTPUT=Path(tmp)
            info=generate()
            for path in OUTPUT.rglob('*'):
                if path.is_file():
                    relative=path.relative_to(OUTPUT)
                    if not (ROOT/relative).exists() or path.read_bytes()!=(ROOT/relative).read_bytes():
                        raise SystemExit('generated evidence differs: '+str(relative))
        print('Generated Lean evidence matches the pinned repository inputs.')
    else:
        print(json.dumps(generate(),indent=2))

if __name__=='__main__':main()
