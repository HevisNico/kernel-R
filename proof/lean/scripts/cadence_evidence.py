"""Emit bounded-size Lean modules for cadence endpoint checks and trace replay.

The trace is input data. Its compatibility with all hybrid trajectories is not
asserted by this emitter or the generated Lean theorems.
"""
import hashlib
import json

CHUNK_SIZE = 160
CASE_NAMES = {
    'weak_full_ERROR': 'weakError',
    'strong_firing': 'fire',
    'protected_MARK_only': 'markOnly',
    'protected_MARK_then_full_ERROR': 'markThenError',
}
STAGES = [
    ('bTeaching', 'B.teach_', 3, 0, 16, 16, 0, 0),
    ('cTeaching', 'Cteach.teach_', 0, 0, 16, 14, 1, 1),
    ('cFast', 'C.fast_', 0, 0, 25, 20, 4, 2),
    ('bFast', 'B.fast_', 3, 0, 20, 18, 1, 2),
    ('aFast', 'A.fast_', 3, 0, 18, 16, 1, 2),
]


def chunks(xs):
    return [xs[i:i + CHUNK_SIZE] for i in range(0, len(xs), CHUNK_SIZE)]


def header(namespace, imports):
    return ['import ' + x for x in imports] + [
        '', '/-! Generated exact evidence checks, not hybrid-flow soundness. -/',
        'namespace ' + namespace,
        'set_option maxRecDepth 20000', 'set_option maxHeartbeats 4000000', '',
    ]


def conjunction(lines, name, statements, proofs):
    if not statements:
        raise ValueError('empty evidence conjunction')
    lines += ['def ' + name + ' : Prop :=', '  ' + ' ∧\n  '.join(statements),
              'theorem ' + name + '_verified : ' + name + ' := by',
              '  exact ⟨' + ', '.join(proofs) + '⟩' if len(proofs) > 1 else '  exact ' + proofs[0], '']


def trace_module(data, module, write):
    trace = data['pulse_trace']
    labels = [row['pulse'] for row in trace]
    if len(labels) != len(set(labels)):
        raise ValueError('duplicate pulse labels')
    if any(row['case'] not in CASE_NAMES for row in trace):
        raise ValueError('unknown cadence pulse case')
    ns = 'KernelR.CadenceRecorded.' + module
    lines = header(ns, ['KernelR.Cadence', 'KernelR.Protocol']) + ['open KernelR.Cadence', '']
    accounted = 0
    for name, label, g, m, n, fires, errors, marks in STAGES:
        rows = [row for row in trace if row['pulse'].startswith(label)]
        accounted += len(rows)
        lines += [f'def {name} : List RecordedStep := [']
        emitted = []
        for row in rows:
            if type(row['gain_doses']) is not int or type(row['protected_marks']) is not int:
                raise ValueError('cadence counters must be natural integers')
            if min(row['gain_doses'], row['protected_marks']) < 0:
                raise ValueError('negative cadence counter')
            emitted.append(f"  ⟨.{CASE_NAMES[row['case']]}, {row['gain_doses']}, {row['protected_marks']}⟩")
        lines += [',\n'.join(emitted) + ']', '',
                  f'theorem {name}_counters : checkSteps {g} {m} {name} = true := by decide',
                  f'theorem {name}_counts : {name}.length = {n} ∧ emissions {name} = {fires} ∧',
                  f'    errors {name} = {errors} ∧ marks {name} = {marks} := by decide', '']
    if accounted != len(trace):
        raise ValueError('unrecognized pulse trace stage')
    lines += [
        'theorem routed_input_counts : bFast.length = emissions cFast ∧',
        '    aFast.length = emissions bFast ∧ cTeaching.length = emissions bTeaching := by decide',
        'theorem all_input_cases : bTeaching.length + cTeaching.length + cFast.length +',
        '    bFast.length + aFast.length = 95 := by decide',
        'theorem total_emissions_through_789_9 :',
        '    KernelR.fireCount (KernelR.aWarmup ++ KernelR.aTeaching ++ KernelR.feedbackWord 13) +',
        '      emissions aFast = 54 ∧',
        '    KernelR.fireCount (KernelR.bWarmup ++ KernelR.feedbackWord 16) +',
        '      emissions bTeaching + emissions bFast = 61 ∧',
        '    emissions cTeaching + emissions cFast = 34 := by decide',
        '', 'end ' + ns, '',
    ]
    write(f'KernelR/CadenceRecorded/{module}.lean', '\n'.join(lines))


def generate_cadence(repo, write, rational, ident):
    provenance = {}
    for box, suffix in [('eps3e-3', '003'), ('eps1e-1', '010')]:
        source = repo / 'results/reciprocal_cadence' / box / 'certificate.json'
        data = json.loads(source.read_text())
        bounds = list(data['bounds'].items())
        obs = data['obligations']
        if len({ident(k) for k, _ in bounds}) != len(bounds):
            raise ValueError('colliding cadence bound names')
        if len({ident(o['name']) for o in obs}) != len(obs):
            raise ValueError('colliding cadence obligation names')
        module = 'Cadence' + suffix
        ns = 'KernelR.Certificates.' + module
        imports, bound_props, bound_proofs = [], [], []
        owner = {}
        for i, group in enumerate(chunks(bounds)):
            part = f'Bounds{i:02}'
            full = ns + '.' + part
            imports.append(full)
            lines = header(ns, ['KernelR.Intervals'])
            for name, (lo, hi) in group:
                n = ident(name)
                owner[name] = full
                lines += [f'def {n} : RationalBox := ⟨{rational(lo)}, {rational(hi)}⟩',
                          f'theorem {n}_valid : {n}.Valid := by norm_num [RationalBox.Valid, {n}]', '']
            prop = f'Bounds{i:02}Valid'
            conjunction(lines, prop, [ident(k) + '.Valid' for k, _ in group],
                        [ident(k) + '_valid' for k, _ in group])
            bound_props.append(prop)
            bound_proofs.append(prop + '_verified')
            write(f'KernelR/Certificates/{module}/{part}.lean', '\n'.join(lines + ['end ' + ns, '']))
        ob_props, ob_proofs = [], []
        for i, group in enumerate(chunks(obs)):
            part = f'Checks{i:02}'
            needed = set()
            for ob in group:
                if ob['relation'] != 'strict_lt':
                    raise ValueError('cadence must contain strict obligations')
                needed.update([owner[ob['left']], owner[ob['right']]])
            lines = header(ns, sorted(needed))
            statements, proofs = [], []
            for ob in group:
                name, left, right = ident(ob['name']), ident(ob['left']), ident(ob['right'])
                statement = f'RationalBox.StrictBefore {left} {right}'
                lines += [f'theorem {name}_verified : {statement} := by',
                          f'  norm_num [RationalBox.StrictBefore, {left}, {right}]', '']
                statements.append(statement)
                proofs.append(name + '_verified')
            prop = f'Checks{i:02}Valid'
            conjunction(lines, prop, statements, proofs)
            ob_props.append(prop)
            ob_proofs.append(prop + '_verified')
            imports.append(ns + '.' + part)
            write(f'KernelR/Certificates/{module}/{part}.lean', '\n'.join(lines + ['end ' + ns, '']))
        lines = header(ns, imports)
        conjunction(lines, 'Obligations', ob_props, ob_proofs)
        conjunction(lines, 'AllBoundsValid', bound_props, bound_proofs)
        lines += ['end ' + ns,
                  f'#print axioms {ns}.Obligations_verified',
                  f'#print axioms {ns}.AllBoundsValid_verified', '']
        write(f'KernelR/Certificates/{module}.lean', '\n'.join(lines))
        trace_module(data, module, write)
        provenance[str(source.relative_to(repo))] = {
            'sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
            'obligations': len(obs), 'bounds': len(bounds),
            'pulse_cases': len(data['pulse_trace']), 'module': module,
        }
    return provenance
