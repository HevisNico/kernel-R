"""Inert, paired proof mutations; no simulation or scenario generation."""
MUTATIONS = [
    ('weaken_repair_guard',
     'def Ready (lower : Int) : Prop := 250 ≤ lower ∧ lower ≤ 660',
     'def Ready (lower : Int) : Prop := 249 ≤ lower ∧ lower ≤ 660'),
    ('authorize_two_ticks_too_early',
     'else if policy = .early ∧ 550 ≤ lower then .wait2',
     'else if policy = .early ∧ 549 ≤ lower then .wait2'),
    ('undercharge_carried_loss',
     '| .wait1 => lower - 150',
     '| .wait1 => lower - 149'),
    ('understate_sensor_error',
     'if delivered then min 660 (report - 2 + 220) else report - 2',
     'if delivered then min 660 (report - 1 + 220) else report - 1'),
    ('upper_rate_endpoint_refuses',
     'let action := if rateReport - 1 > 150 then .refuse else choose policy lower upper',
     'let action := if rateReport + 1 > 150 then .refuse else choose policy lower upper'),
]
