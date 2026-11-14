# Negative control of the DRC: a copy of the cell with one metal1 wire drawn 0.1 um from another.
load rcell
select top cell
flatten rcell_neg
load rcell_neg
box 0i -400i 200i -360i
paint metal1
box 0i -340i 200i -300i
paint metal1
select top cell
drc style drc(full)
drc check
drc catchup
puts "NEG_DRC_COUNT [drc list count total]"
quit -noprompt
