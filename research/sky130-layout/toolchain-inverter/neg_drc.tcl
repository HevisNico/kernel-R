# Negative control: a metal1 wire of 0.10 um, below the minimum width of 0.14 um, must be reported.
load inv
box 300i 0i 320i 200i
paint metal1
select top cell
drc style drc(full)
drc check
drc catchup
puts "DRC_COUNT [drc list count total]"
gds datestamp no
gds write neg.gds
quit -noprompt
