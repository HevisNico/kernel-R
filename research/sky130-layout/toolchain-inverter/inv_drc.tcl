load inv
select top cell
drc style drc(full)
drc check
drc catchup
set n [drc list count total]
puts "DRC_STYLE [drc list style]"
puts "DRC_COUNT $n"
foreach {why boxes} [drc listall why] { puts "DRC_WHY [llength $boxes] x $why" }
quit -noprompt
