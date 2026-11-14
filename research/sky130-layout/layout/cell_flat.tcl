# The whole cell: bounding box, DRC of a flattened copy (style drc(full)), and its GDS.
load rcell
select top cell
puts "CELL_BBOX [box values]"
flatten rcell_flat
load rcell_flat
select top cell
drc style drc(full)
drc check
drc catchup
puts "FLAT_DRC_COUNT [drc list count total]"
foreach {why boxes} [drc listall why] { puts "FLAT_DRC_WHY [llength $boxes] x $why" }
load rcell
select top cell
gds write rcell.gds
quit -noprompt
