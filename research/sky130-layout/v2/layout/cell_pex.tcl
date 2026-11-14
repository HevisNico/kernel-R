# Parasitics of the cell: the cell is flattened so that every wire is seen in one cell, then
# extracted with capacitance only (decision D5). Magic names each net by a label of the hierarchy,
# written INSTANCE.INSTANCE.NET, which is how ngspice names the nodes of cell.spice.
load rcell
select top cell
flatten rcell_pex
load rcell_pex
select top cell
extract all
ext2spice lvs
ext2spice cthresh 0
ext2spice -o rcell_pex_c.spice
quit -noprompt
