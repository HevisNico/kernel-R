# Extraction of the inverter: LVS netlist, GDS, then parasitics on the flattened cell.
load inv
select top cell
extract all
ext2spice lvs
ext2spice -o inv_lvs.spice
gds datestamp no
gds write inv.gds
# parasitics: the cell is flattened so that every wire is seen in one cell
flatten inv_pex
load inv_pex
select top cell
extract all
ext2spice lvs
ext2spice cthresh 0
ext2spice -o inv_pex_c.spice
extresist tolerance 10
extresist all
ext2spice lvs
ext2spice cthresh 0
ext2spice extresist on
ext2spice -o inv_pex_rc.spice
quit -noprompt
