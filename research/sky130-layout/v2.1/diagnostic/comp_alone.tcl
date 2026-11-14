# Exploratory. A block drawn alone, flattened and extracted as the cell is (capacitance only,
# no threshold): what its own devices and wires put between its two inputs.
#   by x1.sh, in a copy of a build folder, with BLOCK set
set block $::env(BLOCK)
load $block
select top cell
flatten ${block}_alone
load ${block}_alone
select top cell
extract all
ext2spice lvs
ext2spice cthresh 0
ext2spice -o ${block}_alone.spice
quit -noprompt
