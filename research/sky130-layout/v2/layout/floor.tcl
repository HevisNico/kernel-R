# The switch of 1 um by 0.15 um drawn alone, with its exits: what its own gate exit has to its
# source and drain exits (the device floor of ../PREDICTION.md).
load dev_nfet_01v8_l0p15_w1
select top cell
flatten dev_nfet_01v8_l0p15_w1_fl
load dev_nfet_01v8_l0p15_w1_fl
select top cell
extract all
ext2spice lvs
ext2spice cthresh 0
ext2spice -o dev_nfet_01v8_l0p15_w1_fl.spice
quit -noprompt
