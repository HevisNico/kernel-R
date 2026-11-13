# Footprints of the parts of one R cell as drawn by the SKY130 device generator of Magic.
# Each part is drawn alone, with the default options of the generator (guard ring included for
# transistors), and its bounding box and DRC count are printed. Nothing is wired.
proc one {group dev count args} {
    global total
    load fp_[incr ::k] -force
    box 0 0 0 0
    eval [list magic::gencell sky130::sky130_fd_pr__$dev d1] $args
    select top cell
    set b [box values]
    set w [expr {([lindex $b 2] - [lindex $b 0]) * 0.005}]
    set h [expr {([lindex $b 3] - [lindex $b 1]) * 0.005}]
    drc style drc(full); drc check; drc catchup
    set a [expr {$w * $h}]
    set total($group) [expr {[info exists total($group)] ? $total($group) + $a * $count : $a * $count}]
    puts "FP $group | $dev | $args | x$count | [format %.2f $w] x [format %.2f $h] um | [format %.1f $a] um2 each | [format %.0f [expr {$a * $count}]] um2 | DRC [drc list count total]"
    foreach {why boxes} [drc listall why] { puts "FP    why: [llength $boxes] x $why" }
}
set k 0
# transistors of the analog blocks: total width split into fingers of at most 10 um
one mos nfet_01v8      4 w 10 l 2.5 nf 4
one mos pfet_01v8      2 w 8 l 2 nf 4
one mos pfet_01v8      6 w 8 l 2 nf 2
one mos pfet_01v8      7 w 8 l 2 nf 1
one mos pfet_01v8_lvt  2 w 8 l 4 nf 2
one mos pfet_01v8_lvt  4 w 8 l 1 nf 2
one mos pfet_01v8_lvt  4 w 4 l 1 nf 1
one mos nfet_01v8      4 w 4 l 2 nf 1
one mos nfet_01v8      2 w 8 l 1 nf 2
one mos nfet_01v8      4 w 0.42 l 8 nf 1
one mos nfet_01v8      6 w 2 l 1 nf 1
one mos nfet_01v8      3 w 2 l 0.5 nf 1
one mos pfet_01v8      2 w 2 l 0.5 nf 1
one mos nfet_01v8     14 w 1 l 0.15 nf 1
one mos pfet_01v8      6 w 2 l 0.15 nf 1
# resistors: 8 Mohm as 20 strips of 70 um of the 2 kohm/square poly, 100 kohm, 4 kohm
one res res_xhigh_po_0p35 1 l 70 nx 20
one res res_xhigh_po_0p35 5 l 17.5
one res res_high_po_0p35  2 l 4.4
# MIM capacitors: the largest plate the generator accepts is 30 um x 30 um
one mim_unit30   cap_mim_m3_1 1 w 30 l 30
one mim_4x4      cap_mim_m3_1 1 w 30 l 30 nx 4 ny 4
one mim2_4x4     cap_mim_m3_2 1 w 30 l 30 nx 4 ny 4
one mim_unit14   cap_mim_m3_1 1 w 14.14 l 14.14
one mim_9x9      cap_mim_m3_1 1 w 14.14 l 14.14 nx 9 ny 9
one mim_unit10   cap_mim_m3_1 1 w 10 l 10
one mim_stackopt cap_mim_m3_1 1 w 30 l 30 stack 2
foreach g [lsort [array names total]] { puts "FP_TOTAL $g [format %.0f $total($g)] um2" }

# Two MIM types drawn on top of each other, as a first attempt at a stacked capacitor
load stk -force
box 0 0 0 0
magic::gencell sky130::sky130_fd_pr__cap_mim_m3_1 ca w 30 l 30
magic::gencell sky130::sky130_fd_pr__cap_mim_m3_2 cb w 30 l 30
select top cell
set b [box values]
drc style drc(full); drc check; drc catchup
puts "FP stack_overlap | [format %.2f [expr {([lindex $b 2]-[lindex $b 0])*0.005}]] x [format %.2f [expr {([lindex $b 3]-[lindex $b 1])*0.005}]] um | DRC [drc list count total]"
extract all
ext2spice lvs
ext2spice -o stk.spice
quit -noprompt
