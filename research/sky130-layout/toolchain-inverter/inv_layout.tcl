# Layout of the inverter of research/circuit/blocks.spice (pfet 1/0.15, nfet 0.42/0.15).
# Coordinates are Magic internal units of this technology setup: 1 unit = 5 nm.
proc place {inst dev x y args} {
    eval [list magic::gencell sky130::$dev $inst] $args
    set master ""
    foreach c [cellname list allcells] { if {[string match ${dev}_* $c]} { set master $c } }
    select cell $inst
    delete
    box position ${x}i ${y}i
    getcell $master child 0 0
    identify $inst
}
load inv -force
box 0i 0i 0i 0i
place xmn sky130_fd_pr__nfet_01v8 0 0   w 0.42 l 0.15 nf 1 guard 1 topc 1 botc 0
place xmp sky130_fd_pr__pfet_01v8 0 520 w 1    l 0.15 nf 1 guard 1 topc 0 botc 1
# input: metal1 from the gate contact of the nfet to the gate contact of the pfet
box -29i 43i 29i 415i
paint metal1
# output: metal1 from the two drains, routed on the left of the guard rings
box -260i -60i -21i 0i
paint metal1
box -260i -60i -200i 580i
paint metal1
box -260i 520i -21i 580i
paint metal1
# sources to their guard rings on local interconnect: vss and vdd
box 61i -61i 141i -1i
paint locali
box 61i 520i 141i 580i
paint locali
# ports
box -10i 200i 10i 220i
label a FreeSans 20 0 0 0 c metal1
port make 1
box -240i 200i -220i 220i
label y FreeSans 20 0 0 0 c metal1
port make 2
box -10i 741i 10i 761i
paint locali
label vdd FreeSans 20 0 0 0 c locali
port make 3
box -10i -178i 10i -158i
paint locali
label vss FreeSans 20 0 0 0 c locali
port make 4
select top cell
puts "BBOX [box values]"
writeall force
quit -noprompt
