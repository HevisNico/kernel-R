v {xschem version=3.4.4 file_version=1.2}
G {}
K {}
V {}
S {}
E {}
N 100 -130 100 -70 {lab=y}
N 60 -160 60 -40 {lab=a}
N 40 -100 60 -100 {lab=a}
N 100 -100 160 -100 {lab=y}
N 100 -220 100 -190 {lab=vdd}
N 100 -10 100 20 {lab=vss}
N 100 -160 120 -160 {lab=vdd}
N 120 -220 120 -160 {lab=vdd}
N 100 -220 120 -220 {lab=vdd}
N 100 -40 120 -40 {lab=vss}
N 120 -40 120 20 {lab=vss}
N 100 20 120 20 {lab=vss}
C {sky130_fd_pr/pfet_01v8.sym} 80 -160 0 0 {name=xmp
L=0.15
W=1
nf=1
mult=1
model=pfet_01v8
spiceprefix=X
}
C {sky130_fd_pr/nfet_01v8.sym} 80 -40 0 0 {name=xmn
L=0.15
W=0.42
nf=1
mult=1
model=nfet_01v8
spiceprefix=X
}
C {ipin.sym} 40 -100 0 0 {name=p1 lab=a}
C {opin.sym} 160 -100 0 0 {name=p2 lab=y}
C {iopin.sym} 100 -220 3 0 {name=p3 lab=vdd}
C {iopin.sym} 100 20 1 0 {name=p4 lab=vss}
