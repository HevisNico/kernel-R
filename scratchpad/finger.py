import sys; sys.path.insert(0, ".")
import instrument, lcal2, spec as specmod, session as sess
s = specmod.load("specs/xor3.json"); cfg, _ = lcal2.config("config_inverter_c5.json")
ses = sess.Session(sys.argv[1], instrument.deck_text(s, cfg), cfg, seed=int(sys.argv[2]))
names = ["v(ibm)", "@m.xcmpm.xm1.msky130_fd_pr__pfet_01v8_lvt[vth]", "@m.xcmpm.xm2.msky130_fd_pr__pfet_01v8_lvt[vth]",
         "@m.xmh1.msky130_fd_pr__nfet_01v8[vth]", "@m.xmj1.msky130_fd_pr__pfet_01v8[vth]"]
ses.cmd("op")
for j in (0, 1):
    vals = []
    for n in names:
        q = n.replace("v(", f"v(xn{j}.") if n.startswith("v(") else n.replace("@m.", f"@m.xn{j}.")
        vals.append(ses.cmd(f"print {q}").strip())
    print(f"xn{j}", vals)
ses.close()
