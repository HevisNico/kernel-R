"""Numbers of the layout generator. Lengths are in units of 5 nm, the grid of SKY130.

The routing grid has one pitch on every layer. A wire is as wide as the pad of a via, so a wire
and a via on neighbouring tracks keep the spacing of their layer by construction:

    pitch - width >= spacing        metal1: 136 - 68 = 68 >= 28
                                    metal2: 136 - 76 = 60 >= 28
                                    metal3, metal4: 136 - 76 = 60 >= 60
"""
import os
from pathlib import Path

HERE = Path(__file__).resolve().parent
BUILD = Path(os.environ.get("LAYOUT_BUILD", HERE / "build"))
PDK = Path(os.environ.get("PDK_ROOT", "/usr/local/share/pdk")) / "sky130A"
MAGICRC = PDK / "libs.tech" / "magic" / "sky130A.magicrc"
NETGEN_SETUP = PDK / "libs.tech" / "netgen" / "sky130A_setup.tcl"

UM = 200                    # units per micrometre
P = 136                     # routing pitch, 0.68 um
LAYERS = ["m1", "m2", "m3", "m4"]
WIRE = {"m1": 68, "m2": 76, "m3": 76, "m4": 76}
SPACE = {"m1": 28, "m2": 28, "m3": 60, "m4": 60}
WIDE_SPACE = {"m1": 56, "m2": 56, "m3": 80, "m4": 80}      # to a shape wider than 3 um
WIDE = 600
MIN_AREA = {"m1": 83000 / 25, "m2": 67600 / 25, "m3": 240000 / 25, "m4": 240000 / 25}   # in units^2
VIAS = ["v1", "v2", "v3"]                                   # v1 joins m1 and m2, and so on
CUT = {"v1": 52, "v2": 56, "v3": 64}                        # painted size of a contact
CUT_SPACE = {"v1": 12, "v2": 24, "v3": 16}
MAGIC = {"m1": "metal1", "m2": "metal2", "m3": "metal3", "m4": "metal4",
         "v1": "via1", "v2": "via2", "v3": "via3", "li": "locali", "mcon": "viali",
         "nwell": "nwell", "capm": "mimcap", "capc": "mimcapcontact"}
