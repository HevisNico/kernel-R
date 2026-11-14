# Exploratory economic sweep plan

Written before calculation, 2026-11-13 13:52 UTC. This is an exploratory grid,
not a v5 or v6 preregistration, confirmation study or physical campaign. It
uses no v5 seeds and changes no historical repository source. Preserve failures
and do not change this grid in response to results.

Source policy reference: boundary-cost-study at repository commit
`2cd95d2043ad2c964304a64178f3b7f1c377d671`, source SHA256
`df390c631ce3bf9b77bd506b37343b912d02d8f1f49f9eccb3fb1568444a0e43`.

Fixed: H=150, service100, dose220, latency1, maxWait40, horizon264 inclusive
initial t0 and terminal t264 probes. Capacity grid: 300,440,660,1000,1500,3000,
6600. Initial reserve=min(440,capacity), freshly measured at t0. Fixed reserve
error `(7*t+1)%5-2`, rate error `(5*t+2)%3-1`. Both channel errors are bounded
and no stochastic confidence is claimed. Probe/write price ratios: .01,.1,1,10,
represented by integer write price100 and probe prices1,10,100,1000.

Two declared scenarios: `jump` has leakage10 before t133 then140; `high` has
constant leakage140. The second prevents silently concluding universal action
identity from a low-rate prefix followed by immediate refutation: an initially
high rate can keep the optimistic candidate unrefuted while its extra margin
changes a decision. Such a difference is not automatically a learning benefit.

Compare exactly the source study's `hard_max_wait`, `optimistic_shield` and
`hard_fill` policies, parameterized only by capacity/horizon. No policy receives
future rates, truth, sensor-error schedule, or economic prices. Record action
calendar differences, first difference, revision count, probe/write counts,
unsafe periods, saturation loss and final reserve. Since these policies are
price-blind, the price axis reweights fixed action traces; it is not policy
learning or an economic optimization inside the controller.

The offline oracle knows future rates and error schedule. It minimizes each
price's total cost over the same hard-ready action family: any write or any
wait d<=40 with L-H*d>=S+H, using max(fresh,H-carried) at the next probe. Terminal
service only, no terminal inventory value. Count the initial and terminal probes
once, no command beyond the horizon. Early writes and saturation are allowed;
this is not a global physical optimum. A forward dynamic program evaluates
all four weights jointly on the same state graph. Independent scalar backward
DP/brute checks on small cases will validate it.

Outputs: complete JSON/CSV cells and all failures; finite-grid conclusions only.
If there are zero beneficial action-changing cells, say exactly that for this
grid. If an action-changing benefit appears, distinguish a fixed margin or
threshold effect from learning: no policy in this sweep learns a new rule.
