# Networks of trained cells

[Back to the native package](../README.md)

## Networks of any number of trained cells

[FamilyProduct.lean](FamilyProduct.lean) removes the limit of two cells.

The earlier product, `ParameterExecution.independentPair`, weaves two
one-cell executions. Here `Snapshot.family` is the state of a network of
`n` cells, each with its own parameters, and `family_execution` weaves
`n` one-cell executions with common start and end dates into one
execution of that network. Each cell keeps its ordered FIRE dates. The
proof takes the next jump of any cell when there is one, and otherwise
cuts every flow at the earliest flow end. `family_jump` lifts each of the
nine kinds of jump to the network.

- `trained_network`: for any positive `n`, `n` trained cells with their
  own parameters, start gains, FIRE levels, pulse trains and read dates.
  In every complete run of the network, the last FIRE of each cell is
  its read FIRE, later than 0.239 units after its first read pulse and
  no later than 0.256 units after its second. For any two cells read
  with an offset of −0.3, 0 or +0.3 units, the two dates are closer than
  3/20 exactly when the offset is zero.
- `trained_network_witness`: for any positive `n`, `n` copies of the
  explicit cell satisfy the hypotheses. Every cell fires its read in its
  window and any two cells are accepted together.

In this module the cells are independent: no cell sends a pulse to
another. The next modules add wires.

## Wires between cells

[RoutedProduct.lean](RoutedProduct.lean) composes cells joined by wires,
in the parameterized semantics.

Each cell keeps a one-cell run with an empty router. In that run its
queue already holds the pulses that other cells will send it. In the
network a pulse enters the queue only at the FIRE that sends it.
`routed_execution` weaves the one-cell runs into one run of the routed
network. Its hypotheses are:

- every wire has a strictly positive delay;
- the queues balance at the start: the queues of the cells are the queue
  of the network plus what the FIRE dates of the cells will send.

The proof keeps that balance as a multiset equation through every move.
A FIRE moves its deliveries from the promised side to the queue. An
arrival finds its delivery in the queue, because every delivery still
promised is due later. Each cell keeps its ordered FIRE dates. The one-
cell theorems of the earlier modules are used unchanged.

## Read pulses in either order

[FreeRead.lean](FreeRead.lean) separates the training of a cell from its
read.

- `rest_wait`: a cell at rest stays at rest for as long as no pulse
  arrives. No gain moves.
- `OpenCell`: a trained cell without its read pulses. Its hypotheses are
  those of `TrainedCell` without the read dates. After `horizon` the
  cell is trained and at rest.
- `OpenCell.read`: two read pulses arrive after `horizon`, one on each
  trained port, at most a quarter of a unit apart, **in either order**.
  The cell fires its read later than 0.239 units after the first pulse
  and no later than 0.256 units after the second. Every FIRE of training
  comes before `horizon`, which is a fixed date.

## Composition along forward wires

[AcyclicNetwork.lean](AcyclicNetwork.lean) proves one composition theorem
for every network whose wires go from a cell to a cell of higher index.

`acyclic_network` takes, for each cell, a description of its FIRE dates
that may mention the FIRE dates of the cells before it. Its hypothesis is
local: a cell fed by cells that follow their descriptions has a run to
rest that follows its own. The pulses it receives are computed from the
router by `incoming`. The conclusion is global: the network has a
complete run, every cell follows its description, and the FIRE dates are
the same in every complete run. The cells are treated one after the
other, in index order, and `routed_execution` weaves their runs.

## Networks of trained cells of any depth

[WiredNetwork.lean](WiredNetwork.lean) applies the composition theorem to
trained cells.

- `ReadInput`: each of the two read pulses of a cell comes from a source
  at a fixed date, or from the read FIRE of an earlier cell through a
  wire with a positive delay.
- `trained_wired_network`: any number of cells, any wiring of that kind.
  The hypothesis `admissible` says that, whenever the earlier cells fire
  their reads in their windows, the two read pulses of a cell arrive
  after its training and at most a quarter of a unit apart. Their order
  is free. In every complete run, each cell fires its read later than
  0.239 units after its first read pulse and no later than 0.256 units
  after its second, after the FIRE events of its own training.
- `trained_chain_witness`: for every `n`, a chain of `n` copies of the
  explicit cell. A source reads the first cell at date 968. The read
  FIRE of each cell reads the two ports of the next one, one unit later.
  In every complete run, each cell fires its read between 1.239 and
  1.256 units after the cell before it.

Limits:

- **Width of the windows.** The theorem bounds each read FIRE inside a
  window of 0.017 units plus the distance between the two arrivals. On a
  path where the two ports of a cell are fed by different cells, the
  windows widen with the depth, and the hypothesis `admissible` needs
  them to stay within a quarter of a unit. In the chain both ports of a
  cell are fed by the same FIRE, so the depth is free.
- **Gates.** Each wire carries the FIRE events after a fixed date only.
  That date is the end of the training of the sending cell.
- **Every read pulse arrives.** A cell that may or may not receive a
  read pulse is not covered by `trained_wired_network`. The next modules
  cover it.

## Report windows in the parameterized semantics

[SignalNetwork.lean](SignalNetwork.lean) is the parameterized counterpart
of the report windows of the scheduled circuits.

Each cell has a window `(lo, hi]`. A FIRE in the window is a signal. A
signal sends pulses at fixed dates to later cells, as a `ReportWire`
does in the nominal circuits. `Signal lo hi l b` says that the FIRE dates
`l` carry the bit `b`: for a true bit the last FIRE is in the window and
the others are before it, for a false bit every FIRE is before the
window.

`signal_network` takes a bit for each cell. Its hypothesis is local: a
cell that receives the pulses of the wires whose senders have a true bit
has a run to rest that carries its own bit. The conclusion is a complete
run of the network in which every cell carries its bit, with the same
FIRE dates in every complete run. A cell may receive all, some or none
of its pulses.
