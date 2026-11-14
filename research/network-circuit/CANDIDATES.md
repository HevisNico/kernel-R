# Candidate predictions for the decisive experiment

Phase 0, exploratory. **None of the network runs below has been made.** The
only network runs that exist are the two of [`NETWORK.json`](NETWORK.json):
nominal cells, 27 C, no noise, calendars N and L. Everything here is a
proposal for the owner to choose from, change or reject before a
preregistration. Numbers quoted are from one cell alone
([`PERCELL.json`](PERCELL.json)) or from earlier campaigns, as said.

## The form a prediction would take

For each network instance, before its run:

1. measure each cell alone, on the deck of the network, with the other cells
   idle: per port, the gap at the preset, the dose, the help of a recent
   pulse at the spacings the calendar uses, and the noise of a read;
2. apply the rule of [`EXPECTATION.md`](EXPECTATION.md): reserve, plus help,
   against zero;
3. state the **learned state**: the write count of every port, the decision
   word of every port, the FIRE count of every cell, the routed pulses;
4. state, for every read, its **room**: how far the score is from zero after
   the help and after `k` standard deviations of noise. A port whose rooms
   are all positive is predicted; a port with a room below zero is declared
   "no prediction" before the run, as the certification campaigns do;
5. run the network once.

## Candidates

| | Network run, not made | What is predicted | Per-cell measures needed first | What it tests |
|---|---|---|---|---|
| K1 | Two cells with mismatch (SKY130 mismatch models, several seeds), calendar L, no noise | Per instance and per port: the need, hence the write count, from that port's own gap. Needs from 2 to 5 are expected (layout study: 16 ports, needs 2 to 5), so the four ports of an instance differ and the wires stop at different pulses | gap and dose of the four ports; help at 8 units, per cell | the core claim: learned state from measured margins, on cells that are not the one the rule was built on |
| K2 | The same instances with noise, several repetitions each | The same counts, for the ports whose rooms exceed `k` standard deviations; for the others, no prediction, or a stated probability of the other count | read noise per port, as an equivalent reserve | bounded read errors against real noise (departure 6) |
| K3 | Nominal cells, calendar L, with noise, many repetitions | The fourth read of each train has a room of 0.17 mV and a noise of about 0.10 mV rms: it should fire early in a few percent of the runs, leaving 3 writes instead of 4 on that port | read noise on the bench | whether the rule's small rooms are real: a prediction of failures, at a rate |
| K4 | Calendar L with the pulses of each cell 16 units apart instead of 8 | The same counts, from the isolated margins alone (help at 16 units: 0.05 mV) | none beyond K1's | the separation hypothesis: with enough separation the theorem's score needs no history term (departure 5) |
| K5 | A calendar that sends a pulse to a trained port 4 to 5 units after a FIRE of its cell, ten times | One gain dose per such pulse, no FIRE: ten writes with no read deciding them. And none for the same pulses 2 to 3 units after | the window of dates in which a protected arrival writes, per cell | departures 10 and 11: a prediction that the circuit **leaves** the theorem, and where |
| K6 | Calendar L at 125 C | Two statements of the write counts, both from measures at 125 C: one by the rule as it is, one by the rule with the drift of the stored voltage added between pulses. They differ: stage J gives about 0.19 mV lost per 22 units, so over the 128 idle units before the forward train a trained port loses about 1.1 mV, most of a dose, and may have to be taught again. The run says which statement holds | drift, gap, dose and help at 125 C, per port | departure 8: the condition "memory changes only by doses" |
| K7 | Three cells in a ring, each FIRE of a cell routed to the next in its own date band | Write counts and words of the six ports, as in K1 | as K1, three cells | a cycle longer than two |
| K8 | Calendar L on the netlist extracted from layout 2.2, in each cell | Counts from margins measured on that netlist. One cell alone needs four doses there too, with a dose of 1.3616 mV | gap, dose and help on the extracted netlist | whether the prediction survives the parasitics of the cell; nothing about wires between cells |

Not proposed, and why:

- **An ungated loop** (both edges always open, delay 7/20). After a FIRE of A
  on its source, B's answer returns 2.5 units after the start of A's pulse:
  A is protected and, from the table of protected arrivals, nothing happens.
  The return port never learns. A loop that rings needs delays above about
  2 units; then it never stops firing, and the theorem's clause for perpetual
  traffic asks for a fairness that a single ring gives trivially. It can be
  added if the owner wants a perpetual case.
- **Overlapping pulses on the two ports of one cell.** The theorem has no
  counterpart (departure 12). A prediction would rest on the joint read of
  the cell, not on the network theorem.

## What a preregistration would have to fix

- which candidates, how many instances and repetitions, within a budget
  (about 10 minutes of one processor for a noisy two-cell run of calendar L);
- the rule, word for word, and the value of `k`;
- that every per-cell measure of an instance is finished and committed
  before the network run of that instance starts;
- what a missing run, a refused delivery or a protected arrival counts as;
- that the router is ideal, and that the result is about cells, not wires.
