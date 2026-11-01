import KernelR.HybridPreparedTrain
/-! Actual receiving-cell delivery cuts retain all other cells and legal interleavings. -/
namespace KernelR.Hybrid

/-- Deliveries observed at one cell; other cells remain in the execution. -/
def Execution.cellDeliveries {n θ route s u} (e : @Execution n θ route s u) (i : Fin n) : List (Delivery n) :=
  e.deliveries.filter (fun d => d.cell = i)

structure CellDeliveryStep {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (d : Delivery n) (ds : List (Delivery n)) where
  beforeArrival : Snapshot n
  afterArrival : Snapshot n
  span : Execution θ route s beforeArrival
  entry : Jump route beforeArrival afterArrival
  rest : Execution θ route afterArrival u
  reconstruct : e = span.append (.cons (.jump entry) rest)
  no_earlier : span.cellDeliveries i = []
  delivery : entry.deliveries = [d]
  cell : d.cell = i
  later : rest.cellDeliveries i = ds

theorem Execution.first_cell_delivery {n θ route s u} (e : @Execution n θ route s u)
    (i : Fin n) (d : Delivery n) (ds : List (Delivery n)) (hd : e.cellDeliveries i = d :: ds) :
    Nonempty (CellDeliveryStep e i d ds) := by
  induction e with
  | nil => simp [cellDeliveries,deliveries] at hd
  | @cons s v u move rest ih =>
    cases move with
    | flow f =>
      obtain ⟨cut⟩ := ih (by simpa [cellDeliveries,deliveries,Move.deliveries] using hd)
      exact ⟨{
        beforeArrival := cut.beforeArrival
        afterArrival := cut.afterArrival
        span := .cons (.flow f) cut.span
        entry := cut.entry
        rest := cut.rest
        reconstruct := by simp only [append,cut.reconstruct]
        no_earlier := by simpa [cellDeliveries,deliveries,Move.deliveries] using cut.no_earlier
        delivery := cut.delivery
        cell := cut.cell
        later := cut.later
      }⟩
    | jump j =>
      by_cases hj : j.deliveries.filter (fun d => d.cell = i) = []
      · obtain ⟨cut⟩ := ih (by simpa [cellDeliveries,deliveries,Move.deliveries,List.filter_append,hj] using hd)
        exact ⟨{
          beforeArrival := cut.beforeArrival
          afterArrival := cut.afterArrival
          span := .cons (.jump j) cut.span
          entry := cut.entry
          rest := cut.rest
          reconstruct := by simp only [append,cut.reconstruct]
          no_earlier := by simpa [cellDeliveries,deliveries,Move.deliveries,List.filter_append,hj] using cut.no_earlier
          delivery := cut.delivery
          cell := cut.cell
          later := cut.later
        }⟩
      · cases j with
        | arrive token before after queue due free =>
          have hslot : token.cell = i := by
            by_contra hn
            simp [Jump.deliveries,hn] at hj
          have heq : token = d ∧ rest.cellDeliveries i = ds := by
            simpa [cellDeliveries,deliveries,Move.deliveries,Jump.deliveries,hslot] using hd
          exact ⟨⟨s,_,.nil _,.arrive s token before after queue due free,rest,rfl,rfl,
            by simp [Jump.deliveries,heq.1],by rw [← heq.1]; exact hslot,heq.2⟩⟩
        | _ => simp [Jump.deliveries] at hj

theorem Execution.cellDeliveries_empty_iff {n θ route s u} (e : @Execution n θ route s u) (i : Fin n) :
    e.cellDeliveries i = [] ↔ ∀ p, NoArrivalAt e i p := by
  classical
  constructor
  · intro h p d hd
    by_cases hc : d.cell = i
    · have hm : d ∈ e.cellDeliveries i := by simp [cellDeliveries,List.mem_filter,hd,hc]
      rw [h] at hm
      contradiction
    · exact Or.inl hc
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro d hd
    have hm : d ∈ e.deliveries ∧ d.cell = i := by simpa only [cellDeliveries,List.mem_filter,decide_eq_true_eq] using hd
    rcases h d.port d hm.1 with hn | hn
    · exact hn hm.2
    · exact hn rfl

theorem CellDeliveryStep.no_arrivals_before {n θ route s u i d ds} {e : @Execution n θ route s u}
    (cut : CellDeliveryStep e i d ds) : ∀ p, NoArrivalAt cut.span i p :=
  (cut.span.cellDeliveries_empty_iff i).mp cut.no_earlier

theorem CellDeliveryStep.date {n θ route s u i d ds} {e : @Execution n θ route s u}
    (cut : CellDeliveryStep e i d ds) : cut.beforeArrival.time = d.due ∧ cut.afterArrival.time = d.due := by
  have hd : d ∈ cut.entry.deliveries := by rw [cut.delivery]; simp
  exact ⟨(cut.entry.delivery_due d hd).symm,
    cut.entry.time_unchanged.trans (cut.entry.delivery_due d hd).symm⟩

theorem CellDeliveryStep.raw_after {n θ route s u i d ds} {e : @Execution n θ route s u}
    (cut : CellDeliveryStep e i d ds) : cut.afterArrival.raw d.cell d.port = some cut.afterArrival.time := by
  have hd : d ∈ cut.entry.deliveries := by rw [cut.delivery]; simp
  obtain ⟨before,after,hq,ht,hfree,he⟩ := cut.entry.delivery_snapshot d hd
  rw [he]
  simp [setRaw]

theorem CellDeliveryStep.modes_after {n θ route s u i d ds} {e : @Execution n θ route s u}
    (cut : CellDeliveryStep e i d ds) :
    cut.afterArrival.main = cut.beforeArrival.main ∧ cut.afterArrival.aux = cut.beforeArrival.aux := by
  have hd : d ∈ cut.entry.deliveries := by rw [cut.delivery]; simp
  obtain ⟨before,after,hq,ht,hfree,he⟩ := cut.entry.delivery_snapshot d hd
  rw [he]
  exact ⟨rfl,rfl⟩

theorem CellDeliveryStep.raw_other {n θ route s u i d ds} {e : @Execution n θ route s u}
    (cut : CellDeliveryStep e i d ds) (j : Fin n) (p : Port) (h : j ≠ d.cell ∨ p ≠ d.port) :
    cut.afterArrival.raw j p = cut.beforeArrival.raw j p := by
  have hd : d ∈ cut.entry.deliveries := by rw [cut.delivery]; simp
  obtain ⟨before,after,hq,ht,hfree,he⟩ := cut.entry.delivery_snapshot d hd
  rw [he]
  rcases h with hj | hp
  · simp [setRaw,hj]
  · by_cases hj : j = d.cell
    · subst j; simp [setRaw,hp]
    · simp [setRaw,hj]

theorem CellDeliveryStep.prepared {n θ route s u i d ds} {e : @Execution n θ route s u}
    (cut : CellDeliveryStep e i d ds) (hs : PreparedSection cut.beforeArrival i) :
    PreparedSection cut.afterArrival i := by
  have hx := cut.entry.physical_continuous
  have hm := cut.modes_after
  exact ⟨by rw [hm.1]; exact hs.ready,
    by rw [hx]; exact hs.charge,by rw [hx]; exact hs.recovery,
    by rw [hm.2,hx]; exact hs.auxiliary⟩

theorem CellDeliveryStep.emissions {n θ route s u i d ds} {e : @Execution n θ route s u}
    (cut : CellDeliveryStep e i d ds) :
    e.emissionTimes i = cut.span.emissionTimes i ++ cut.rest.emissionTimes i := by
  have hd : d ∈ cut.entry.deliveries := by rw [cut.delivery]; simp
  calc
    e.emissionTimes i = (cut.span.append (.cons (.jump cut.entry) cut.rest)).emissionTimes i :=
      congrArg (fun actual => actual.emissionTimes i) cut.reconstruct
    _ = _ := by simp [Execution.emissionTimes_append,Execution.emissionTimes_cons,
      Move.ledger,cut.entry.no_emissions_of_delivery d hd]

end KernelR.Hybrid
