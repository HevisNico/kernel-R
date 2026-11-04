import KernelR.HybridFastAuxLeg
import KernelR.HybridBirthFirstFire

namespace KernelR.Hybrid
open Set

/-- An event-free main FAST segment, including optional RAW expiry. The two
scalar clocks are global so they survive every legal cut. -/
structure FastAuxTrace (θ : Fin 1 → Parameters) (route : Router 1) (s : Snapshot 1)
    (mode : AuxMode) (F P initial : ℝ) where
  final : Snapshot 1
  execution : Execution θ route s final
  contacts_transversal : execution.ContactsTransversal
  main_fast : final.main 0 = .fast
  aux_mode : final.aux 0 0 = mode
  aux_other : ∀ j q, j ≠ 0 ∨ q ≠ 0 → final.aux j q = .ready
  main_clock : final.x 0 .q = Real.exp (-a * (final.time - F))
  sensor_clock : final.x 0 (.m 0) = initial * Real.exp (-protectedReadyRate (θ 0) 0 mode * (final.time - P))
  other_below : ∀ j q, j ≠ 0 ∨ q ≠ 0 → final.x j (.m q) < 1
  raw_other : ∀ j q, j ≠ 0 ∨ q ≠ 0 → final.raw j q = none
  pending : final.pending = s.pending
  gains : ∀ j q, final.x j (.z q) = s.x j (.z q)
  recovery : ∀ j, final.x j .b = s.x j .b
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []

noncomputable def FastAuxTrace.ofLeg {θ route s mode origin T F P initial}
    (leg : FastAuxLeg θ s mode origin T F P initial)
    (hm : s.main 0 = .fast) (ha : s.aux 0 0 = mode)
    (hao : ∀ j q, j ≠ 0 ∨ q ≠ 0 → s.aux j q = .ready)
    (ho : ∀ j q, j ≠ 0 ∨ q ≠ 0 → s.raw j q = none) :
    FastAuxTrace θ route s mode F P initial where
  final := protectedMainEnd θ s 0 0 .fast mode origin T
  execution := .cons (.flow leg.flow) (.nil _)
  contacts_transversal := by trivial
  main_fast := hm
  aux_mode := ha
  aux_other := hao
  main_clock := leg.main_solution
  sensor_clock := leg.sensor_solution
  other_below := leg.other_below
  raw_other := ho
  pending := rfl
  gains := fun _ _ => rfl
  recovery := fun _ => rfl
  emissions := rfl
  deliveries := rfl

noncomputable def FastAuxTrace.expire {θ route s mode F P initial}
    (r : FastAuxTrace θ route s mode F P initial) (origin : ℝ)
    (hr : r.final.raw 0 0 = some origin) (ht : r.final.time = origin + 1) :
    FastAuxTrace θ route s mode F P initial where
  final := setRaw r.final 0 0 none
  execution := r.execution.append (rawExpiryExecution r.final 0 0 origin hr ht)
  contacts_transversal := by
    simpa [rawExpiryExecution, rawExpiryJump, Execution.ContactsTransversal,
      Jump.ContactTransversal] using r.contacts_transversal
  main_fast := r.main_fast
  aux_mode := r.aux_mode
  aux_other := r.aux_other
  main_clock := r.main_clock
  sensor_clock := r.sensor_clock
  other_below := r.other_below
  raw_other := by intro j q h; rw [raw_update_other _ _ _ _ _ _ h]; exact r.raw_other j q h
  pending := r.pending
  gains := r.gains
  recovery := r.recovery
  emissions := by simp [Execution.emissions_append,r.emissions,rawExpiryExecution,rawExpiryJump,Execution.ledger,Move.ledger,Jump.ledger,Ledger.add,Ledger.zero]
  deliveries := by simp [Execution.deliveries_append,r.deliveries,rawExpiryExecution,rawExpiryJump,Execution.deliveries,Move.deliveries,Jump.deliveries]

noncomputable def FastAuxTrace.append {θ route s mode F P initial}
    (r : FastAuxTrace θ route s mode F P initial)
    (v : FastAuxTrace θ route r.final mode F P initial) :
    FastAuxTrace θ route s mode F P initial where
  final := v.final
  execution := r.execution.append v.execution
  contacts_transversal := by
    simpa using And.intro r.contacts_transversal v.contacts_transversal
  main_fast := v.main_fast
  aux_mode := v.aux_mode
  aux_other := v.aux_other
  main_clock := v.main_clock
  sensor_clock := v.sensor_clock
  other_below := v.other_below
  raw_other := v.raw_other
  pending := v.pending.trans r.pending
  gains := fun j q => (v.gains j q).trans (r.gains j q)
  recovery := fun j => (v.recovery j).trans (r.recovery j)
  emissions := by simp [Execution.emissions_append,r.emissions,v.emissions]
  deliveries := by simp [Execution.deliveries_append,r.deliveries,v.deliveries]

/-- A complete protected auxiliary decay while the main cell is FAST. RAW
expiry is taken at its actual date; the endpoint consumes expiry at equality. -/
theorem fast_aux_phase_exists {θ ε route} (hb : PhysicalBox θ ε) (s : Snapshot 1)
    (mode : AuxMode) (origin T F P initial : ℝ)
    (hmode : mode = .silent ∨ mode = .error)
    (hT : s.time < T) (hm : s.main 0 = .fast) (ha : s.aux 0 0 = mode)
    (hao : ∀ j q, j ≠ 0 ∨ q ≠ 0 → s.aux j q = .ready)
    (hr : s.raw 0 0 = if s.time < origin + 1 then some origin else none)
    (ho : ∀ j q, j ≠ 0 ∨ q ≠ 0 → s.raw j q = none)
    (horigin : origin ≤ s.time)
    (hx : ∀ j q, j ≠ 0 ∨ q ≠ 0 → s.x j (.m q) < 1)
    (hq : s.x 0 .q = Real.exp (-a * (s.time - F)))
    (hs : s.x 0 (.m 0) = initial * Real.exp (-protectedReadyRate (θ 0) 0 mode * (s.time - P)))
    (hP : P ≤ s.time) (hF : T ≤ F + 1) (hi : fastAuxFloor mode < initial)
    (hphase : T ≤ P + Real.log (initial / fastAuxFloor mode) / protectedReadyRate (θ 0) 0 mode)
    (hp : ∀ d ∈ s.pending, T ≤ d.due) :
    ∃ r : FastAuxTrace θ route s mode F P initial,
      r.final.time = T ∧ r.final.raw 0 0 = if T < origin + 1 then some origin else none := by
  by_cases hstart : s.time < origin + 1
  · rw [ite_eq_left hstart] at hr
    by_cases hend : T < origin + 1
    · obtain ⟨leg⟩ := fast_aux_leg_exists hb s mode (some origin) T F P initial hmode hT hm ha hao hr ho
        (by intro o he; cases Option.some.inj he; exact ⟨horigin,hend.le⟩) hx hq hs hP hF hi hphase hp
      exact ⟨.ofLeg leg hm ha hao ho,rfl,by simpa [FastAuxTrace.ofLeg,protectedMainEnd,hend] using hr⟩
    · obtain ⟨leg⟩ := fast_aux_leg_exists hb s mode (some origin) (origin + 1) F P initial hmode hstart hm ha hao hr ho
        (by intro o he; cases Option.some.inj he; exact ⟨horigin,le_rfl⟩) hx hq hs hP
        (by linarith) hi (by linarith) (fun d hd => by linarith [hp d hd])
      let firstLeg :=  FastAuxTrace.ofLeg (route := route) leg hm ha hao ho
      let expired := firstLeg.expire origin hr rfl
      have he : expired.final.time = origin + 1 := rfl
      have hraw : expired.final.raw 0 0 = none := by simp [expired,FastAuxTrace.expire,setRaw]
      by_cases heq : T = origin + 1
      · exact ⟨expired,by simpa [heq] using he,by simpa [hend] using hraw⟩
      · have hnext : expired.final.time < T := by rw [he]; exact lt_of_le_of_ne (le_of_not_gt hend) (Ne.symm heq)
        obtain ⟨last⟩ := fast_aux_leg_exists hb expired.final mode none T F P initial hmode hnext
          expired.main_fast expired.aux_mode expired.aux_other hraw expired.raw_other (by intros; contradiction)
          expired.other_below expired.main_clock expired.sensor_clock (by rw [he]; linarith) hF hi hphase
          (fun d hd => by rw [expired.pending] at hd; exact hp d hd)
        let suffix := FastAuxTrace.ofLeg (route := route) last expired.main_fast expired.aux_mode expired.aux_other expired.raw_other
        exact ⟨expired.append suffix,rfl,by simpa [FastAuxTrace.append,suffix,FastAuxTrace.ofLeg,protectedMainEnd,hend] using hraw⟩
  · rw [ite_eq_right hstart] at hr
    obtain ⟨leg⟩ := fast_aux_leg_exists hb s mode none T F P initial hmode hT hm ha hao hr ho
      (by intros; contradiction) hx hq hs hP hF hi hphase hp
    refine ⟨.ofLeg leg hm ha hao ho,rfl,?_⟩
    have hend : ¬T < origin + 1 := by linarith
    simpa [FastAuxTrace.ofLeg,protectedMainEnd,hend] using hr

structure BirthFirstFastEnd {θ born} (c : BirthFirstFire θ (fun _ _ => []) born) where
  final : Snapshot 1
  execution : Execution θ (fun _ _ => []) c.final final
  contacts_transversal : execution.ContactsTransversal
  date : final.time = c.final.time + 1
  main_slow : final.main 0 = .slow
  charge : final.x 0 .q = 1 / 4
  auxiliary : ∀ j p, final.aux j p = .ready
  sensor_charge : final.x 0 (.m 0) = 1 / 40
  rest : ∀ p, RestBand (final.x 0 (.m p))
  raw_none : ∀ j p, final.raw j p = none
  pending : final.pending = c.final.pending
  gains : ∀ j p, final.x j (.z p) = c.final.x j (.z p)
  recovery : ∀ j, final.x j .b = c.final.x j .b
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final
  emissions : execution.ledger.emissions = []
  deliveries : execution.deliveries = []


theorem BirthFirstFire.first_fast_end_exists {θ ε born}
    (c : BirthFirstFire θ (fun _ _ => []) born) (hb : PhysicalBox θ ε) :
    Nonempty (BirthFirstFastEnd c) := by
  let F := c.final.time
  let P := c.fire.firstSilent.final.time
  let Te := c.fire.firstSilent.errorDate
  let Tr := c.weak.final.time + c.fire.firstMark.latency + auxCycleDuration (θ 0) 0
  have hFdate : F = c.weak.final.time + c.fire.latency := c.fire.date
  have hFearly : c.weak.final.time + 2 / 5 < F := by
    exact readyPulse_root_after_four_tenths (c.weak.ready 0).charge.2 c.weak.learned_gain.2
      (by rw [hFdate]; linarith [c.fire.early]) c.fire.response_root
  have hFupper : F < c.weak.final.time + 9 / 10 := by rw [hFdate]; linarith [c.fire.deadline]
  have hP : P < c.weak.final.time + 1 / 20 := c.fire.firstSilent.deadline
  have hPstart : c.weak.final.time ≤ P := by
    change c.weak.final.time ≤ c.weak.final.time + c.fire.firstMark.latency + Real.log (5 / 4) / (θ 0).lm 0
    linarith [c.fire.firstMark.early,(hb.aux_durations_positive 0 0).1]
  have hTe : c.weak.final.time + 99 / 100 < Te ∧ Te < c.weak.final.time + 123 / 100 :=
    c.fire.firstSilent.errorDate_bounds hb
  have hcycle := hb.first_cycle_schedule 0 0 ⟨c.fire.firstMark.early,c.fire.firstMark.deadline⟩
  have hTr : c.weak.final.time + 1 < Tr ∧ Tr < c.weak.final.time + 419 / 300 := by
    constructor <;> dsimp [Tr] <;> linarith [hcycle.2.2.2.2.1,hcycle.2.2.2.2.2]
  have hTeTr : Te < Tr := by
    have hd := (hb.aux_durations_positive 0 0).2.2
    change c.weak.final.time + c.fire.firstMark.latency + Real.log (5 / 4) / (θ 0).lm 0 +
      Real.log 8 / (θ 0).ls 0 < c.weak.final.time + c.fire.firstMark.latency + auxCycleDuration (θ 0) 0
    dsimp [auxCycleDuration]
    linarith
  have hTrF : Tr < F + 1 := by linarith [hTr.2]
  have hqueue : c.final.pending = sourceTrain 0 0 32 8 12 ++ sourceTrain 0 0 160 8 16 := by
    simpa using c.pending
  have hfuture : ∀ d ∈ c.final.pending, F + 1 ≤ d.due := by
    intro d hd; rw [hqueue] at hd
    have hl := a_source_tail_future 32 32 12 (by norm_num) (by norm_num) d hd
    rw [c.weak.date] at hFupper
    linarith
  have hother : ∀ j q, j ≠ 0 ∨ q ≠ 0 → c.final.x j (.m q) < 1 := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have hq : q ≠ 0 := by simpa using h
    have hh := c.fire.execution.aux_no_input_rest_band 0 q ((c.weak.ready 0).auxiliary q).1
      ((c.weak.ready 0).auxiliary q).2 (c.weak.raw_other 0 q (Or.inr hq))
      (by simp [NoArrivalAt,c.fire.deliveries])
    change c.fire.final.x 0 (.m q) < 1
    linarith [hh.1.2.2]
  have hclock : c.final.x 0 .q = Real.exp (-a * (c.final.time - F)) := by
    simp only [F,sub_self,mul_zero,Real.exp_zero]
    exact c.fire.charge
  have hsensor : c.final.x 0 (.m 0) = (4 / 5 : ℝ) * Real.exp (-protectedReadyRate (θ 0) 0 .silent * (c.final.time - P)) := by
    change c.fire.firstSilent.final.x 0 (.m 0) * Real.exp (-protectedReadyRate (θ 0) 0 .silent *
      (c.weak.final.time + c.fire.latency - c.fire.firstSilent.final.time)) = _
    rw [c.fire.firstSilent.sensor_charge]
    rfl
  obtain ⟨silent,hsdate,hsraw⟩ := fast_aux_phase_exists (route := fun _ _ => []) hb c.final .silent c.weak.final.time Te F P (4 / 5)
    (Or.inl rfl) (by change F < Te; linarith [hTe.1]) c.fire.main_fast c.fire.aux_silent
    c.fire.aux_other (by rw [ite_eq_left (show c.final.time < c.weak.final.time + 1 by change F < _; linarith)]; exact c.fire.raw_active)
    c.fire.raw_other (by change c.weak.final.time ≤ F; linarith) hother hclock hsensor
    (by change P ≤ F; linarith) (by linarith [hTrF]) (by norm_num [fastAuxFloor])
    (by dsimp [Te,FirstInputSilent.errorDate,P,fastAuxFloor,protectedReadyRate]; norm_num)
    (fun d hd => by linarith [hfuture d hd])
  have hsthreshold : silent.final.x 0 (.m 0) = 1 / 10 := by
    rw [silent.sensor_clock,hsdate]
    simpa [Te,FirstInputSilent.errorDate,P,protectedReadyRate] using
      silent_full_decay_end (start := P) (ne_of_gt (hb.rates_positive 0 0).2.1)
  let se := setAux silent.final 0 0 .error
  let es : Execution θ (fun _ _ => []) c.final se := silent.execution.append
    (.cons (.jump (.error silent.final 0 0 silent.aux_mode hsthreshold)) (.nil _))
  have hseother : ∀ j q, j ≠ 0 ∨ q ≠ 0 → se.aux j q = .ready := by
    intro j q h
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have hq : q ≠ 0 := by simpa using h
    simpa [se,setAux,hq] using silent.aux_other 0 q (Or.inr hq)
  have hTrsplit : Tr = Te + Real.log 4 / (θ 0).le 0 := by
    change Tr = (P + Real.log 8 / (θ 0).ls 0) + Real.log 4 / (θ 0).le 0
    have hPdate : P = c.fire.firstMark.silentDate := c.fire.firstSilent.date
    rw [hPdate]
    dsimp [Tr,FirstInputMark.silentDate,auxCycleDuration]
    ring
  obtain ⟨err,hedate,heraw⟩ := fast_aux_phase_exists (route := fun _ _ => []) hb se .error c.weak.final.time Tr F Te (1 / 10)
    (Or.inr rfl) (by change silent.final.time < Tr; rw [hsdate]; exact hTeTr)
    silent.main_fast (by simp [se,setAux]) hseother
    (by simpa only [se,setAux,hsdate] using hsraw) silent.raw_other
    (by change c.weak.final.time ≤ silent.final.time; rw [hsdate]; linarith [hTe.1]) silent.other_below
    silent.main_clock (by simpa only [se,setAux,hsdate,sub_self,mul_zero,Real.exp_zero,mul_one] using hsthreshold)
    (by change Te ≤ silent.final.time; rw [hsdate]) hTrF.le (by norm_num [fastAuxFloor])
    (by change Tr ≤ Te + Real.log ((1 / 10 : ℝ) / (1 / 40)) / (θ 0).le 0
        norm_num
        exact hTrsplit.le)
    (fun d hd => by change d ∈ silent.final.pending at hd; rw [silent.pending] at hd; linarith [hfuture d hd])
  have hethreshold : err.final.x 0 (.m 0) = 1 / 40 := by
    rw [err.sensor_clock,hedate]
    rw [hTrsplit]
    have hend := (protected_decay_schedule (by norm_num : (0 : ℝ) < 1 / 40)
      (by norm_num : (1 / 40 : ℝ) < 1 / 10) (hb.rates_positive 0 0).2.2).2.1
    norm_num at hend
    simpa only [protectedReadyRate,add_sub_cancel_left,neg_mul] using hend
  let ready := setAux err.final 0 0 .ready
  let er : Execution θ (fun _ _ => []) se ready := err.execution.append
    (.cons (.jump (.auxReady err.final 0 0 err.aux_mode hethreshold)) (.nil _))
  have hreadyraw : ∀ j p, ready.raw j p = none := by
    intro j p
    by_cases h : j = 0 ∧ p = 0
    · rcases h with ⟨rfl,rfl⟩
      change err.final.raw 0 0 = none
      simpa [show ¬Tr < c.weak.final.time + 1 by linarith [hTr.1]] using heraw
    · exact err.raw_other j p (by tauto)
  have hreadyaux : ∀ j p, ready.aux j p = .ready := by
    intro j p
    by_cases h : j = 0 ∧ p = 0
    · rcases h with ⟨rfl,rfl⟩; simp [ready,setAux]
    · have hh : j ≠ 0 ∨ p ≠ 0 := by tauto
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      have hp : p ≠ 0 := by simpa using hh
      simpa [ready,setAux,hp] using err.aux_other 0 p (Or.inr hp)
  have hreadydate : ready.time = Tr := hedate
  have hreadym : ready.x 0 (.m 0) = 1 / 40 := hethreshold
  have hqglobal (t : ℝ) : ready.x 0 .q * Real.exp (-a * (t - ready.time)) = Real.exp (-a * (t - F)) := by
    change err.final.x 0 .q * Real.exp (-a * (t - err.final.time)) = _
    rw [err.main_clock,attenuation_split]
  let flow : Flow θ ready (protectedMainEnd θ ready 0 0 .fast .ready none (F + 1)) :=
    protectedMainFlow ready 0 0 .fast .ready none (by rw [hreadydate]; exact hTrF)
      (Or.inl rfl) (Or.inl rfl) err.main_fast
      (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim) (hreadyaux 0 0)
      (fun j p _ => hreadyaux j p) (hreadyraw 0 0) (fun j p _ => hreadyraw j p) (by intros; contradiction)
      (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim) err.other_below
      (by intro t ht
          simp only [ite_true,protectedMainRate]
          rw [hqglobal]
          have he : Real.exp (-a * ((F + 1) - F)) = (1 / 4 : ℝ) := by
            norm_num [a,Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 4)]
          rw [← he]
          apply Real.exp_lt_exp.mpr
          nlinarith [a_coarse_bounds.1,ht.2])
      (by intro t ht
          simp only [ite_true,rawInputScale,mul_zero,auxPulse_zero_eq_relax]
          exact relax_lt (by norm_num) ht.1 (by rw [hreadym]; norm_num) (by norm_num))
      (fun d hd => by change d ∈ err.final.pending at hd; rw [err.pending] at hd
                      change d ∈ silent.final.pending at hd; rw [silent.pending] at hd; exact hfuture d hd)
  let before := protectedMainEnd θ ready 0 0 .fast .ready none (F + 1)
  have hbeforeq : before.x 0 .q = 1 / 4 := by
    change ready.x 0 .q * Real.exp (-a * ((F + 1) - ready.time)) = _
    rw [hqglobal]
    norm_num [a,Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  let final := setMain before 0 .slow
  let finish : Execution θ (fun _ _ => []) ready final :=
    .cons (.flow flow) (.cons (.jump (.fastEnd before 0 err.main_fast hbeforeq)) (.nil _))
  let e := es.append (er.append finish)
  have hdel : e.deliveries = [] := by
    simp [e,es,er,finish,Execution.deliveries_append,silent.deliveries,err.deliveries,
      Execution.deliveries,Move.deliveries,Jump.deliveries]
  have hfinishEm : finish.ledger.emissions = [] := rfl
  have herEm : er.ledger.emissions = [] := by
    change (err.execution.append (.cons (.jump (.auxReady err.final 0 0 err.aux_mode hethreshold)) (.nil _))).ledger.emissions = []
    rw [Execution.emissions_append,err.emissions]
    rfl
  have hesEm : es.ledger.emissions = [] := by
    rw [Execution.emissions_append,silent.emissions]
    rfl
  have hem : e.ledger.emissions = [] := by
    change (es.append (er.append finish)).ledger.emissions = []
    rw [Execution.emissions_append es (er.append finish),hesEm,
      Execution.emissions_append er finish,herEm,hfinishEm]
    rfl
  have hfinalm : final.x 0 (.m 0) = 1 / 40 := by
    simp [final,setMain,before,protectedMainEnd,protectedMainValues,rawInputScale,
      auxPulse_zero_eq_relax,relax,hreadym]
  refine ⟨{
    final := final
    execution := e
    contacts_transversal := by
      simpa [e, es, er, finish, Execution.ContactsTransversal, Jump.ContactTransversal]
        using And.intro silent.contacts_transversal err.contacts_transversal
    date := rfl
    main_slow := by simp [final,setMain]
    charge := hbeforeq
    auxiliary := hreadyaux
    sensor_charge := hfinalm
    rest := ?_
    raw_none := hreadyraw
    pending := err.pending.trans silent.pending
    gains := fun j p => (err.gains j p).trans (silent.gains j p)
    recovery := fun j => (err.recovery j).trans (silent.recovery j)
    physical := e.physical_invariant hb c.fire.physical
    raw_valid := e.raw_valid c.fire.raw_valid
    emissions := hem
    deliveries := hdel
  }⟩
  intro p
  by_cases hp : p = 0
  · subst p; rw [hfinalm]; constructor <;> norm_num
  · let eFire : Execution θ (fun _ _ => []) c.fire.final final := e
    have hdelFire : eFire.deliveries = [] := hdel
    let whole := c.fire.execution.append eFire
    exact (whole.aux_no_input_rest_band 0 p ((c.weak.ready 0).auxiliary p).1
      ((c.weak.ready 0).auxiliary p).2 (c.weak.raw_other 0 p (Or.inr hp))
      (by
        have hwhole : whole.deliveries = [] := by
          change (c.fire.execution.append eFire).deliveries = []
          rw [Execution.deliveries_append,c.fire.deliveries,hdelFire]
          rfl
        intro d hd
        rw [hwhole] at hd
        contradiction)).1.2

end KernelR.Hybrid
