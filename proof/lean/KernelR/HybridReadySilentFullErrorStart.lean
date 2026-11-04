import KernelR.HybridWeakInputErrorExistence
import KernelR.HybridPhysicalInvariant
import KernelR.HybridPulseSection
import KernelR.HybridContactTransversality

/-! Full-budget READY/SILENT entry after origin+0.43. A READY/SILENT state with an old RAW origin reaches its own actual ERROR
threshold. Expiry before, at or after that threshold is handled by real flows
and jumps; reopening never restarts the incoming pulse at full amplitude. -/
namespace KernelR.Hybrid
open Set

structure ReadySilentFullErrorBoundary (θ : Fin 1 → Parameters) (route : Router 1)
    (input : Snapshot 1) (p : Port) (origin P : ℝ) where
  beforeError : Snapshot 1
  span : Execution θ route input beforeError
  contacts_transversal : span.ContactsTransversal
  date : beforeError.time=P+Real.log 8/(θ 0).ls p
  main_before : ∀ j, beforeError.main j=.ready
  silent_before : beforeError.aux 0 p=.silent
  other_before : ∀ q, q≠p → beforeError.aux 0 q=.ready
  sensor_before : beforeError.x 0 (.m p)=1/10
  main_below : ∀ j, beforeError.x j .q<1
  aux_below : ∀ q, q≠p → beforeError.x 0 (.m q)<1
  charge_margin : beforeError.x 0 .q≤24/25
  pending : beforeError.pending= input.pending
  gains : ∀ q, beforeError.x 0 (.z q)= input.x 0 (.z q)
  recovery : beforeError.x 0 .b= input.x 0 .b
  raw_option : (beforeError.raw 0 p=some origin ∧ beforeError.time<origin+1) ∨
    (beforeError.raw 0 p=none ∧ origin+1≤beforeError.time)
  raw_other : ∀ q, q≠p → beforeError.raw 0 q=none
  emissions : span.ledger.emissions=[]
  deliveries : span.deliveries=[]

private theorem ready_silent_full_error_boundary_exists {θ ε route} (hb : PhysicalBox θ ε)
    (input : Snapshot 1) (p : Port) (origin P : ℝ)
    (hm : input.main 0=.ready) (hq : input.x 0 .q=1/10)
    (ha : input.aux 0 p=.silent)
    (hsensor : input.x 0 (.m p)=(4/5:ℝ)*Real.exp (-(θ 0).ls p*(input.time-P)))
    (hao : ∀ q, q≠p → input.aux 0 q=.ready ∧ RestBand (input.x 0 (.m q)))
    (hr : input.raw 0 p=some origin) (ho : ∀ q, q≠p → input.raw 0 q=none)
    (hwindow : origin+43/100< input.time ∧ input.time<origin+99/100)
    (hErrorWindow : origin+99/100<P+Real.log 8/(θ 0).ls p ∧
      P+Real.log 8/(θ 0).ls p<origin+123/100)
    (hmargin : ∀ t, input.time≤t → readyPulse (input.x 0 .q)
      (Real.exp (input.x 0 (.z p))*rawInputScale (some origin) input.time) input.time t≤24/25)
    (hp : ∀ d∈input.pending, origin+37/10≤d.due) :
    Nonempty (ReadySilentFullErrorBoundary θ route input p origin P) := by
  let Te := P+Real.log 8/(θ 0).ls p
  have hrate := (hb.rates_positive 0 p).2.1
  have hT : input.time<Te := by dsimp [Te]; linarith [hwindow.2,hErrorWindow.1]
  have hRawTime : input.time<origin+1 := by linarith [hwindow.2]
  have hOrigin : origin≤ input.time := by linarith [hwindow.1]
  have hmAll : ∀ j, input.main j=.ready := by
    intro j
    have hj : j=0 := Subsingleton.elim _ _
    subst j
    exact hm
  have haOther : ∀ j q, j≠(0:Fin 1) ∨ q≠p → input.aux j q=.ready := by
    intro j q h
    have hj : j=0 := Subsingleton.elim _ _
    subst j
    exact (hao q (by simpa using h)).1
  have hrOther : ∀ j q, j≠(0:Fin 1) ∨ q≠p → input.raw j q=none := by
    intro j q h
    have hj : j=0 := Subsingleton.elim _ _
    subst j
    exact ho q (by simpa using h)
  have hqAll : ∀ j, input.x j .q<1 := by
    intro j
    have hj : j=0 := Subsingleton.elim _ _
    subst j
    rw [hq]; norm_num
  have hxOther : ∀ j q, j≠(0:Fin 1) ∨ q≠p → input.x j (.m q)<1 := by
    intro j q h
    have hj : j=0 := Subsingleton.elim _ _
    subst j
    linarith [(hao q (by simpa using h)).2.2]
  have hsensorpos : 0< input.x 0 (.m p) := by rw [hsensor]; positivity
  have hend : input.x 0 (.m p)*Real.exp (-(θ 0).ls p*(Te-input.time))=1/10 := by
    rw [hsensor,mul_assoc,←Real.exp_add]
    rw [show -(θ 0).ls p*(input.time-P)+ -(θ 0).ls p*(Te-input.time)=
      -(θ 0).ls p*(Te-P) by ring]
    simpa [Te] using silent_full_decay_end (start:=P) (ne_of_gt hrate)
  have rawLeg {T : ℝ} (hIT : input.time<T) (hTE : T≤Te) (hTR : T≤origin+1) :
      Nonempty (SilentLeg θ input 0 p (some origin) T) := by
    apply silent_leg_exists hIT hmAll ha haOther hr hrOther
      (by intro o he; have he' : o=origin := (Option.some.inj he).symm; subst o; exact ⟨hOrigin,hTR⟩)
      hqAll hxOther
    · intro t ht
      exact hmargin t ht.1
    · intro t ht
      rw [←hend]
      apply mul_lt_mul_of_pos_left _ hsensorpos
      apply Real.exp_lt_exp.mpr
      have htE : t<Te := ht.2.trans_le hTE
      nlinarith
    · intro d hd
      dsimp [Te] at hTE
      linarith [hp d hd,hErrorWindow.2]
  by_cases hE : Te≤origin+1
  · obtain ⟨leg⟩ := rawLeg hT le_rfl hE
    let before := readyProtectedEnd θ input 0 p .silent (some origin) Te
    have hthreshold : before.x 0 (.m p)=1/10 := by
      simpa [before,readyProtectedEnd,readyProtectedValues,protectedReadyRate] using hend
    by_cases hearly : Te<origin+1
    · exact ⟨{
        beforeError:=before,span:=.cons (.flow leg.flow) (.nil _),contacts_transversal:=trivial,date:=rfl
        main_before:=hmAll,silent_before:=ha,other_before:=fun q hq => haOther 0 q (Or.inr hq)
        sensor_before:=hthreshold,main_below:=leg.main_below
        aux_below:=fun q hq => leg.aux_below 0 q (Or.inr hq),charge_margin:=leg.charge_margin
        pending:=rfl,gains:=fun _ => rfl,recovery:=rfl
        raw_option:=Or.inl ⟨hr,hearly⟩,raw_other:=ho,emissions:=rfl,deliveries:=rfl
      }⟩
    · have heq : Te=origin+1 := le_antisymm hE (le_of_not_gt hearly)
      let expired := setRaw before 0 p none
      let expiry := rawExpiryJump (route:=route) before 0 p origin hr heq
      refine ⟨{
        beforeError:=expired,span:=.cons (.flow leg.flow) (.cons (.jump expiry) (.nil _)),date:=rfl
        contacts_transversal:=by simp [expiry,rawExpiryJump,Execution.ContactsTransversal,Jump.ContactTransversal]
        main_before:=hmAll,silent_before:=ha,other_before:=fun q hq => haOther 0 q (Or.inr hq)
        sensor_before:=hthreshold,main_below:=leg.main_below
        aux_below:=fun q hq => leg.aux_below 0 q (Or.inr hq),charge_margin:=leg.charge_margin
        pending:=rfl,gains:=fun _ => rfl,recovery:=rfl
        raw_option:=Or.inr ⟨by simp [expired,setRaw],heq.ge⟩
        raw_other:=?_,emissions:=rfl,deliveries:=rfl
      }⟩
      intro q hqp
      rw [raw_update_other _ _ _ _ _ _ (Or.inr hqp)]
      exact ho q hqp
  · have hRE : origin+1<Te := lt_of_not_ge hE
    obtain ⟨first⟩ := rawLeg hRawTime hRE.le le_rfl
    let middle := readyProtectedEnd θ input 0 p .silent (some origin) (origin+1)
    let expired := setRaw middle 0 p none
    have hraw : expired.raw 0 p=none := by simp [expired,setRaw]
    have hother : ∀ j q, j≠(0:Fin 1) ∨ q≠p → expired.raw j q=none := by
      intro j q hh
      rw [raw_update_other _ _ _ _ _ _ hh]
      exact hrOther j q hh
    have hm' : ∀ j, expired.main j=.ready := hmAll
    have ha' : expired.aux 0 p=.silent := ha
    have hao' : ∀ j q, j≠(0:Fin 1) ∨ q≠p → expired.aux j q=.ready := haOther
    have hsensor' : expired.x 0 (.m p)= input.x 0 (.m p)*Real.exp (-(θ 0).ls p*(origin+1-input.time)) := by
      simp [expired,middle,readyProtectedEnd,readyProtectedValues,protectedReadyRate,setRaw]
    have hsensorpos' : 0<expired.x 0 (.m p) := by rw [hsensor']; positivity
    have hend' : expired.x 0 (.m p)*Real.exp (-(θ 0).ls p*(Te-expired.time))=1/10 := by
      rw [hsensor',mul_assoc,←Real.exp_add]
      change input.x 0 (.m p)*Real.exp
        (-(θ 0).ls p*(origin+1-input.time)+ -(θ 0).ls p*(Te-(origin+1)))=1/10
      rw [show -(θ 0).ls p*(origin+1-input.time)+ -(θ 0).ls p*(Te-(origin+1))=
        -(θ 0).ls p*(Te-input.time) by ring]
      exact hend
    have hqnone : ∀ t∈Icc expired.time Te, readyPulse (expired.x 0 .q)
        (Real.exp (expired.x 0 (.z p))*rawInputScale none expired.time) expired.time t≤24/25 := by
      intro t ht
      simp only [rawInputScale,mul_zero,readyPulse_zero_eq_relax]
      have hbound : expired.x 0 .q≤24/25 := first.charge_margin
      have hc := decay_upper (show expired.x 0 .q-1/10≤(43/50:ℝ) by linarith)
        (by norm_num) (by norm_num : (0:ℝ)≤1/2) (sub_nonneg.mpr ht.1)
      unfold relax
      linarith
    have hxnone : ∀ t∈Ico expired.time Te, 1/10<expired.x 0 (.m p)*Real.exp (-(θ 0).ls p*(t-expired.time)) := by
      intro t ht
      rw [←hend']
      apply mul_lt_mul_of_pos_left _ hsensorpos'
      apply Real.exp_lt_exp.mpr
      nlinarith [ht.2]
    obtain ⟨last⟩ := silent_leg_exists (show expired.time<Te from hRE) hm' ha' hao' hraw hother
      (by intro o he; contradiction) first.main_below first.aux_below hqnone hxnone
      (by intro d hd; change d∈input.pending at hd; dsimp [Te]; linarith [hp d hd,hErrorWindow.2])
    let before := readyProtectedEnd θ expired 0 p .silent none Te
    let expiry := rawExpiryJump (route:=route) middle 0 p origin hr rfl
    exact ⟨{
      beforeError:=before,span:=.cons (.flow first.flow) (.cons (.jump expiry) (.cons (.flow last.flow) (.nil _)))
      contacts_transversal:=by simp [expiry,rawExpiryJump,Execution.ContactsTransversal,Jump.ContactTransversal]
      date:=rfl,main_before:=hm',silent_before:=ha',other_before:=fun q hq => hao' 0 q (Or.inr hq)
      sensor_before:=by simpa [before,readyProtectedEnd,readyProtectedValues,protectedReadyRate] using hend'
      main_below:=last.main_below,aux_below:=fun q hq => last.aux_below 0 q (Or.inr hq)
      charge_margin:=last.charge_margin,pending:=rfl,gains:=fun _ => rfl,recovery:=rfl
      raw_option:=Or.inr ⟨hraw,hRE.le⟩,raw_other:=fun q hq => hother 0 q (Or.inr hq)
      emissions:=rfl,deliveries:=rfl
    }⟩

structure ReadySilentFullErrorStart (θ : Fin 1 → Parameters) (route : Router 1)
    (input : Snapshot 1) (p : Port) (origin P : ℝ) where
  boundary : ReadySilentFullErrorBoundary θ route input p origin P
  final : Snapshot 1
  final_state : final=setAux boundary.beforeError 0 p .error
  execution : Execution θ route input final
  contacts_transversal : execution.ContactsTransversal
  reconstruct : HEq execution (boundary.span.append (.cons
    (.jump (.error boundary.beforeError 0 p boundary.silent_before boundary.sensor_before)) (.nil _)))
  date : final.time=P+Real.log 8/(θ 0).ls p
  main_ready : ∀ j, final.main j=.ready
  aux_error : final.aux 0 p=.error
  sensor_charge : final.x 0 (.m p)=1/10
  charge_margin : final.x 0 .q≤24/25
  main_below : ∀ j, final.x j .q<1
  auxiliary_other : ∀ q, q≠p → final.aux 0 q=.ready ∧ RestBand (final.x 0 (.m q))
  raw_option : final.raw 0 p=if final.time<origin+1 then some origin else none
  raw_other : ∀ q, q≠p → final.raw 0 q=none
  pending : final.pending= input.pending
  gains : ∀ q, final.x 0 (.z q)= input.x 0 (.z q)
  recovery : final.x 0 .b= input.x 0 .b
  emissions : execution.ledger.emissions=[]
  deliveries : execution.deliveries=[]
  physical : PhysicalInvariant θ final
  raw_valid : RawValid final

/-- Construct the residual SILENT path from a reopened state. The only main
response hypothesis is a scalar bound on the old, attenuated RAW tail. -/
theorem ready_silent_full_error_start_exists {θ ε route} (hb : PhysicalBox θ ε)
    (input : Snapshot 1) (p : Port) (origin P : ℝ)
    (hf : PhysicalInvariant θ input) (hv : RawValid input)
    (hq : input.x 0 .q=1/10) (hm : input.main 0=.ready) (ha : input.aux 0 p=.silent)
    (hsensor : input.x 0 (.m p)=(4/5:ℝ)*Real.exp (-(θ 0).ls p*(input.time-P)))
    (hao : ∀ q, q≠p → input.aux 0 q=.ready ∧ RestBand (input.x 0 (.m q)))
    (hr : input.raw 0 p=some origin) (ho : ∀ q, q≠p → input.raw 0 q=none)
    (hwindow : origin+43/100< input.time ∧ input.time<origin+99/100)
    (hErrorWindow : origin+99/100<P+Real.log 8/(θ 0).ls p ∧
      P+Real.log 8/(θ 0).ls p<origin+123/100)
    (hmargin : ∀ t, input.time≤t → readyPulse (input.x 0 .q)
      (Real.exp (input.x 0 (.z p))*rawInputScale (some origin) input.time) input.time t≤24/25)
    (hp : ∀ d∈input.pending, origin+37/10≤d.due) :
    Nonempty (ReadySilentFullErrorStart θ route input p origin P) := by
  obtain ⟨b⟩ := ready_silent_full_error_boundary_exists (route:=route) hb input p origin P hm hq ha hsensor hao hr ho
    hwindow hErrorWindow hmargin hp
  let final := setAux b.beforeError 0 p .error
  let entry : Jump route b.beforeError final := .error b.beforeError 0 p b.silent_before b.sensor_before
  have haEm : entry.ledger.emissions=[] := rfl
  have haDel : entry.deliveries=[] := rfl
  let e := b.span.append (.cons (.jump entry) (.nil _))
  have he : e.ledger.emissions=[] := by
    simp only [e,Execution.emissions_append,b.emissions,Execution.ledger,Move.ledger,haEm,Ledger.add,Ledger.zero,List.append_nil]
  have hd : e.deliveries=[] := by
    simp only [e,Execution.deliveries_append,b.deliveries,Execution.deliveries,Move.deliveries,haDel,List.append_nil]
  have hOther : ∀ q, q≠p → final.aux 0 q=.ready ∧ RestBand (final.x 0 (.m q)) := by
    intro q hq
    have hno : NoArrivalAt b.span 0 q := by simp [NoArrivalAt,b.deliveries]
    have h := (b.span.aux_no_input_rest_band 0 q (hao q hq).1 (hao q hq).2 (ho q hq) hno).1
    simpa [final,setAux,hq] using h
  have hraw : final.raw 0 p=if final.time<origin+1 then some origin else none := by
    rcases b.raw_option with ⟨hr,ht⟩ | ⟨hr,ht⟩
    · simpa [final,setAux,ht] using hr
    · simpa [final,setAux,show ¬b.beforeError.time<origin+1 by linarith] using hr
  exact ⟨{
    boundary:=b,final:=final,final_state:=rfl,execution:=e,reconstruct:=HEq.rfl,date:=b.date
    contacts_transversal:=by simp [e,entry,Execution.ContactsTransversal,Jump.ContactTransversal,b.contacts_transversal]
    main_ready:=b.main_before,aux_error:=by simp [final,setAux],sensor_charge:=b.sensor_before
    charge_margin:=b.charge_margin,main_below:=b.main_below,auxiliary_other:=hOther
    raw_option:=hraw,raw_other:=b.raw_other,pending:=b.pending,gains:=b.gains,recovery:=b.recovery
    emissions:=he,deliveries:=hd,physical:=e.physical_invariant hb hf,raw_valid:=e.raw_valid hv
  }⟩

end KernelR.Hybrid
