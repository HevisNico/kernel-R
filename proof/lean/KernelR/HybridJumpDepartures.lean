import KernelR.HybridSnapshotObservational

/-! Classification of actual operational control departures. The hypotheses
name the old mode and a real change of that component, rather than supplying
an event calendar or a desired endpoint. -/
namespace KernelR.Hybrid

theorem Jump.eq_fire_of_main_changed {n route s u} (j : @Jump n route s u)
    (i : Fin n) (hmode : s.main i=.ready) (hchange : u.main i≠s.main i) :
    u={ (setMain s i .fast) with pending:=s.pending++route i s.time } := by
  cases j <;> simp_all [setMain,setAux,setRaw,Function.update_apply]

theorem Jump.eq_fastEnd_of_main_changed {n route s u} (j : @Jump n route s u)
    (i : Fin n) (hmode : s.main i=.fast) (hchange : u.main i≠s.main i) :
    u=setMain s i .slow := by
  cases j <;> simp_all [setMain,setAux,setRaw,Function.update_apply]

theorem Jump.eq_reopen_of_main_changed {n route s u} (j : @Jump n route s u)
    (i : Fin n) (hmode : s.main i=.slow) (hchange : u.main i≠s.main i) :
    u=setMain s i .ready := by
  cases j <;> simp_all [setMain,setAux,setRaw,Function.update_apply]

theorem Jump.eq_mark_of_aux_changed {n route s u} (j : @Jump n route s u)
    (i : Fin n) (p : Port) (hmode : s.aux i p=.ready) (hchange : u.aux i p≠s.aux i p) :
    u=setAux s i p .mark := by
  cases j <;> simp_all [setMain,setAux,setRaw,Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]

theorem Jump.eq_silent_of_aux_changed {n route s u} (j : @Jump n route s u)
    (i : Fin n) (p : Port) (hmode : s.aux i p=.mark) (hchange : u.aux i p≠s.aux i p) :
    u=setAux s i p .silent := by
  cases j <;> simp_all [setMain,setAux,setRaw,Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]

theorem Jump.eq_error_of_aux_changed {n route s u} (j : @Jump n route s u)
    (i : Fin n) (p : Port) (hmode : s.aux i p=.silent) (hchange : u.aux i p≠s.aux i p) :
    u=setAux s i p .error := by
  cases j <;> simp_all [setMain,setAux,setRaw,Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]

theorem Jump.eq_auxReady_of_aux_changed {n route s u} (j : @Jump n route s u)
    (i : Fin n) (p : Port) (hmode : s.aux i p=.error) (hchange : u.aux i p≠s.aux i p) :
    u=setAux s i p .ready := by
  cases j <;> simp_all [setMain,setAux,setRaw,Function.update_apply]
  all_goals split_ifs at * <;> simp_all [Function.update_apply]

end KernelR.Hybrid
