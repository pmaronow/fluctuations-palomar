module

public import ComparisonActualVarianceColumns

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open MeasureTheory ProbabilityTheory Set Hierarchy
open scoped BigOperators NNReal ENNReal

theorem left_mass_square_row_le (x : ℕ→ℝ) (K : ℕ) {a b t : ℝ}
    (hstart:x 0=a) (hend:x K=b) (hat:a<t) (htb:t≤b)
    (hx:∀u:Fin K,x u.val<x (u.val+1)) :
    (∑u:Fin K,(x (u.val+1)-x u.val)*(left a (x u.val) (x (u.val+1)) t)^2) ≤ (t-a)⁻¹ := by
  have hn : (∑u:Fin K,(x (u.val+1)-x u.val)*left a (x u.val) (x (u.val+1)) t)=1 := by
    rw [Fin.sum_univ_eq_sum_range (fun u=>(x (u+1)-x u)*left a (x u) (x (u+1)) t)]
    exact left_row_normalized x K hstart hend hat htb (fun u hu=>hx ⟨u,by simpa using hu⟩)
  calc
    _ ≤ ∑u:Fin K,(t-a)⁻¹*((x (u.val+1)-x u.val)*left a (x u.val) (x (u.val+1)) t) := by
      apply Finset.sum_le_sum
      intro u _
      have hb:=left_bounds (hx u) hat
      have hh:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb.2 hb.1) (sub_pos.mpr (hx u)).le
      convert hh using 1 <;> ring
    _ = _ := by rw [←Finset.mul_sum,hn,mul_one]

theorem right_mass_square_row_le (x : ℕ→ℝ) (K : ℕ) {a b t : ℝ}
    (hstart:x 0=a) (hend:x K=b) (hat:a≤t) (htb:t<b)
    (hx:∀u:Fin K,x u.val<x (u.val+1)) :
    (∑u:Fin K,(x (u.val+1)-x u.val)*(right b (x u.val) (x (u.val+1)) t)^2) ≤ (b-t)⁻¹ := by
  have hn : (∑u:Fin K,(x (u.val+1)-x u.val)*right b (x u.val) (x (u.val+1)) t)=1 := by
    rw [Fin.sum_univ_eq_sum_range (fun u=>(x (u+1)-x u)*right b (x u) (x (u+1)) t)]
    exact right_row_normalized x K hstart hend hat htb (fun u hu=>hx ⟨u,by simpa using hu⟩)
  calc
    _ ≤ ∑u:Fin K,(b-t)⁻¹*((x (u.val+1)-x u.val)*right b (x u.val) (x (u.val+1)) t) := by
      apply Finset.sum_le_sum
      intro u _
      have hb:=right_bounds (hx u) htb
      have hh:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb.2 hb.1) (sub_pos.mpr (hx u)).le
      convert hh using 1 <;> ring
    _ = _ := by rw [←Finset.mul_sum,hn,mul_one]

theorem left_mass_square_columns_le_log (x : ℕ→ℝ) (K : ℕ) {b δ:ℝ}
    (hstart:x 0=0) (hend:x K=b) (hδ:0<δ) (hwidth:2*δ≤b)
    (hx:∀u:Fin K,x u.val<x (u.val+1)) :
    (∑u:Fin K,(x (u.val+1)-x u.val)*(∫t in δ..b-δ,(left 0 (x u.val) (x (u.val+1)) t)^2)) ≤ Real.log (b/δ) := by
  have hdb:δ≤b:=by linarith
  have hI u : IntervalIntegrable (fun t=>(x ((u:Fin K).val+1)-x u.val)*(left 0 (x u.val) (x (u.val+1)) t)^2) volume δ b := by
    apply ContinuousOn.intervalIntegrable (μ:=volume)
    simpa [uIcc_of_le hdb,Pi.pow_def] using
      ((left_continuousOn (a:=0) (b:=b) hδ (hx u)).pow 2).const_mul (x (u.val+1)-x u.val)
  have hS : IntervalIntegrable (fun t=>∑u:Fin K,(x (u.val+1)-x u.val)*(left 0 (x u.val) (x (u.val+1)) t)^2) volume δ b := by
    convert IntervalIntegrable.sum Finset.univ (fun u _=>hI u) using 1
    funext t
    simp only [Finset.sum_apply]
  have hInv : IntervalIntegrable (fun t:ℝ=>t⁻¹) volume δ b := by
    apply ContinuousOn.intervalIntegrable (μ:=volume)
    simpa [uIcc_of_le hdb,Pi.inv_def] using continuous_id.continuousOn.inv₀ (fun (t:ℝ) (ht:t∈Icc δ b)=>ne_of_gt (hδ.trans_le ht.1))
  have hs := intervalIntegral.integral_mono_interval (le_refl δ) (by linarith : δ≤b-δ)
    (by linarith : b-δ≤b) (Filter.Eventually.of_forall (fun _=>Finset.sum_nonneg (fun u _=>mul_nonneg (sub_pos.mpr (hx u)).le (sq_nonneg _)))) hS
  have hbnd := intervalIntegral.integral_mono_on hdb hS hInv (fun t ht=>by
    simpa only [sub_zero] using left_mass_square_row_le x K hstart hend (hδ.trans_le ht.1) ht.2 hx)
  have hpq:δ≤b-δ:=by linarith
  have he : (∫t in δ..b-δ,∑u:Fin K,(x (u.val+1)-x u.val)*(left 0 (x u.val) (x (u.val+1)) t)^2)=
      ∑u:Fin K,(x (u.val+1)-x u.val)*(∫t in δ..b-δ,(left 0 (x u.val) (x (u.val+1)) t)^2) := by
    rw [intervalIntegral.integral_finset_sum (fun u _=>(hI u).mono_set (by rw [uIcc_of_le hpq,uIcc_of_le hdb];exact Icc_subset_Icc le_rfl (by linarith)))]
    simp only [intervalIntegral.integral_const_mul]
  rw [he] at hs
  exact hs.trans (hbnd.trans_eq (integral_inv_of_pos hδ (by linarith)))

theorem right_mass_square_columns_le_log (x : ℕ→ℝ) (K : ℕ) {b δ:ℝ}
    (hstart:x 0=0) (hend:x K=b) (hδ:0<δ) (hwidth:2*δ≤b)
    (hx:∀u:Fin K,x u.val<x (u.val+1)) :
    (∑u:Fin K,(x (u.val+1)-x u.val)*(∫t in δ..b-δ,(right b (x u.val) (x (u.val+1)) t)^2)) ≤ Real.log (b/δ) := by
  have h0b:0≤b-δ:=by linarith
  have hI u : IntervalIntegrable (fun t=>(x ((u:Fin K).val+1)-x u.val)*(right b (x u.val) (x (u.val+1)) t)^2) volume 0 (b-δ) := by
    apply ContinuousOn.intervalIntegrable (μ:=volume)
    simpa [uIcc_of_le h0b,Pi.pow_def] using
      ((right_continuousOn (a:=0) hδ (hx u)).pow 2).const_mul (x (u.val+1)-x u.val)
  have hS : IntervalIntegrable (fun t=>∑u:Fin K,(x (u.val+1)-x u.val)*(right b (x u.val) (x (u.val+1)) t)^2) volume 0 (b-δ) := by
    convert IntervalIntegrable.sum Finset.univ (fun u _=>hI u) using 1
    funext t
    simp only [Finset.sum_apply]
  have hInv : IntervalIntegrable (fun t:ℝ=>(b-t)⁻¹) volume 0 (b-δ) := by
    apply ContinuousOn.intervalIntegrable (μ:=volume)
    simpa [uIcc_of_le h0b,Pi.inv_def] using
      (continuous_const.sub continuous_id).continuousOn.inv₀ (fun (t:ℝ) (ht:t∈Icc 0 (b-δ))=>by change b-t≠0;linarith [ht.2])
  have hs := intervalIntegral.integral_mono_interval hδ.le (by linarith : δ≤b-δ) le_rfl
    (Filter.Eventually.of_forall (fun _=>Finset.sum_nonneg (fun u _=>mul_nonneg (sub_pos.mpr (hx u)).le (sq_nonneg _)))) hS
  have hbnd := intervalIntegral.integral_mono_on h0b hS hInv (fun t ht=>
    right_mass_square_row_le x K hstart hend ht.1 (by linarith [ht.2]) hx)
  have hpq:δ≤b-δ:=by linarith
  have he : (∫t in δ..b-δ,∑u:Fin K,(x (u.val+1)-x u.val)*(right b (x u.val) (x (u.val+1)) t)^2)=
      ∑u:Fin K,(x (u.val+1)-x u.val)*(∫t in δ..b-δ,(right b (x u.val) (x (u.val+1)) t)^2) := by
    rw [intervalIntegral.integral_finset_sum (fun u _=>(hI u).mono_set (by rw [uIcc_of_le hpq,uIcc_of_le h0b];exact Icc_subset_Icc hδ.le le_rfl))]
    simp only [intervalIntegral.integral_const_mul]
  rw [he] at hs
  have heInv : (∫t in 0..b-δ,(b-t)⁻¹)=Real.log (b/δ) := by
    rw [intervalIntegral.integral_comp_sub_left (fun t:ℝ=>t⁻¹) b]
    have he:b-(b-δ)=δ:=by ring
    rw [he,sub_zero]
    exact integral_inv_of_pos hδ (by linarith)
  exact hs.trans (hbnd.trans_eq heInv)

theorem physical_actual_bin_variance_le_cap_contact_energy (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → Fin K) (x : ℕ → ℝ) {δ width tau : ℝ}
    (hδ:0<δ) (hwidth:2*δ≤width) (hstart:x 0=0) (hend:x K=width)
    (hx:∀u:Fin K,x u<x (u.val+1)) (htau:0≤tau)
    (contacts:Finset (Fin K))
    (hcap:∀u:Fin K,u∉contacts→physicalSelectedUnitEnergy n steps q0 J unit u≤tau*(x (u.val+1)-x u)) :
    actualBinSideVariance n K steps q0 J unit x δ width ≤
      2*tau*Real.log (width/δ)+
      ∑u∈contacts,physicalSelectedUnitEnergy n steps q0 J unit u*
        ((∫t in δ..width-δ,(left 0 (x u.val) (x (u.val+1)) t)^2)+
          (∫t in δ..width-δ,(right width (x u.val) (x (u.val+1)) t)^2)) := by
  have hpq:δ≤width-δ:=by linarith
  let IL := fun u:Fin K=>(∫t in δ..width-δ,(left 0 (x u.val) (x (u.val+1)) t)^2)
  let IR := fun u:Fin K=>(∫t in δ..width-δ,(right width (x u.val) (x (u.val+1)) t)^2)
  let E := fun u:Fin K=>physicalSelectedUnitEnergy n steps q0 J unit u
  let mu := fun u:Fin K=>x (u.val+1)-x u
  have hIL u:0≤IL u:=intervalIntegral.integral_nonneg_of_forall hpq (fun _=>sq_nonneg _)
  have hIR u:0≤IR u:=intervalIntegral.integral_nonneg_of_forall hpq (fun _=>sq_nonneg _)
  have hVL := physical_selected_weight_variance_integral_le_energy n steps ha q0 J unit
    (fun t u=>left 0 (x u.val) (x (u.val+1)) t) hpq (fun u=>by
      have h:=left_continuousOn (a:=0) (b:=width) hδ (hx u)
      exact h.mono (by simpa only [zero_add] using Icc_subset_Icc le_rfl (by linarith : width-δ≤width)))
  have hVR := physical_selected_weight_variance_integral_le_energy n steps ha q0 J unit
    (fun t u=>right width (x u.val) (x (u.val+1)) t) hpq (fun u=>
      (right_continuousOn (a:=0) hδ (hx u)).mono (Icc_subset_Icc hδ.le le_rfl))
  have hraw:actualBinSideVariance n K steps q0 J unit x δ width≤∑u:Fin K,E u*(IL u+IR u) := by
    unfold actualBinSideVariance selectedScoreVariance selectedLeftWeight selectedRightWeight
    exact (add_le_add hVL hVR).trans_eq (by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u _
      dsimp only [E,IL,IR]
      ring)
  have hsplit:(∑u:Fin K,E u*(IL u+IR u))≤
      tau*(∑u:Fin K,mu u*(IL u+IR u))+∑u∈contacts,E u*(IL u+IR u) := by
    have he:(∑u:Fin K,if u∈contacts then E u*(IL u+IR u) else 0)=∑u∈contacts,E u*(IL u+IR u) := by simp
    rw [←he,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro u _
    have hI:0≤IL u+IR u:=add_nonneg (hIL u) (hIR u)
    by_cases hu:u∈contacts
    · simp only [hu,ite_true]
      exact le_add_of_nonneg_left (mul_nonneg htau (mul_nonneg (sub_pos.mpr (hx u)).le hI))
    · simp only [hu,ite_false,add_zero]
      have hh:=mul_le_mul_of_nonneg_right (hcap u hu) hI
      convert hh using 1 <;> dsimp only [mu,E] <;> ring
  have hsum:(∑u:Fin K,mu u*(IL u+IR u))≤2*Real.log (width/δ) := by
    have hL:=left_mass_square_columns_le_log x K hstart hend hδ hwidth hx
    have hR:=right_mass_square_columns_le_log x K hstart hend hδ hwidth hx
    dsimp only [mu,IL,IR]
    simp only [mul_add,Finset.sum_add_distrib]
    linarith
  exact (hraw.trans hsplit).trans (add_le_add (by
    have hh:=mul_le_mul_of_nonneg_left hsum htau
    convert hh using 1 <;> ring) le_rfl)

end OAI.SKFluctuations.WholeUnitSideKernel
