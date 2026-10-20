module

public import ComparisonContactOnlyVaryingWeights

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory
open scoped Topology
set_option maxHeartbeats 7000000

theorem interval_integral_contact_indicator
    (nu : Measure ℝ) (hnu : nu ≤ volume) (H g : ℝ→ℝ)
    {a z l r : ℝ} (hal : a ≤ l) (hlr : l ≤ r) (hrz : r ≤ z)
    (hA : MeasurableSet {t | t∈Ioo a z ∧ H t=0}) :
    (∫t in l..r,({t | t∈Ioo a z ∧ H t=0}).indicator g t∂nu)=
      ∫t in {t | t∈Ioo l r ∧ H t=0},g t∂nu := by
  let : NullSingletonClass nu := ⟨fun t=>le_antisymm
    ((hnu {t}).trans (by simp)) zero_le⟩
  rw [intervalIntegral.integral_of_le hlr,integral_Ioc_eq_integral_Ioo,
    setIntegral_indicator hA]
  have heq : Ioo l r∩{t | t∈Ioo a z ∧ H t=0}={t | t∈Ioo l r ∧ H t=0} := by
    ext t
    constructor
    · intro ht
      exact ⟨ht.1,ht.2.2⟩
    · intro ht
      exact ⟨ht.1,⟨⟨hal.trans_lt ht.1.1,ht.1.2.trans_le hrz⟩,ht.2⟩⟩
  rw [heq]

theorem interval_trace_single_cut_eventually
    (mu : ℕ→Measure ℝ) (hmu : ∀j,mu j ≤ volume)
    (f : ℝ→ℝ) {a s z C K : ℝ} (has : a ≤ s) (hsz : s ≤ z)
    (hi : IntervalIntegrable f volume a z)
    (hf : ∀r∈Icc a z,0 ≤ f r ∧ f r ≤ K) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hleft : ∀p∈Icc a s,p<s → ∀eps>0,∀ᶠj in atTop,
      (∫r in a..p,f r∂mu j) ≤ C*(∫r in a..p,f r)+eps)
    (hright : ∀eps>0,∀ᶠj in atTop,
      (∫r in s..z,f r∂mu j) ≤ C*(∫r in s..z,f r)+eps)
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠj in atTop,(∫r in a..z,f r∂mu j) ≤ C*(∫r in a..z,f r)+eps := by
  by_cases heq : a=s
  · subst s
    exact hright eps heps
  have has' : a < s := lt_of_le_of_ne has heq
  let eta := min ((s-a)/2) (eps/(3*(K+1)))
  have heta : 0 < eta := lt_min (by positivity) (by positivity)
  let p := s-eta
  have hpa : a ≤ p := by have hh:=min_le_left ((s-a)/2) (eps/(3*(K+1))); dsimp [p,eta]; linarith
  have hps : p < s := by dsimp [p]; linarith
  have hapz : a ≤ z := has.trans hsz
  have hips : IntervalIntegrable f volume p s := hi.mono_set (by
    rw [uIcc_of_le hps.le,uIcc_of_le hapz]
    exact Icc_subset_Icc hpa hsz)
  have hiap : IntervalIntegrable f volume a p := hi.mono_set (by
    rw [uIcc_of_le hpa,uIcc_of_le hapz]
    exact Icc_subset_Icc le_rfl (hps.le.trans hsz))
  have hisz : IntervalIntegrable f volume s z := hi.mono_set (by
    rw [uIcc_of_le hsz,uIcc_of_le hapz]
    exact Icc_subset_Icc has le_rfl)
  have htail0 : 0 ≤ ∫r in p..s,f r := intervalIntegral.integral_nonneg hps.le
    (fun r hr=> (hf r ⟨hpa.trans hr.1,hr.2.trans hsz⟩).1)
  have htail : (∫r in p..s,f r) ≤ eps/3 := by
    have hh : (∫r in p..s,f r) ≤ ∫r in p..s,(K:ℝ) :=
      intervalIntegral.integral_mono_on hps.le hips intervalIntegrable_const
        (fun r hr=>(hf r ⟨hpa.trans hr.1,hr.2.trans hsz⟩).2)
    have hsize := (le_div_iff₀ (show 0 < 3*(K+1) by positivity)).mp
      (min_le_right ((s-a)/2) (eps/(3*(K+1))))
    rw [intervalIntegral.integral_const] at hh
    simp only [smul_eq_mul] at hh
    dsimp [p] at hh
    change eta*(3*(K+1)) ≤ eps at hsize
    nlinarith
  have hevol : (∫r in a..p,f r)+(∫r in p..s,f r)+(∫r in s..z,f r)=∫r in a..z,f r := by
    rw [intervalIntegral.integral_add_adjacent_intervals hiap hips,
      intervalIntegral.integral_add_adjacent_intervals (hiap.trans hips) hisz]
  filter_upwards [hleft p ⟨hpa,hps.le⟩ hps (eps/3) (by positivity),
    hright (eps/3) (by positivity)] with j hjl hjr
  have hmid : (∫r in p..s,f r∂mu j) ≤ ∫r in p..s,f r := by
    simp only [intervalIntegral.integral_of_le hps.le]
    exact integral_mono_measure (Measure.restrict_mono (Subset.refl _) (hmu j))
      ((ae_restrict_mem measurableSet_Ioc).mono (fun r hr=>(hf r ⟨hpa.trans hr.1.le,hr.2.trans hsz⟩).1))
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hps.le).mp hips)
  have hemu : (∫r in a..p,f r∂mu j)+(∫r in p..s,f r∂mu j)+(∫r in s..z,f r∂mu j)=
      ∫r in a..z,f r∂mu j := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hiap.mono_measure (hmu j)) (hips.mono_measure (hmu j)),
      intervalIntegral.integral_add_adjacent_intervals ((hiap.trans hips).mono_measure (hmu j)) (hisz.mono_measure (hmu j))]
  have hdrop := mul_nonneg hC htail0
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
