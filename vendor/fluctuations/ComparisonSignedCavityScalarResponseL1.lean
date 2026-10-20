module

public import JointProfileResponse
public import ScalarLowClockCalibration

@[expose] public section

noncomputable section
set_option maxHeartbeats 5000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy GaussianCalculus Scalar

theorem HeatJet.profile_L1_window_tendstoUniformly (J : HeatJet 0)
    {α : ℕ → boundedMassProfiles} {β : boundedMassProfiles} (l : ℝ) (t : ℝ≥0)
    (hL1 : Tendsto (fun n => ∫ s in l..(l+t), |(α n).val s-β.val s|)
      atTop (𝓝 0)) :
    TendstoUniformly (fun n => J.nonnegativeProfileValue
      (boundedNonnegativeProfile (α n)) l t)
      (J.nonnegativeProfileValue (boundedNonnegativeProfile β) l t) atTop := by
  choose D _ hD using fun i => (J.smoothG i).bound
  have he := hL1.const_mul ((∑ i, (D i)^2)/2)
  simp only [mul_zero] at he
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [he.eventually (gt_mem_nhds hε)] with n hn x
  have hh := J.nonnegativeProfileValue_L1_comparison D hD
    (boundedNonnegativeProfile (α n)) (boundedNonnegativeProfile β) l t x
  simpa only [Real.dist_eq,abs_sub_comm] using hh.trans_lt hn

theorem scalarProfileJet_L1_window_tendsto
    {α : ℕ → boundedMassProfiles} {β : boundedMassProfiles} (l : ℝ) (t : ℝ≥0)
    (hL1 : Tendsto (fun n => ∫ s in l..(l+t), |(α n).val s-β.val s|)
      atTop (𝓝 0)) (k : ℕ) :
    TendstoUniformly (fun n => scalarProfileJet (boundedNonnegativeProfile (α n)) l t k)
      (scalarProfileJet (boundedNonnegativeProfile β) l t k) atTop := by
  apply jet_tendstoUniformly_of_limit
    (fun n j => scalarProfileJet (boundedNonnegativeProfile (α n)) l t j)
    (scalarProfileJet (boundedNonnegativeProfile β) l t)
    (fun n j x => scalarProfileJet_hasDerivAt _ (fun s => ((α n).property.1 s).2) l t j x)
    (fun j => ⟨(ReplicaTree.attachmentCount 1 j:ℝ),fun n x =>
      scalarProfileJet_bound _ (fun s => ((α n).property.1 s).2) l t j x⟩)
    (scalarProfileJet_hasDerivAt _ (fun s => (β.property.1 s).2) l t)
  have hh := HeatJet.profile_L1_window_tendstoUniformly scalarTerminal l t hL1
  rw [Metric.tendstoUniformly_iff] at hh ⊢
  intro ε hε
  filter_upwards [hh ε hε] with n hn x
  rw [scalarProfileJet_zero (boundedNonnegativeProfile β) (fun s => (β.property.1 s).2),
    scalarProfileJet_zero (boundedNonnegativeProfile (α n)) (fun s => ((α n).property.1 s).2)]
  exact hn (fun _ => x)

theorem HeatJet.profileTest_L1_window_tendsto (J : HeatJet 0)
    {α : ℕ → boundedMassProfiles} {β : boundedMassProfiles} (l : ℝ) (t : ℝ≥0)
    (hL1 : Tendsto (fun n => ∫ s in l..(l+t), |(α n).val s-β.val s|)
      atTop (𝓝 0)) (x : Fin 1 → ℝ) :
    Tendsto (fun n => J.nonnegativeProfileTest (boundedNonnegativeProfile (α n)) l t x)
      atTop (𝓝 (J.nonnegativeProfileTest (boundedNonnegativeProfile β) l t x)) := by
  obtain ⟨K, hK, hb⟩ := J.smoothA.bound
  apply tendsto_response_of_uniform_taylor (M := 4*(K+1)^2)
    (f := fun s n => (J.terminalPerturb s).nonnegativeProfileValue
      (boundedNonnegativeProfile (α n)) l t x)
    (F := fun s => (J.terminalPerturb s).nonnegativeProfileValue
      (boundedNonnegativeProfile β) l t x) (by positivity)
  · intro s
    exact (HeatJet.profile_L1_window_tendstoUniformly (J.terminalPerturb s) l t hL1).tendsto_at x
  · intro s n
    rw [J.nonnegativeProfile_perturb_zero]
    exact J.nonnegativeProfile_terminal_taylor (by linarith)
      (fun y => (hb y).trans (by linarith)) (boundedNonnegativeProfile (α n))
      (fun u => ((α n).property.1 u).2) l t s x
  · intro s
    rw [J.nonnegativeProfile_perturb_zero]
    exact J.nonnegativeProfile_terminal_taylor (by linarith)
      (fun y => (hb y).trans (by linarith)) (boundedNonnegativeProfile β)
      (fun u => (β.property.1 u).2) l t s x

theorem scalarTailSpatialJet_L1_window_tendsto {T : ℝ} (hT : 0 < T)
    {α : ℕ → boundedMassProfiles} {β : boundedMassProfiles} (q : ℝ)
    (hL1 : Tendsto (fun n => ∫ s in (T*q)..(T*q+Real.toNNReal (T*(1-q))),
      |(rescaledBoundedProfile hT (α n)).val s-(rescaledBoundedProfile hT β).val s|)
      atTop (𝓝 0)) (k : ℕ) :
    TendstoUniformly (fun n => scalarTailSpatialJet hT (α n) k q)
      (scalarTailSpatialJet hT β k q) atTop := by
  have hh := scalarProfileJet_L1_window_tendsto
    (T*q) (Real.toNNReal (T*(1-q))) hL1 k
  rw [Metric.tendstoUniformly_iff] at hh ⊢
  intro ε hε
  filter_upwards [hh ε hε] with n hn x
  exact hn (x 0)

theorem scalarPlantedEnergy_L1_window_tendsto {T : ℝ} (hT : 0 < T)
    {α : ℕ → boundedMassProfiles} {β : boundedMassProfiles} (q : ℝ)
    (hL : Tendsto (fun n => ∫ s in (0:ℝ)..(Real.toNNReal (T*q):ℝ),
      |(rescaledBoundedProfile hT (α n)).val s-(rescaledBoundedProfile hT β).val s|)
      atTop (𝓝 0))
    (hR : Tendsto (fun n => ∫ s in (T*q)..(T*q+Real.toNNReal (T*(1-q))),
      |(rescaledBoundedProfile hT (α n)).val s-(rescaledBoundedProfile hT β).val s|)
      atTop (𝓝 0)) :
    Tendsto (fun n => scalarPlantedEnergy hT (α n) q) atTop
      (𝓝 (scalarPlantedEnergy hT β q)) := by
  have hA : TendstoUniformly (fun n => (scalarTailJet hT (α n) q).square.A)
      (scalarTailJet hT β q).square.A atTop :=
    tendstoUniformly_squared_unit (fun n => scalarTailJet_G_bound hT (α n) q 0)
      (scalarTailJet_G_bound hT β q 0)
      (scalarTailSpatialJet_L1_window_tendsto hT q hR 1)
  have hm := HeatJet.nonnegativeProfileTest_terminal_tendsto
    (fun n => (scalarTailJet hT (α n) q).square) (scalarTailJet hT β q).square
    (scalarTailSpatialJet_L1_window_tendsto hT q hR 0) hA
    (fun n => rescaledMassProfile (α n) hT) (fun n s => ((α n).property.1 (s/T)).2)
    (fun _ => 0) (fun _ => Real.toNNReal (T*q))
  have hl := HeatJet.profileTest_L1_window_tendsto
    (scalarTailJet hT β q).square 0 (Real.toNNReal (T*q))
    (by simpa only [zero_add] using hL) 0
  have hh := (hm.tendsto_at 0).add hl
  simpa only [boundedNonnegativeProfile_rescaled, sub_add_cancel,zero_add,
    scalarPlantedEnergy] using hh

theorem rescaledBoundedProfile_l1_window_tendsto {T : ℝ} (hT : 0 < T)
    {α : ℕ → boundedMassProfiles} {β : boundedMassProfiles}
    (hL1 : Tendsto (fun n => ∫ s in (0:ℝ)..1, |(α n).val s-β.val s|) atTop (𝓝 0))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    Tendsto (fun n => ∫ s in a..b,
      |(rescaledBoundedProfile hT (α n)).val s-(rescaledBoundedProfile hT β).val s|)
      atTop (𝓝 0) := by
  have Hfull : Tendsto (fun n => ∫ s in (0:ℝ)..T,
      |(rescaledBoundedProfile hT (α n)).val s-(rescaledBoundedProfile hT β).val s|)
      atTop (𝓝 0) := by
    have he (n : ℕ) : (∫ s in (0:ℝ)..T,
        |(rescaledBoundedProfile hT (α n)).val s-(rescaledBoundedProfile hT β).val s|) =
        T*(∫ s in (0:ℝ)..1, |(α n).val s-β.val s|) := by
      change (∫ s in (0:ℝ)..T, |(α n).val (s/T)-β.val (s/T)|) = _
      rw [intervalIntegral.integral_comp_div (fun z => |(α n).val z-β.val z|) hT.ne']
      simp only [zero_div,div_self hT.ne',smul_eq_mul]
    simp_rw [he]
    simpa only [mul_zero] using hL1.const_mul T
  apply squeeze_zero (fun n => intervalIntegral.integral_nonneg hab (fun _ _ => abs_nonneg _))
    (fun n => intervalIntegral.integral_mono_interval ha hab hb
      (Eventually.of_forall (fun s => abs_nonneg _))
      (((rescaledBoundedProfile hT (α n)).property.2.intervalIntegrable.sub
        (rescaledBoundedProfile hT β).property.2.intervalIntegrable).abs)) Hfull

theorem scalarPlantedEnergy_L1_tendsto {T : ℝ} (hT : 0 < T)
    {α : ℕ → boundedMassProfiles} {β : boundedMassProfiles}
    (hL1 : Tendsto (fun n => ∫ s in (0:ℝ)..1, |(α n).val s-β.val s|) atTop (𝓝 0))
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    Tendsto (fun n => scalarPlantedEnergy hT (α n) q) atTop
      (𝓝 (scalarPlantedEnergy hT β q)) := by
  have hleft : (Real.toNNReal (T*q):ℝ)=T*q := Real.coe_toNNReal _ (mul_nonneg hT.le hq)
  have hright : T*q+(Real.toNNReal (T*(1-q)):ℝ)=T := by
    rw [Real.coe_toNNReal _ (mul_nonneg hT.le (sub_nonneg.mpr hq1))]
    ring
  apply scalarPlantedEnergy_L1_window_tendsto hT q
  · rw [hleft]
    exact rescaledBoundedProfile_l1_window_tendsto hT hL1 le_rfl
      (mul_nonneg hT.le hq) (by nlinarith)
  · rw [hright]
    exact rescaledBoundedProfile_l1_window_tendsto hT hL1
      (mul_nonneg hT.le hq) (by nlinarith) le_rfl

theorem scalarPlantedEnergy_unit_abs_sub_le {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (hc : ∀ x, ContinuousWithinAt α.val (Ici x) x)
    {q r : ℝ} (hq : q∈Icc (0:ℝ) 1) (hr : r∈Icc (0:ℝ) 1) :
    |scalarPlantedEnergy hT α q-scalarPlantedEnergy hT α r| ≤ T*|q-r| := by
  have hqE := scalarPlantedEnergy_integral_nonnegative hT α hq.1 hq.2 (fun x _ => hc x)
  have hrE := scalarPlantedEnergy_integral_nonnegative hT α hr.1 hr.2 (fun x _ => hc x)
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((scalarPlantedCurvature_continuous hT α).intervalIntegrable 0 r)
    ((scalarPlantedCurvature_continuous hT α).intervalIntegrable r q)
  have he : scalarPlantedEnergy hT α q-scalarPlantedEnergy hT α r =
      T*(∫ x in r..q, scalarPlantedCurvature hT α x) := by
    have hh : T*(∫ x in 0..r,scalarPlantedCurvature hT α x)+
        T*(∫ x in r..q,scalarPlantedCurvature hT α x) =
        T*(∫ x in 0..q,scalarPlantedCurvature hT α x) := by rw [← mul_add,hadd]
    linarith only [hqE,hrE,hh]
  have H := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := r) (b := q) (C := (1:ℝ)) (fun x _ => by
      rw [Real.norm_eq_abs,abs_of_nonneg (scalarPlantedCurvature_bounds hT α x).1]
      exact (scalarPlantedCurvature_bounds hT α x).2)
  rw [he,abs_mul,abs_of_pos hT]
  exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs,one_mul] using H) hT.le

theorem scalarPlantedEnergy_L1_varying_clock_tendsto {T : ℝ} (hT : 0 < T)
    {α : ℕ → boundedMassProfiles} {β : boundedMassProfiles}
    (hL1 : Tendsto (fun n => ∫ s in (0:ℝ)..1, |(α n).val s-β.val s|) atTop (𝓝 0))
    (hc : ∀ n x, ContinuousWithinAt (α n).val (Ici x) x)
    {q : ℕ → ℝ} {r : ℝ} (hqb : ∀ n,q n∈Icc (0:ℝ) 1) (hr : r∈Icc (0:ℝ) 1)
    (hq : Tendsto q atTop (𝓝 r)) :
    Tendsto (fun n => scalarPlantedEnergy hT (α n) (q n)) atTop
      (𝓝 (scalarPlantedEnergy hT β r)) := by
  have He := scalarPlantedEnergy_L1_tendsto hT hL1 hr.1 hr.2
  have Hbound := ((hq.sub_const r).abs.const_mul T)
  simp only [sub_self,abs_zero,mul_zero] at Hbound
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Hbound.eventually (gt_mem_nhds (half_pos hε)),
    He.eventually (Metric.ball_mem_nhds _ (half_pos hε))] with n hn he
  rw [Real.dist_eq] at he
  rw [Real.dist_eq]
  have H := scalarPlantedEnergy_unit_abs_sub_le hT (α n) (hc n) (hqb n) hr
  exact (abs_sub_le _ (scalarPlantedEnergy hT (α n) r) _).trans_lt
    ((add_le_add H le_rfl).trans_lt (by linarith only [hn,he]))

end OAI.SKFluctuations.LaplaceWindowFormalization
