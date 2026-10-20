module

public import VaryingProfileSmallClock
public import UniformTaylorResponseLimit

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem HeatJet.profile_joint_parameter_window_tendstoUniformly (J : HeatJet 0)
    {α : ℕ → boundedMassProfiles} {β : boundedMassProfiles}
    (hα : Tendsto α atTop (𝓝 β))
    {l : ℕ → ℝ} {t : ℕ → ℝ≥0} {L : ℝ} {T : ℝ≥0}
    (hl : Tendsto l atTop (𝓝 L)) (ht : Tendsto t atTop (𝓝 T)) :
    TendstoUniformly (fun n => J.nonnegativeProfileValue (boundedNonnegativeProfile (α n)) (l n) (t n))
      (J.nonnegativeProfileValue (boundedNonnegativeProfile β) L T) atTop := by
  obtain ⟨D, hD0, hD⟩ := (J.smoothG 0).bound
  obtain ⟨B, hB0, hB⟩ := (J.smoothH 0).bound
  have hc : Tendsto (fun n => (t n:ℝ)) atTop (𝓝 (T:ℝ)) :=
    (NNReal.continuous_coe.tendsto T).comp ht
  have hw : Tendsto (fun n => D^2*|l n-L|+((B+3*D^2)/2)*|(t n:ℝ)-T|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero, mul_zero, add_zero] using
      ((hl.sub_const L).abs.const_mul (D^2)).add
        ((hc.sub_const (T:ℝ)).abs.const_mul ((B+3*D^2)/2))
  have hp := J.profile_parameter_tendstoUniformly hα L T
  rw [Metric.tendstoUniformly_iff] at hp ⊢
  intro ε hε
  filter_upwards [hw.eventually (gt_mem_nhds (half_pos hε)), hp (ε/2) (half_pos hε)] with n hn hpn x
  rw [Real.dist_eq]
  have he := J.profile_window_stability_general hD hB (boundedNonnegativeProfile (α n))
    (fun s => ((α n).property.1 s).2) (l n) L (t n) T x
  have ha := abs_sub_le
    (J.nonnegativeProfileValue (boundedNonnegativeProfile β) L T x)
    (J.nonnegativeProfileValue (boundedNonnegativeProfile (α n)) L T x)
    (J.nonnegativeProfileValue (boundedNonnegativeProfile (α n)) (l n) (t n) x)
  have hpnx := hpn x
  rw [Real.dist_eq] at hpnx
  rw [abs_sub_comm] at he
  linarith

theorem HeatJet.profileTest_joint_parameter_window_tendsto (J : HeatJet 0)
    {α : ℕ → boundedMassProfiles} {β : boundedMassProfiles}
    (hα : Tendsto α atTop (𝓝 β))
    {l : ℕ → ℝ} {t : ℕ → ℝ≥0} {L : ℝ} {T : ℝ≥0}
    (hl : Tendsto l atTop (𝓝 L)) (ht : Tendsto t atTop (𝓝 T)) (x : Fin 1 → ℝ) :
    Tendsto (fun n => J.nonnegativeProfileTest (boundedNonnegativeProfile (α n)) (l n) (t n) x)
      atTop (𝓝 (J.nonnegativeProfileTest (boundedNonnegativeProfile β) L T x)) := by
  obtain ⟨K, hK, hb⟩ := J.smoothA.bound
  apply tendsto_response_of_uniform_taylor (M := 4*(K+1)^2)
    (f := fun s n => (J.terminalPerturb s).nonnegativeProfileValue
      (boundedNonnegativeProfile (α n)) (l n) (t n) x)
    (F := fun s => (J.terminalPerturb s).nonnegativeProfileValue
      (boundedNonnegativeProfile β) L T x) (by positivity)
  · intro s
    exact (HeatJet.profile_joint_parameter_window_tendstoUniformly (J.terminalPerturb s) hα hl ht).tendsto_at x
  · intro s n
    rw [J.nonnegativeProfile_perturb_zero]
    exact J.nonnegativeProfile_terminal_taylor (by linarith)
      (fun y => (hb y).trans (by linarith)) (boundedNonnegativeProfile (α n))
      (fun u => ((α n).property.1 u).2) (l n) (t n) s x
  · intro s
    rw [J.nonnegativeProfile_perturb_zero]
    exact J.nonnegativeProfile_terminal_taylor (by linarith)
      (fun y => (hb y).trans (by linarith)) (boundedNonnegativeProfile β)
      (fun u => (β.property.1 u).2) L T s x

theorem scalarPlantedJetPower_joint_parameter_window_tendsto {T : ℝ} (hT : 0 < T)
    {α : ℕ → boundedMassProfiles} {β : boundedMassProfiles}
    (hα : Tendsto α atTop (𝓝 β)) {q : ℕ → ℝ} {r : ℝ}
    (hq : Tendsto q atTop (𝓝 r)) (k p : ℕ) :
    Tendsto (fun n => scalarPlantedJetPower hT (α n) k p (q n)) atTop
      (𝓝 (scalarPlantedJetPower hT β k p r)) := by
  have hb (γ : boundedMassProfiles) (u : ℝ) (y : Fin 1 → ℝ) :
      |scalarTailSpatialJet hT γ (k+1) u y| ≤ (ReplicaTree.attachmentCount 1 k:ℝ) :=
    scalarProfileJet_bound _ (fun s => (γ.property.1 (s/T)).2) _ _ k (y 0)
  have hA := tendstoUniformly_pow_of_abs_le (fun n => hb (α n) (q n)) (hb β r)
    (scalarTailSpatialJet_joint_parameter_window_tendsto hT hα hq (k+1)) p
  have hm := Hierarchy.HeatJet.nonnegativeProfileTest_terminal_tendsto
    (fun n => scalarJetPowerTest hT (α n) k p (q n)) (scalarJetPowerTest hT β k p r)
    (scalarTailSpatialJet_joint_parameter_window_tendsto hT hα hq 0) hA
    (fun n => rescaledMassProfile (α n) hT) (fun n s => ((α n).property.1 (s/T)).2)
    (fun _ => 0) (fun n => Real.toNNReal (T*q n))
  have hl := HeatJet.profileTest_joint_parameter_window_tendsto (scalarJetPowerTest hT β k p r)
    (l := fun _ => 0) (L := 0)
    ((continuous_rescaledBoundedProfile hT).tendsto β |>.comp hα)
    tendsto_const_nhds
    (continuous_real_toNNReal.tendsto (T*r) |>.comp (hq.const_mul T)) 0
  have hh := (hm.tendsto_at 0).add hl
  simpa only [Function.comp_def,boundedNonnegativeProfile_rescaled,sub_add_cancel,zero_add,scalarPlantedJetPower] using hh

end OAI.SKFluctuations.LaplaceWindowFormalization
