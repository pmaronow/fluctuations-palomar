module

public import CavityRetainedFrozenExpansion

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem native_frozen_one_high_constant_zero (n : ℕ)
    (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as)
    (hq0 : ∀ j i, 0≤q j i) (hq : ∀ i, Monotone (fun j => q j i))
    (hb : ∀ j, 0≤b j) (hh : ∀ j, 0≤h j) (hK : ∀ j, 0≤K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    cutFrozenLowHighJet n q U b h K T (fun _ => 1) 0 0 1 0=0 := by
  have hbase (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      cutFrozenLowHighJet n q U b h K T (fun _ => 1) 0 0 0 t=1 := by
    rw [cutFrozenLowHighJet_eq_profileJets n q U b h K T ho _ 0
      hq0 hq hb hh hK hbm hhm hKm 0 0 ht]
    simp only [List.replicate_zero,List.nil_append,ClockTree.disorderProfileJets]
    exact T.disorderExpect_one (fullWeight_pos n) (fullFeature n) ho 0
      (cutFullVariance n q U 0 t b h K) 0
  have heq : Set.EqOn (cutFrozenLowHighJet n q U b h K T (fun _ => 1) 0 0 1)
      (fun _ => 0) (Ioo (0:ℝ) 1) := by
    intro t ht
    have he : cutFrozenLowHighJet n q U b h K T (fun _ => 1) 0 0 0 =ᶠ[𝓝 t] (fun _ => 1) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact hbase s ⟨hs.1.le,hs.2.le⟩
    have hd := cutFrozenLowHighJet_hasDerivAt n q U b h K T hq0 hq hb hh hK
      hbm hhm hKm ho (fun _ => 1) 0 0 0 ht
    exact hd.unique ((hasDerivAt_const t (1:ℝ)).congr_of_eventuallyEq he)
  have hc := heq.closure
    (cutFrozenLowHighJet_continuous n q U b h K T (fun _ => 1) 0 0 1) continuous_const
  apply hc
  rw [closure_Ioo (by norm_num : (0:ℝ)≠1)]
  exact ⟨le_rfl,zero_le_one⟩

theorem native_retained_one_high_constant_mean_zero (n : ℕ)
    (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as)
    (hq0 : ∀ j i, 0≤q j i) (hq : ∀ i, Monotone (fun j => q j i))
    (hb : ∀ j, 0≤b j) (hh : ∀ j, 0≤h j) (hK : ∀ j, 0≤K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    retainedSignedJets n q U b h K [restHighKernel n U b h K] T (fun _ => 1) []=0 := by
  have hi := actual_frozen_coefficient_eq_retained n q U b h K T ho
    (fun _ => 1) [] hq0 hq hb hh hK hbm hhm hKm 0 1
  simp only [siteMonomial,List.replicate_zero,List.replicate_one,List.nil_append,mul_one] at hi
  rw [←hi]
  exact native_frozen_one_high_constant_zero n q U b h K T ho hq0 hq hb hh hK hbm hhm hKm

end OAI.SKFluctuations.Cavity
