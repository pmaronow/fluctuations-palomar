module

public import ComparisonNativeCanonicalBandGeometry
public import ComparisonNativeCavityConcentrationBareRadius

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal
set_option maxHeartbeats 4000000

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def Potential.negativeSet
    {a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : a.Potential) : Set ℝ := Ioo (0 : ℝ) 1 ∩ p.H ⁻¹' Iio 0

theorem Potential.negativeSet_open
    {a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : a.Potential) : IsOpen p.negativeSet := by
  have hc : ContinuousOn p.H (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using p.hH.continuousOn
  exact (hc.mono Ioo_subset_Icc_self).isOpen_inter_preimage isOpen_Ioo isOpen_Iio

theorem Potential.negative_component_endpoints
    {a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : a.Potential) {r : ℝ} (hr : r ∈ p.negativeSet) :
    (p.H (sInf (ordConnectedComponent p.negativeSet r)) = 0 ∨
      sInf (ordConnectedComponent p.negativeSet r) = 0) ∧
    (p.H (sSup (ordConnectedComponent p.negativeSet r)) = 0 ∨
      sSup (ordConnectedComponent p.negativeSet r) = 1) := by
  let C := ordConnectedComponent p.negativeSet r
  have hs : p.negativeSet ⊆ Icc (0 : ℝ) 1 := inter_subset_left.trans Ioo_subset_Icc_self
  have hp := wholeCap_component_endpoints p.negativeSet_open hs hr
  have hnon : C.Nonempty := nonempty_ordConnectedComponent.mpr hr
  have hsub : C ⊆ Icc (0 : ℝ) 1 := ordConnectedComponent_subset.trans hs
  have hclosed : IsClosed (Icc (0 : ℝ) 1 ∩ p.H ⁻¹' Iic 0) :=
    (show ContinuousOn p.H (Icc (0 : ℝ) 1) by
      simpa only [uIcc_of_le zero_le_one] using p.hH.continuousOn).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Iic
  have hCsub : C ⊆ Icc (0 : ℝ) 1 ∩ p.H ⁻¹' Iic 0 := by
    intro t ht
    have hh := (ordConnectedComponent_subset ht).2
    change p.H t < 0 at hh
    exact ⟨hsub ht, hh.le⟩
  have hlo : BddBelow C := ⟨0, fun t ht => (hsub ht).1⟩
  have hhi : BddAbove C := ⟨1, fun t ht => (hsub ht).2⟩
  have hleft0 : p.H (sInf C) ≤ 0 :=
    (hclosed.closure_subset_iff.mpr hCsub (csInf_mem_closure hnon hlo)).2
  have hright0 : p.H (sSup C) ≤ 0 :=
    (hclosed.closure_subset_iff.mpr hCsub (csSup_mem_closure hnon hhi)).2
  constructor
  · by_cases ha : sInf C = 0
    · exact Or.inr ha
    · apply Or.inl
      apply le_antisymm hleft0
      by_contra hbad
      have ht : sInf C ∈ p.negativeSet :=
        ⟨⟨lt_of_le_of_ne hp.1 (fun he => ha he.symm),
          (hp.2.1.trans hp.2.2.1).trans_le hp.2.2.2.1⟩, lt_of_not_ge hbad⟩
      exact hp.2.2.2.2.2.1 ht
  · by_cases hz : sSup C = 1
    · exact Or.inr hz
    · apply Or.inl
      apply le_antisymm hright0
      by_contra hbad
      have ht : sSup C ∈ p.negativeSet :=
        ⟨⟨hp.1.trans_lt (hp.2.1.trans hp.2.2.1),
          lt_of_le_of_ne hp.2.2.2.1 hz⟩, lt_of_not_ge hbad⟩
      exact hp.2.2.2.2.2.2 ht

def Potential.contactCaps
    {a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : a.Potential) : Set ℝ :=
  {r | r ∈ p.negativeSet ∧ p.H (sInf (ordConnectedComponent p.negativeSet r)) = 0}

theorem Potential.component_subset_contactCaps
    {a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : a.Potential) {r : ℝ} (hr : r ∈ p.contactCaps) :
    ordConnectedComponent p.negativeSet r ⊆ p.contactCaps := by
  intro t ht
  refine ⟨ordConnectedComponent_subset ht, ?_⟩
  rw [← ordConnectedComponent_eq ht]
  exact hr.2

theorem Potential.contactCaps_component
    {a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : a.Potential) {r : ℝ} (hr : r ∈ p.contactCaps) :
    ordConnectedComponent p.contactCaps r = ordConnectedComponent p.negativeSet r := by
  apply Subset.antisymm
  · intro t ht
    exact (mem_ordConnectedComponent.mp ht).trans (fun _ h => h.1)
  · exact subset_ordConnectedComponent (self_mem_ordConnectedComponent.mpr hr.1)
      (p.component_subset_contactCaps hr)

theorem Potential.contactCaps_open
    {a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : a.Potential) : IsOpen p.contactCaps := by
  rw [isOpen_iff_forall_mem_open]
  intro r hr
  exact ⟨ordConnectedComponent p.negativeSet r, p.component_subset_contactCaps hr,
    wholeCap_component_isOpen p.negativeSet_open r, self_mem_ordConnectedComponent.mpr hr.1⟩

def Potential.commonGeometry
    {a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : a.Potential) (Kb Kh : ℝ≥0)
    (hb : LipschitzOnWith Kb (fun r => a.b (a.alpha.val.val r)) (Icc 0 1))
    (hh : LipschitzOnWith Kh (fun r => a.h (a.alpha.val.val r)) (Icc 0 1)) :
    a.CommonBandGeometry p where
  clockRegularity := NativePullbackClockRegularity.smooth Kb Kh hb hh
  capSet := p.contactCaps
  hopen := p.contactCaps_open
  hcapSet := fun _ hr => hr.1.1
  hnegative := fun _ hr => hr.1.2
  hcomponent := by
    intro r hr
    rw [p.contactCaps_component hr]
    exact ⟨hr.2, (p.negative_component_endpoints hr.1).2⟩

def Potential.constantClockGeometry
    {a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : a.Potential) {T H : ℝ} (hb : ∀u, a.b u = T) (hh : ∀u, a.h u = H) :
    a.CommonBandGeometry p :=
  p.commonGeometry 0 0 (cavity_constant_clock_lipschitz hb) (cavity_constant_clock_lipschitz hh)

theorem exists_actual_common_geometry_constant
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hq : 2 ≤ a.context.N^delta) {T H : ℝ}
    (hb : ∀u, a.b u = T) (hh : ∀u, a.h u = H) :
    ∃p : a.Potential, Nonempty (a.CommonBandGeometry p) := by
  obtain ⟨p⟩ := a.exists_potential hq
  exact ⟨p, ⟨p.constantClockGeometry hb hh⟩⟩

theorem eventually_exists_actual_common_geometry_constant
    (hdelta : 0 < delta) :
    ∀ᶠn : ℕ in atTop,
      ∀a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀T H : ℝ, (∀u, a.b u = T) → (∀u, a.h u = H) →
      ∃p : a.Potential, Nonempty (a.CommonBandGeometry p) := by
  have hshift : Tendsto (fun n : ℕ => n+1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop k] with n hn
    omega
  have hp : ∀ᶠn : ℕ in atTop, 2 ≤ (n+1 : ℝ)^delta := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (((tendsto_rpow_atTop hdelta).comp tendsto_natCast_atTop_atTop).comp hshift).eventually
        (eventually_ge_atTop 2)
  filter_upwards [hp] with n hn
  intro a T H hb hh
  exact a.exists_actual_common_geometry_constant
    (by simpa only [NativeOverlapContext.N, Nat.cast_add, Nat.cast_one] using hn) hb hh

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
