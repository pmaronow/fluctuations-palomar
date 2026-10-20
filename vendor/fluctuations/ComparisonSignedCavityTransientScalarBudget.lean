module

public import ComparisonSignedCavitySmallCutRowGraph
public import CavityScalarPairClock

@[expose] public section

noncomputable section
set_option maxHeartbeats 6000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem native_scalar_low_profile_abs_le (n U : ℕ) (b h K : ℕ → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hK : ∀ j<U,|K j|≤M) :
    ∀ j σ τ,|ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 0 b h K) j σ τ|≤M := by
  intro j σ τ
  rw [native_cutLSlope_rest_row_kernel]
  unfold nativeRestRowKernel
  by_cases hj : j<U
  · simp only [hj,↓reduceIte,sub_zero,one_mul,zero_mul,add_zero,abs_mul,abs_spinValue,mul_one]
    exact hK j hj
  · simpa only [hj,↓reduceIte,zero_mul,abs_zero] using hM

theorem native_scalar_lowJet_abs_le (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (b h K : ℕ → ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (c d : T.Slot)
    (x : ActiveCoordinate n → ℝ)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j => q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK0 : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    {M : ℝ} (hM : 0 ≤ M) (hK : ∀ j<U,|K j|≤M)
    (k : ℕ) {l : ℝ} (hl : l∈Icc (0:ℝ) 1) :
    |cutLowJet n q U b h K T (fun σ => sitePair T c d (T.cavityAssignment σ).2)
      (cavityEmbed x) k l 0|≤ClockTree.jetVariation T.leaves k*M^k := by
  rw [cutLowJet_eq_profileJets n q U b h K T ho _ _ hq0 hq hb hh hK0 hbm hhm hKm
    k hl (by norm_num)]
  have H := T.disorderProfileJets_abs_le (fullWeight_pos n) (fullFeature n) ho
    (List.replicate k (ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U 0 b h K)))
    (le_refl _) (fun σ => sitePair T c d (T.cavityAssignment σ).2)
    (C:=1) (by norm_num) hM (fun σ => by
      simp only [sitePair_apply,abs_mul,abs_spinValue,one_mul,le_refl])
    (fun A hA j σ τ => by
      rw [(List.mem_replicate.mp hA).2]
      exact native_scalar_low_profile_abs_le n U b h K hM hK j σ τ)
    0 (cutFullVariance n q U l 0 b h K) (cavityEmbed x)
  simpa only [List.length_replicate,mul_one] using H

theorem native_scalar_lowJet_zero_abs_le_clock (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (b h K : ℕ → ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (c d : T.Slot) (hcd : c≠d) (hKm : Monotone K) (hK0 : ∀ j,0 ≤ K j)
    (hz : K 0=0) {M : ℝ} (hclock : K (T.splitIndex c d)≤M)
    {l : ℝ} (hl : l∈Icc (0:ℝ) 1) :
    |cutLowJet n q U b h K T (fun σ => sitePair T c d (T.cavityAssignment σ).2)
      (cavityEmbed 0) 0 l 0|≤M := by
  rw [cutLowJet_zero n q U b h K T ho]
  have Hprod := cutDisorderExpect_scalar_product n q U l b h K T ho
    (fun _ => 1) (sitePair T c d) (0 : ActiveCoordinate n → ℝ)
  simp only [one_mul,T.cavityLeft.disorderExpect_one (restWeight_pos n) (restFeature n) ho,
    Pi.zero_apply] at Hprod
  rw [Hprod]
  have hzero : relocatedClock U l K 0=0 := by simp only [relocatedClock,hz,mul_zero,ite_self]
  have H := actual_scalar_distinct_pair_abs_le T.cavityRight ho (relocatedClock U l K)
    (relocatedClock_monotone U hl hKm hK0) hzero (T.cavityRightSlot c) (T.cavityRightSlot d)
    (fun H => hcd ((T.cavityRightSlot).injective H)) (C:=M) (v:=1) (by
      rw [T.splitIndex_cavityRight,mul_one]
      exact (relocatedClock_le U hl.2 hK0 _).trans hclock)
  have hsite : sitePair T c d = fun σ => spinValue (T.cavityRight.atSlot σ (T.cavityRightSlot c))*
    spinValue (T.cavityRight.atSlot σ (T.cavityRightSlot d)) := rfl
  rw [hsite]
  simpa only [scalarFeature_apply_spin,mul_one,Pi.zero_def] using H

end OAI.SKFluctuations.Cavity
