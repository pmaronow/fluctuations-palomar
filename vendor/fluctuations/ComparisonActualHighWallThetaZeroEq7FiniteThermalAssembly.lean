module

public import ComparisonActualHighWallThetaZeroEq7FiniteMaskCover
public import ComparisonActualHighWallThetaZeroCapExhaustion
public import ComparisonActualHighWallThetaZeroSelectedRowsGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 18000000
attribute [local instance] Classical.propDecidable

namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

theorem thermal_mask_le_finite_cover_ae {ι : Type*} [Fintype ι]
    (A : Set ℝ) (hA : MeasurableSet A) (support : ι → Set ℝ)
    (hmeas : ∀i, MeasurableSet (support i))
    (hcover : ∀ᵐu ∂volume.restrict (Icc (0:ℝ) 1),
      m.R u ∈ A → ∃i, m.R u ∈ support i) :
    (∫u in 0..1,A.indicator (fun _ => (1:ℝ)) (m.R u)*m.thermal u) ≤
      ∑i,∫u in 0..1,
        (support i).indicator (fun _ => (1:ℝ)) (m.R u)*m.thermal u := by
  let f := fun i u =>
    (support i).indicator (fun _ => (1:ℝ)) (m.R u)*m.thermal u
  have hi i : IntervalIntegrable (f i) volume 0 1 :=
    m.thermal_mask_integrable _ (hmeas i)
  have hiSum : IntervalIntegrable (fun u => ∑i,f i u) volume 0 1 := by
    have H : (fun u => ∑i,f i u)=∑i,f i := by
      funext u
      simp only [Finset.sum_apply]
    rw [H]
    exact IntervalIntegrable.sum Finset.univ (fun i _ => hi i)
  have hcover' := ae_restrict_of_ae_restrict_of_subset
    Ioc_subset_Icc_self hcover
  have hp : ∀ᵐu ∂volume.restrict (Ioc (0:ℝ) 1),
      A.indicator (fun _ => (1:ℝ)) (m.R u)*m.thermal u ≤
        ∑i,f i u := by
    filter_upwards [hcover',ae_restrict_mem measurableSet_Ioc] with u hc hu
    have hn i : 0 ≤ f i u :=
      mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
        (m.thermal_nonneg hu)
    by_cases hmem : m.R u ∈ A
    · obtain ⟨i,hi⟩ := hc hmem
      have H : f i u=m.thermal u := by
        simp only [f,indicator_of_mem hi,one_mul]
      have HS := Finset.single_le_sum (s:=Finset.univ)
        (f:=fun i => f i u) (fun i _ => hn i) (Finset.mem_univ i)
      rw [H] at HS
      simpa only [indicator_of_mem hmem,one_mul] using HS
    · simp only [indicator_of_notMem hmem,zero_mul]
      exact Finset.sum_nonneg (fun i _ => hn i)
  have HB : (∫u in 0..1,A.indicator (fun _ => (1:ℝ)) (m.R u)*m.thermal u) ≤
      ∫u in 0..1,∑i,f i u := by
    simp only [intervalIntegral.integral_of_le zero_le_one]
    exact integral_mono_ae
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (m.thermal_mask_integrable A hA))
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hiSum) hp
  rw [intervalIntegral.integral_finsetSum (fun i _ => hi i)] at HB
  exact HB

theorem massSlice_thermal_mask_integral
    {lo hi : ℝ} (hlo : lo ∈ Icc m.u0 1)
    (hhi : hi ∈ Icc m.u0 1) (hlh : lo ≤ hi)
    (F : Set ℝ) (hF : MeasurableSet F) :
    (∫u in 0..1,
      (m.massSlice lo hi ∩ F).indicator (fun _ => (1:ℝ)) (m.R u)*
        m.thermal u) =
      ∫u in lo..hi,F.indicator (fun _ => (1:ℝ)) (m.R u)*
        m.thermal u := by
  let g := fun u => F.indicator (fun _ => (1:ℝ)) (m.R u)*m.thermal u
  rw [intervalIntegral.integral_of_le zero_le_one,
    ←integral_Icc_eq_integral_Ioc]
  have he : (∫u in Icc (0:ℝ) 1,
      (m.massSlice lo hi ∩ F).indicator (fun _ => (1:ℝ)) (m.R u)*
        m.thermal u) =
      ∫u in Icc (0:ℝ) 1,(Ioo lo hi).indicator g u := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    have hm := m.massSlice_quantile_mem hlo hhi hu
    by_cases hp : u ∈ Ioo lo hi
    · have hr := hm.mpr hp
      by_cases hFmem : m.R u ∈ F
      · have hboth : m.R u ∈ m.massSlice lo hi ∩ F := ⟨hr,hFmem⟩
        simp only [g,indicator_of_mem hboth,
          indicator_of_mem hp,indicator_of_mem hFmem,one_mul]
      · have hn : m.R u ∉ m.massSlice lo hi ∩ F :=
          fun hh => hFmem hh.2
        simp only [g,indicator_of_notMem hn,indicator_of_mem hp,
          indicator_of_notMem hFmem,zero_mul]
    · have hn : m.R u ∉ m.massSlice lo hi ∩ F :=
        fun hh => hp (hm.mp hh.1)
      simp only [g,indicator_of_notMem hn,indicator_of_notMem hp,
        zero_mul]
  rw [he,setIntegral_indicator measurableSet_Ioo,
    inter_eq_right.mpr (Ioo_subset_Icc_self.trans
      (Icc_subset_Icc (m.hu.1.trans hlo.1) hhi.2)),
    ←integral_Ioc_eq_integral_Ioo,
    ←intervalIntegral.integral_of_le hlh]

end ShiftedNativeBandModel

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
variable {P : Q.Potential}

abbrev Eq7InnerCoverPiece {ι : Type*}
    (c : ι → ShiftedCapInterval Q P) (h : ℝ) :=
  Sum (Eq7InnerRelevantBroadSlice c h)
    (Sum (Eq7InnerLowDyad Q h) (Eq7InnerPostDyad Q h))

def eq7InnerCoverSupport {ι : Type*}
    (c : ι → ShiftedCapInterval Q P) (h : ℝ)
    (p : Eq7InnerCoverPiece c h) : Set ℝ :=
  match p with
  | .inl b => eq7InnerBroadSlice c b.val
  | .inr (.inl j) => eq7InnerLowSupport c j
  | .inr (.inr j) => eq7InnerPostSupport c j

theorem eq7_inner_cover_support_measurable
    {ι : Type*} [Fintype ι] (c : ι → ShiftedCapInterval Q P)
    (h : ℝ) (p : Eq7InnerCoverPiece c h) :
    MeasurableSet (eq7InnerCoverSupport c h p) := by
  rcases p with b | j | j
  · change MeasurableSet
      (Q.shiftedNativeModel.massSlice
        ((eq7InnerBroadSampler c b.val.1).node b.val.2.val)
        ((eq7InnerBroadSampler c b.val.1).node (b.val.2.val+1)))
    exact measurableSet_Ioo
  · exact P.retainedSupport_measurable
      (fun i : Eq7InnerLowCapIndex c j => c i.val)
      le_rfl (Q.shiftedNativeModel.R_bounds _).2
  · exact P.retainedSupport_measurable
      (fun i : Eq7InnerPostCapIndex c j => c i.val)
      (Q.shiftedNativeModel.R_bounds _).1
      (Q.shiftedNativeModel.R_bounds _).2

theorem eq7_inner_finite_post_thermal_le_piece_sum
    {ι : Type*} [Fintype ι] (c : ι → ShiftedCapInterval Q P)
    {h : ℝ} (hprefix : Q.eq7InnerPrefixEnd ≤ h) (hhi : h ≤ 1) :
    (∫u in 0..1,
      (Q.shiftedNativeModel.massSlice Q.eq7InnerPrefixEnd h ∩
        ((⋃i,Ioo (c i).left (c i).right) ∪ P.contactSet)).indicator
          (fun _ => (1:ℝ)) (Q.shiftedNativeModel.R u)*
          Q.shiftedNativeModel.thermal u) ≤
      ∑p : Eq7InnerCoverPiece c h,
        ∫u in 0..1,(eq7InnerCoverSupport c h p).indicator
          (fun _ => (1:ℝ)) (Q.shiftedNativeModel.R u)*
          Q.shiftedNativeModel.thermal u := by
  let A := Q.shiftedNativeModel.massSlice Q.eq7InnerPrefixEnd h ∩
    ((⋃i,Ioo (c i).left (c i).right) ∪ P.contactSet)
  have hA : MeasurableSet A :=
    measurableSet_Ioo.inter
      ((MeasurableSet.iUnion (fun _ => measurableSet_Ioo)).union
        P.contactSet_measurable)
  have hpMass : Q.eq7InnerPrefixEnd ∈ Icc Q.data.s 1 :=
    ⟨Q.eq7_inner_s_le_prefix_end,Q.eq7_inner_prefix_end_le_one⟩
  have hhMass : h ∈ Icc Q.data.s 1 :=
    ⟨Q.eq7_inner_s_le_prefix_end.trans hprefix,hhi⟩
  have hcover := eq7_inner_finite_mask_cover_ae c h
  have hcover' : ∀ᵐu ∂volume.restrict (Icc (0:ℝ) 1),
      Q.shiftedNativeModel.R u ∈ A →
        ∃p : Eq7InnerCoverPiece c h,
          Q.shiftedNativeModel.R u ∈ eq7InnerCoverSupport c h p := by
    filter_upwards [hcover,ae_restrict_mem measurableSet_Icc] with u hc hu hmem
    have hmass := (Q.shiftedNativeModel.massSlice_quantile_mem
      hpMass hhMass hu).mp hmem.1
    have hregion : u ∈ Icc Q.data.s h :=
      ⟨hpMass.1.trans hmass.1.le,hmass.2.le⟩
    rcases hc hregion hmem.2 with hpre | hBroad | hLow | hPost
    · exact False.elim (hpre.not_gt hmass.1)
    · obtain ⟨p,hp⟩ := hBroad
      exact ⟨Sum.inl p,hp⟩
    · obtain ⟨j,hj⟩ := hLow
      exact ⟨Sum.inr (Sum.inl j),hj⟩
    · obtain ⟨j,hj⟩ := hPost
      exact ⟨Sum.inr (Sum.inr j),hj⟩
  exact Q.shiftedNativeModel.thermal_mask_le_finite_cover_ae A hA
    (eq7InnerCoverSupport c h)
    (eq7_inner_cover_support_measurable c h) hcover'

theorem Potential.eq7_inner_post_thermal_le_of_finite_piece_prices
    (P : Q.Potential) {h B : ℝ}
    (hprefix : Q.eq7InnerPrefixEnd ≤ h) (hhi : h ≤ 1)
    (hprices : ∀F : Finset (ordConnectedSection P.negativeSet),
      (∑p : Eq7InnerCoverPiece (P.capFamily F) h,
        ∫u in 0..1,
          (eq7InnerCoverSupport (P.capFamily F) h p).indicator
            (fun _ => (1:ℝ)) (Q.shiftedNativeModel.R u)*
            Q.shiftedNativeModel.thermal u) ≤ B) :
    (∫u in 0..1,
      (Q.shiftedNativeModel.massSlice Q.eq7InnerPrefixEnd h ∩
        (P.negativeSet ∪ P.contactSet)).indicator (fun _ => (1:ℝ))
        (Q.shiftedNativeModel.R u)*Q.shiftedNativeModel.thermal u) ≤ B := by
  let A := Q.shiftedNativeModel.massSlice Q.eq7InnerPrefixEnd h
  have hA : MeasurableSet A := measurableSet_Ioo
  obtain ⟨F,_,_,hlim⟩ := P.cap_contact_thermal_exhaustion A hA
  apply le_of_tendsto hlim
  exact Eventually.of_forall (fun j =>
    (eq7_inner_finite_post_thermal_le_piece_sum
      (P.capFamily (F j)) hprefix hhi).trans (hprices (F j)))

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
