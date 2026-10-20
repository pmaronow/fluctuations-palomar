module

public import ComparisonVirtualMovingContactExtension
public import ComparisonGlobalProfileRigidity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 5000000

structure ComparisonPinnedGapPrimitive (a b : ℝ) (F : ℝ → ℝ) where
  H : ℝ → ℝ
  nonnegative : ∀ t ∈ Icc a b, 0 ≤ H t
  left_zero : H a = 0
  right_zero : H b = 0
  integrable : IntervalIntegrable F volume a b
  primitive : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → H t-H s = ∫ r in s..t, F r

def ComparisonPinnedGapPrimitive.toGap
    {a b : ℝ} {g F : ℝ → ℝ} (P : ComparisonPinnedGapPrimitive a b F)
    (hbehavior : (∀ᵐ t ∂volume.restrict (Ioo a b),
      (0 < g t → F t < 0) ∧ (g t < 0 → 0 < F t)) ∨
      ∃ spin strength : ℝ → ℝ, ∀ᵐ t ∂volume.restrict (Ioo a b),
        spin t ∈ Icc a b ∧ 0 < strength t ∧ g (spin t) = strength t*(spin t-t) ∧
        (t < spin t → F t < 0) ∧ (spin t < t → 0 < F t)) :
    ComparisonVirtualGapData g a b where
  H := P.H
  F := F
  nonnegative := P.nonnegative
  left_zero := P.left_zero
  right_zero := P.right_zero
  integrable := P.integrable
  primitive_left := fun z hz => P.primitive a ⟨le_rfl,hz.1.trans hz.2⟩ z hz hz.1
  primitive_right := fun z hz => P.primitive z hz b ⟨hz.1.trans hz.2,le_rfl⟩ hz.2
  behavior := hbehavior

theorem comparison_virtual_gap_limit_exists
    {a b B K : ℝ} {C : ℝ≥0} (hab : a < b) (hbB : b < B) (hK : 1 ≤ K)
    (left right errors : ℕ → ℝ) (H J G : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hleftLower : ∀ n, a-1 ≤ left n) (hleftUpper : ∀ n, left n ≤ B)
    (hleft : Tendsto left atTop (𝓝 a)) (hright : Tendsto right atTop (𝓝 b))
    (hrightMem : ∀ n, right n ∈ Icc a B) (hordered : ∀ n, left n ≤ right n)
    (hleftZero : ∀ n, H n (left n) = 0) (hrightZero : ∀ n, H n (right n) = 0)
    (hLip : ∀ n, LipschitzOnWith C (H n) (Icc (left n) B))
    (herr : Tendsto errors atTop (𝓝 0))
    (hLower : ∀ n t, t ∈ Icc a b → -errors n ≤ H n (max (left n) t))
    (hJmono : ∀ n, MonotoneOn (J n) (Icc a B))
    (hJbound : ∀ n t, t ∈ Icc a B → J n t ∈ Icc (1/K^2) (K^2))
    (hJm : ∀ n, Measurable (J n))
    (hf : IntegrableOn f (Icc a b))
    (hGi : ∀ n s t, s ∈ Ioo a b → t ∈ Ioo a b → s ≤ t → IntegrableOn (G n) (Icc s t))
    (hGlim : ∀ s t, s ∈ Ioo a b → t ∈ Ioo a b → s ≤ t →
      Tendsto (fun n => ∫ r in Icc s t, |G n r-f r|) atTop (𝓝 0))
    (hPrimitive : ∀ n s t, s ∈ Ioo a b → t ∈ Ioo a b → left n ≤ s → s ≤ t →
      H n t-H n s = ∫ r in s..t, J n r*G n r) :
    ∃ j : ℝ → ℝ, Monotone j ∧ (∀ t ∈ Icc a b, j t ∈ Icc (1/K^2) (K^2)) ∧
      Nonempty (ComparisonPinnedGapPrimitive a b (fun t => j t*f t)) := by
  have haB : a ≤ B := hab.le.trans hbB.le
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hK2 : 0 < K^2 := sq_pos_of_pos hKp
  obtain ⟨j,phi,hphi,hjMono,hjBound,hjLim⟩ :=
    virtual_band_factor_exists_pointwise_subseq haB hK J hJmono hJbound
  obtain ⟨p,psi,hpsi,hP,hpa,_hpLip⟩ :=
    virtual_moving_contact_potentials_exists_uniform_subseq haB
      (left ∘ phi) (H ∘ phi) (fun n => hleftLower (phi n)) (fun n => hleftUpper (phi n))
      (hleft.comp hphi.tendsto_atTop) (fun n => hleftZero (phi n)) (fun n => hLip (phi n))
  let rho := phi ∘ psi
  have hrho : StrictMono rho := hphi.comp hpsi
  let P : ℕ → BoundedContinuousFunction (Icc a B) ℝ := fun n =>
    virtualMovingContactPotential (a:=a) (hleftUpper (rho n)) (H (rho n)) (hLip (rho n))
  have hPlim : Tendsto P atTop (𝓝 p) := by simpa only [P,rho,Function.comp_def] using hP
  let Hlimit : ℝ → ℝ := IccExtend haB p
  have hHlimit : Continuous Hlimit := continuous_IccExtend_iff.mpr p.continuous
  have hHeq t (ht : t ∈ Icc a B) : Hlimit t = p ⟨t,ht⟩ := IccExtend_of_mem haB p ht
  have hleft0 : Hlimit a = 0 := by
    rw [hHeq a ⟨le_rfl,haB⟩]
    exact hpa
  let rightSub : ℕ → Icc a B := fun n => ⟨right (rho n),hrightMem (rho n)⟩
  have hrightSub : Tendsto rightSub atTop (𝓝 (⟨b,⟨hab.le,hbB.le⟩⟩ : Icc a B)) :=
    tendsto_subtype_rng.mpr (hright.comp hrho.tendsto_atTop)
  have hrightValues : Tendsto (fun n => P n (rightSub n)) atTop (𝓝 0) := by
    have he : (fun n => P n (rightSub n)) = fun _ : ℕ => (0:ℝ) := by
      funext n
      dsimp only [P,rightSub,virtualMovingContactPotential]
      rw [BoundedContinuousFunction.mkOfCompact_apply,ContinuousMap.coe_mk,
        Subtype.coe_mk, max_eq_right (hordered (rho n)),hrightZero]
    rw [he]
    exact tendsto_const_nhds
  have hright0 : Hlimit b = 0 := by
    rw [hHeq b ⟨hab.le,hbB.le⟩]
    exact virtual_potential_moving_anchor_eq_zero P p rightSub ⟨b,⟨hab.le,hbB.le⟩⟩
      hPlim hrightSub hrightValues
  have hNonneg t (ht : t ∈ Icc a b) : 0 ≤ Hlimit t := by
    have htB : t ∈ Icc a B := ⟨ht.1,ht.2.trans hbB.le⟩
    have hEval := (BoundedContinuousFunction.lipschitz_eval_const ⟨t,htB⟩).continuous.tendsto p |>.comp hPlim
    have hErr := (herr.comp hrho.tendsto_atTop).neg
    have hh := le_of_tendsto_of_tendsto hErr hEval (Eventually.of_forall fun n => by
      simpa only [Function.comp_def,P,virtualMovingContactPotential,BoundedContinuousFunction.mkOfCompact_apply,
        ContinuousMap.coe_mk] using hLower (rho n) t ht)
    simpa only [neg_zero,←hHeq t htB] using hh
  have hjAbs : ∀ᵐ t ∂volume.restrict (Icc a b), |j t| ≤ K^2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hh := hjBound t ⟨ht.1,ht.2.trans hbB.le⟩
    rw [abs_of_nonneg ((div_pos zero_lt_one hK2).le.trans hh.1)]
    exact hh.2
  have hfi : IntegrableOn (fun t => j t*f t) (Icc a b) := by
    have hh := hf.bdd_mul hjMono.measurable.aestronglyMeasurable hjAbs
    simpa only [IntegrableOn,mul_comm] using hh
  have hInterior s (hs : s ∈ Ioo a b) t (ht : t ∈ Ioo a b) (hst : s ≤ t) :
      Hlimit t-Hlimit s = ∫ r in s..t, j r*f r := by
    let mu := volume.restrict (Icc s t)
    have hsubset : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1.le ht.2.le
    have hsubsetB : Icc s t ⊆ Icc a B := Icc_subset_Icc hs.1.le (ht.2.le.trans hbB.le)
    have hJb n : ∀ᵐ r ∂mu, |J (rho n) r| ≤ K^2 := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      have hh := hJbound (rho n) r (hsubsetB hr)
      rw [abs_of_nonneg ((div_pos zero_lt_one hK2).le.trans hh.1)]
      exact hh.2
    have hjb : ∀ᵐ r ∂mu, |j r| ≤ K^2 := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      have hh := hjBound r (hsubsetB hr)
      rw [abs_of_nonneg ((div_pos zero_lt_one hK2).le.trans hh.1)]
      exact hh.2
    have hJlim : ∀ᵐ r ∂mu, Tendsto (fun n => J (rho n) r) atTop (𝓝 (j r)) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      simpa only [rho,Function.comp_def] using (hjLim r (hsubsetB hr)).comp hpsi.tendsto_atTop
    have hL1 := virtual_factor_gradient_product_L1 mu (J ∘ rho) (G ∘ rho) j f (sq_nonneg K)
      (fun n => (hJm (rho n)).aestronglyMeasurable) hjMono.measurable.aestronglyMeasurable
      (fun n => hGi (rho n) s t hs ht hst) (hf.mono_set hsubset) hJb hjb hJlim
      ((hGlim s t hs ht hst).comp hrho.tendsto_atTop)
    have hProductI n : IntegrableOn (fun r => J (rho n) r*G (rho n) r) (Icc s t) := by
      have hh := (hGi (rho n) s t hs ht hst).bdd_mul (hJm (rho n)).aestronglyMeasurable (hJb n)
      simpa only [IntegrableOn,mul_comm] using hh
    have hEventually : ∀ᶠ n in atTop, P n ⟨t,⟨ht.1.le,ht.2.le.trans hbB.le⟩⟩-
        P n ⟨s,⟨hs.1.le,hs.2.le.trans hbB.le⟩⟩ = ∫ r in s..t, J (rho n) r*G (rho n) r := by
      have hl := (hleft.comp hrho.tendsto_atTop).eventually (gt_mem_nhds hs.1)
      filter_upwards [hl] with n hn
      change left (rho n) < s at hn
      dsimp only [P,virtualMovingContactPotential]
      change H (rho n) (max (left (rho n)) t)-H (rho n) (max (left (rho n)) s)=
        ∫ r in s..t, J (rho n) r*G (rho n) r
      rw [max_eq_right hn.le,max_eq_right (hn.le.trans hst)]
      exact hPrimitive (rho n) s t hs ht hn.le hst
    have hh := virtual_uniform_potential_primitive_identified_eventually P p
      (fun n r => J (rho n) r*G (rho n) r) (fun r => j r*f r) hPlim
      ⟨s,⟨hs.1.le,hs.2.le.trans hbB.le⟩⟩ ⟨t,⟨ht.1.le,ht.2.le.trans hbB.le⟩⟩ hst
      hProductI (hfi.mono_set hsubset) hL1 hEventually
    simpa only [hHeq s ⟨hs.1.le,hs.2.le.trans hbB.le⟩,
      hHeq t ⟨ht.1.le,ht.2.le.trans hbB.le⟩] using hh
  refine ⟨j,hjMono,fun t ht => hjBound t ⟨ht.1,ht.2.trans hbB.le⟩,⟨?_⟩⟩
  exact ⟨Hlimit,hNonneg,hleft0,hright0,
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr hfi,
    virtual_local_primitives_extend_to_endpoints hab Hlimit (fun t => j t*f t)
      hHlimit.continuousOn hfi hInterior⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
