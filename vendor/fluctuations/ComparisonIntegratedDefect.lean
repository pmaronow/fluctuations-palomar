module

public import NegativeComparisonGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem potential_comparison_integrated_defect
    {H J p S B α k M : ℝ → ℝ} {C : ℝ≥0} {W : ℝ}
    (hW : 0<W) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀ t∈Icc (0:ℝ) 1,0<J t)
    (hd : ∀ᵐ t,t∈Icc (0:ℝ) 1→HasDerivAt H
      (J t*comparisonBracket (p t) t (S t) (B t)) t)
    (hbang : ∀ᵐ t,t∈Icc (0:ℝ) 1→
      (H t<0→deriv α t=M (α t)) ∧ (0<H t→deriv α t=k t))
    (hcontact : ∀ᵐ t,t∈Icc (0:ℝ) 1→H t=0→(S t-t)^2≤B t-(S t)^2)
    (hp : MonotoneOn p (Ioc (0:ℝ) 1))
    (hpb : ∀ t∈Ioc (0:ℝ) 1,p t∈Icc (0:ℝ) 1)
    (hS : MonotoneOn S (Icc (0:ℝ) 1))
    (hBm : MonotoneOn B (Icc (0:ℝ) 1))
    (hSb : ∀ t∈Icc (0:ℝ) 1,S t∈Icc (0:ℝ) 1)
    (hBb : ∀ t∈Icc (0:ℝ) 1,B t∈Icc ((S t)^2) 1)
    (hα : LipschitzOnWith C α (Icc (0:ℝ) 1))
    (hm : StrictMonoOn α (Icc (0:ℝ) 1))
    (hαr : ∀ t∈Icc (0:ℝ) 1,α t∈Icc (0:ℝ) 1)
    (hα0 : α 0=0) (hα1 : α 1=1)
    (hkc : ContinuousOn k (Icc (0:ℝ) 1))
    (hk : ∀ t∈Icc (0:ℝ) 1,0≤k t)
    (hMc : ContinuousOn M (Icc (0:ℝ) 1))
    (hM : ∀ u∈Icc (0:ℝ) 1,0<M u)
    (htravel : (∫u in (0:ℝ)..1,1/M u)≤W) :
    (∫r in Icc (0:ℝ) 1,deriv α r*(S r-r)^2)≤
      (∫r in (0:ℝ)..1,k r)+64*W^2+
        2*(∫r in Icc (0:ℝ) 1,deriv α r*(B r-(S r)^2)) := by
  have hac : AbsolutelyContinuousOnInterval α 0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K:=C)
    simpa only [uIcc_of_le zero_le_one] using hα
  have hden : ∀ᵐ r,r∈Icc (0:ℝ) 1→0≤deriv α r := by
    apply (lipschitz_ae_deriv_lower_iff zero_le_one hα (g:=fun _=>0) continuousOn_const).mpr
    intro x hx y hy hxy
    simpa only [intervalIntegral.integral_zero] using sub_nonneg.mpr (hm.monotoneOn hx hy hxy)
  have hSq : MonotoneOn (fun r=>(S r)^2) (Icc (0:ℝ) 1) := by
    intro x hx y hy hxy
    exact pow_le_pow_left₀ (hSb x hx).1 (hS hx hy hxy) 2
  have hDint : IntervalIntegrable (fun r=>B r-(S r)^2) volume 0 1 :=
    (show MonotoneOn B (uIcc (0:ℝ) 1) by simpa only [uIcc_of_le zero_le_one] using hBm).intervalIntegrable.sub
      (show MonotoneOn (fun r=>(S r)^2) (uIcc (0:ℝ) 1) by simpa only [uIcc_of_le zero_le_one] using hSq).intervalIntegrable
  have hDmeas := ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hDint).aestronglyMeasurable
  have hαint := (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hac.intervalIntegrable_deriv
  have hthermal : IntegrableOn (fun r=>deriv α r*(B r-(S r)^2)) (Icc (0:ℝ) 1) := by
    apply hαint.mul_bdd hDmeas (c:=1)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (hBb r hr).1)]
    nlinarith [(hBb r hr).2,sq_nonneg (S r)]
  have hkint : IntegrableOn k (Icc (0:ℝ) 1) volume := hkc.integrableOn_Icc
  have hright : IntegrableOn
      (fun r=>k r+deriv α r*(64*W^2)+2*(deriv α r*(B r-(S r)^2))) (Icc (0:ℝ) 1) :=
    (hkint.add (hαint.mul_const _)).add (hthermal.const_mul _)
  have hnon : 0≤ᵐ[volume.restrict (Icc (0:ℝ) 1)]
      (fun r=>deriv α r*(S r-r)^2) := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [hden] with r hdr hr
    exact mul_nonneg (hdr hr) (sq_nonneg _)
  have hle : (fun r=>deriv α r*(S r-r)^2)≤ᵐ[volume.restrict (Icc (0:ℝ) 1)]
      (fun r=>k r+deriv α r*(64*W^2)+2*(deriv α r*(B r-(S r)^2))) := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [hbang,hcontact,hden,volume.ae_ne (0:ℝ)] with r hrbang hrzero hdr hr0 hr
    have hr' : r∈Ioc (0:ℝ) 1 := ⟨lt_of_le_of_ne hr.1 hr0.symm,hr.2⟩
    have hd0 := hdr hr
    have hD : 0≤B r-(S r)^2 := sub_nonneg.mpr (hBb r hr).1
    have hweight : 0≤deriv α r*(64*W^2) := mul_nonneg hd0 (by positivity)
    have hweightD : 0≤deriv α r*(B r-(S r)^2) := mul_nonneg hd0 hD
    rcases lt_trichotomy (H r) 0 with hneg|hzero|hpos
    · have hab := potential_negative_comparison_mismatch hW hr' hH hJ hd
        (hbang.mono (fun t ht hti=>(ht hti).1)) hneg hp hpb
        (hS.mono Ioc_subset_Icc_self) (hBm.mono Ioc_subset_Icc_self)
        (fun t ht=>hSb t ⟨ht.1.le,ht.2⟩) (fun t ht=>(hBb t ⟨ht.1.le,ht.2⟩).1)
        hα hm hαr hMc hM htravel
      have hmul := mul_le_mul_of_nonneg_left hab hd0
      nlinarith [hk r hr]
    · have hmul := mul_le_mul_of_nonneg_left (hrzero hr hzero) hd0
      nlinarith [hk r hr]
    · have hsq : (S r-r)^2≤1 := by nlinarith [(hSb r hr).1,(hSb r hr).2,hr.1,hr.2]
      rw [(hrbang hr).2 hpos] at hweight hweightD ⊢
      have hmul := mul_le_mul_of_nonneg_left hsq (hk r hr)
      nlinarith
  have hleint := integral_mono_of_nonneg hnon hright hle
  have hsumint : Integrable (fun r=>k r+deriv α r*(64*W^2))
      (volume.restrict (Icc (0:ℝ) 1)) := by
    exact hkint.add (hαint.mul_const (64*W^2))
  have htwoInt : Integrable (fun r=>2*(deriv α r*(B r-(S r)^2)))
      (volume.restrict (Icc (0:ℝ) 1)) := by
    exact hthermal.const_mul 2
  have hconstInt : Integrable (fun r=>deriv α r*(64*W^2))
      (volume.restrict (Icc (0:ℝ) 1)) := hαint.mul_const (64*W^2)
  have hrightEq : (∫r in Icc (0:ℝ) 1,
      k r+deriv α r*(64*W^2)+2*(deriv α r*(B r-(S r)^2)))=
      (∫r in (0:ℝ)..1,k r)+64*W^2+
        2*(∫r in Icc (0:ℝ) 1,deriv α r*(B r-(S r)^2)) := by
    rw [integral_add (μ:=volume.restrict (Icc (0:ℝ) 1)) (f:=fun r=>k r+deriv α r*(64*W^2))
        (g:=fun r=>2*(deriv α r*(B r-(S r)^2)))
        hsumint htwoInt,
      integral_add (μ:=volume.restrict (Icc (0:ℝ) 1)) (f:=k)
        (g:=fun r=>deriv α r*(64*W^2)) hkint hconstInt,
      integral_const_mul,integral_mul_const,
      integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le zero_le_one,
      integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le zero_le_one,
      hac.integral_deriv_eq_sub,hα0,hα1]
    simp
  exact hleint.trans_eq hrightEq

end OAI.SKFluctuations.LaplaceWindowFormalization
