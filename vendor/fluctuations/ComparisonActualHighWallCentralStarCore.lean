module

public import ComparisonActualHighWallPolynomialStarCore

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 14000000
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem Potential.central_star_from_integrated_band
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (P : M.Potential) (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az)
    {a b W eta c1 s t : ℝ} (hW : 0< W) (hxs : M.xs≤ W)
    (ha : starMassBandConstant cu Az≤ a) (_hab : a≤ b) (hbW : b*W≤1)
    (hhigh : M.data.s≤ a*W)
    (hwall : M.data.rmin+M.cavityCapTravel≤((a/cu)/2)*W)
    (hslab : (∫u in Ioo (a*W) (b*W),orderedPathB (n+1) M.bf M.hf u-
        (orderedPathS (n+1) M.bf M.hf u)^2)≤ M.data.N^(-(eta/2))*W^3)
    (hcoef : M.data.N^(-(eta/2))≤(1/4)*M.data.N^(-(eta/4)-c1))
    (hfloor : M.data.N^(-delta)*(comparisonSmallMass M.data.N M.data.E)≤(1/2)*M.data.N^(-c1)*W)
    (hs : a*W≤ s) (ht : t≤ b*W) (hst : s< t) (hwidth : M.data.N^(-c1)*W≤ t-s) :
    ∃u∈Ioo s t,P.H (M.data.wallRadius M.alpha u)≤0 ∧
      orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2≤ M.data.N^(-(eta/4))*W^2 ∧
      (orderedPathS (n+1) M.bf M.hf u-M.data.wallRadius M.alpha u)^2≤
        16*M.cavityCapTravel^2+2*(M.data.N^(-(eta/4))*W^2) := by
  have ha0 : 0< a:=(star_mass_band_constant_pos hcu hAz).trans_le ha
  have hc : 0< a/cu:=div_pos ha0 hcu
  let F:=fun u=>orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2
  have hsubunit : Ioo (a*W) (b*W)⊆Icc (0:ℝ) 1:=
    fun u hu=>⟨(mul_pos ha0 hW).le.trans hu.1.le,hu.2.le.trans hbW⟩
  have hiF : IntegrableOn F (Icc (0:ℝ) 1):=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
      (physicalOrderedThermal_intervalIntegrable n M.bf M.hf
        (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha))
  have hsub : Ioo s t⊆Ioo (a*W) (b*W):=fun u hu=>⟨hs.trans_lt hu.1,hu.2.trans_le ht⟩
  have Hmono : (∫u in Ioo s t,F u)≤∫u in Ioo (a*W) (b*W),F u:=by
    apply setIntegral_mono_set (hiF.mono_set hsubunit) _ (Eventually.of_forall hsub)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hui:=hsubunit hu
    have hup : 0< u:=(mul_pos ha0 hW).trans hu.1
    exact sub_nonneg.mpr (orderedPath_SK_bounds (n+1) (by omega) M.bf M.hf
      (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) ⟨hup,hui.2⟩).2.2.1
  have HI : (∫u in Ioo s t,F u)≤ M.data.N^(-(eta/2))*W^3:=Hmono.trans hslab
  let threshold:=M.data.N^(-(eta/4))*W^2
  have hthreshold : 0< threshold:=by dsimp only [threshold];positivity
  have hstep : 0< M.data.N^(-c1)*W:=mul_pos (Real.rpow_pos_of_pos M.data.hN _) hW
  have hpow : M.data.N^(-(eta/4)-c1)=M.data.N^(-(eta/4))*M.data.N^(-c1):=by
    rw [←Real.rpow_add M.data.hN];congr 1
  have hthermalbound : (∫u in Ioo s t,F u)<
      threshold*((t-s)-M.data.N^(-delta)*(comparisonSmallMass M.data.N M.data.E)):=by
    calc
      _≤ M.data.N^(-(eta/2))*W^3:=HI
      _≤((1/4)*M.data.N^(-(eta/4)-c1))*W^3:=
        mul_le_mul_of_nonneg_right hcoef (pow_pos hW 3).le
      _=threshold*((1/4)*M.data.N^(-c1)*W):=by rw [hpow];dsimp only [threshold];ring
      _< threshold*((1/2)*M.data.N^(-c1)*W):=
        mul_lt_mul_of_pos_left (by nlinarith only [hstep]) hthreshold
      _≤_:=mul_le_mul_of_nonneg_left (by linarith only [hfloor,hwidth]) hthreshold.le
  have haway : ∀u∈Ioo s t,M.data.rmin+M.cavityCapTravel< M.data.wallRadius M.alpha u:=by
    intro u hu
    have HR:=M.actual_closed_regular_mass_band_radius_bounds hcl hcu hAz hW hxs ha hbW hhigh
      (show u∈Icc (a*W) (b*W) from ⟨(hsub hu).1.le,(hsub hu).2.le⟩)
    have HC : 0<(a/cu)*W:=mul_pos hc hW
    linarith only [hwall,HR.1,HC]
  exact P.exists_thermal_good_star_off_floor (hhigh.trans hs) hst (ht.trans hbW)
    hthreshold.le haway hthermalbound

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
