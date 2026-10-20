module

public import ComparisonActualHighWallTargetThreeFractionalPricesOnStrongMasterAlong
public import ComparisonActualHighWallStrongWindowSourcesAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 48000000
set_option backward.isDefEq.respectTransparency false

theorem actual_high_wall_original_target_literal_radius_scalar_gap_along
    (Bclock : ℝ)
    {m delta cl cu Az C0 Ct D a b ca T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D)
    (hab : a ≤ b) (hca : 0 < ca) (hT : 0 < T)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hTeq : ∀n,(M n).data.T=T)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0))
    (hband : ∀ᶠn in atTop,(M n).data.rmin < (M n).xs*a ∧
      (M n).xs*b ≤ 1 ∧ ca*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*a))
    (dphys : ℕ→ℕ) (ephys : ∀n,Fin (dphys n+1)≃FeatureIndex (dim n+1)) :
    Tendsto (fun n=>(∫r in Ioo ((M n).xs*a) ((M n).xs*b),
      |(M n).radiusS r-
        scalarCovarianceResponse hT ((M n).data.scalarMassProfile (M n).alpha)
          (actualMixedClock (dim n+1) (M n).bf (M n).hf ((M n).alpha.val.val r))|)/
        (M n).xs^4) atTop (𝓝 0) := by
  have hroom : delta < 3*m:=by linarith only [hmargin,hdelta]
  let c:=cu*Az+1
  have hc : 0 < c:=by dsimp only [c];positivity
  have hcout : cu*Az < c:=by dsimp only [c];linarith
  let Rmacro : ℝ:=1/2
  have hmacro : 0 < Rmacro:=by norm_num [Rmacro]
  have hRhalf : Rmacro ≤ 1/2:=le_rfl
  let Cband:=max 0 b
  have hCband : 0 ≤ Cband:=le_max_left _ _
  have HT : ∀n,T ≤ (M n).data.T:=fun n=>(hTeq n).ge
  obtain ⟨L,Cenv,Ccut,Cs,hL,hCenv,hCcut,hCs,hbandRoom,w,Hgeometry⟩:=
    exists_actual_high_wall_strong_window_sources_along
      1 Cband 1 c Rmacro (by norm_num) hCband (by norm_num) hc hmacro
      hm hdelta hroom hcl hcu hAz hC0 hCt hT dim hdim M hfixed hdlim hsRatio HT
  have hw : ∀ᶠn in atTop,ActualHighWallOverlapMinimum.IsActualHighWallCalibratedSlowWindow
      (M n) ((M n).data.d) L Cs (w n):=Hgeometry.mono (fun _ hn=>hn.1)
  have hcutgap : Cenv < Ccut:=by
    obtain ⟨n,hn⟩:=Hgeometry.exists
    obtain ⟨source,outer,_hs,_ho,Hsource⟩:=hn.2.2.2.2
    have H:=Hsource.low_lt_source.trans_le Hsource.source_upper
    by_contra hnot
    have Hreverse:=mul_le_mul_of_nonneg_right (le_of_not_gt hnot) (M n).data.hd.le
    exact (not_lt_of_ge Hreverse) H
  obtain ⟨p,dOrder,eta,hp,hd,hOrder,htheta1,htheta2,hdeficit,heta,hgap⟩:=
    actual_high_wall_category_orders hm hdelta
  let F:=max (1+2*cu) 3
  have hFmass : 1+2*cu ≤ F:=le_max_left _ _
  have hFradius : 1+1/Rmacro ≤ F:=by
    have H : 1+1/Rmacro=3:=by norm_num [Rmacro]
    rw [H]
    exact le_max_right _ _
  let cK:=3*T*(starMassBandConstant cu Az/cu)/16
  have hcstar : 0 < starMassBandConstant cu Az/cu:=
    div_pos (star_mass_band_constant_pos hcu hAz) hcu
  have hcK : 0 < cK:=by dsimp only [cK];positivity
  have hKroom : cK ≤ 3*T*(starMassBandConstant cu Az/cu)/8:=by
    dsimp only [cK]
    have H:=mul_pos (mul_pos (by norm_num : (0:ℝ)<3) hT) hcstar
    linarith only [H]
  obtain ⟨pReader,hpReader,Cm,Cr,Ctaylor,hCm,hCr,hCtaylor,e,he,He,Hthree⟩:=
    eventually_actual_high_wall_original_target_three_fractional_prices_on_same_strong_master_along
      dOrder hd p hp hOrder htheta1 htheta2 hdeficit Cenv Ccut Rmacro F 1 hCenv hCcut
      hcutgap (by norm_num) heta hm hdelta hroom hgap hcl hcu hAz hC0 hCt hD
      hmacro hRhalf hFmass hFradius hL hc hcout hcK hT hKroom hbandRoom
      dim hdim M hfixed hdlim hsRatio HT Cs hCs w hw
  have Hprices : ∀ᶠn in atTop,∀r∈Ioo ((M n).xs*a) ((M n).xs*b),
      ActualHighWallLiteralRadiusCalibratedFractionalReaderPrices
        (M n) pReader Cm Cr Ctaylor (e n) r:=by
    filter_upwards [Hthree,Hgeometry,hband] with n hnThree hnGeometry hnBand
    obtain ⟨_hw,_htarget,hstarUpper,Hradius,source,outer,_hsource,_houter,Hsource⟩:=hnGeometry
    intro r hr
    have hr1 : r ≤ 1:=hr.2.le.trans hnBand.2.1
    have hradius : r ≤ Cband*(M n).data.d:=by
      calc
        r ≤ (M n).xs*b:=hr.2.le
        _ = b*(M n).data.d:=by rw [hfixed n];ring
        _ ≤ Cband*(M n).data.d:=mul_le_mul_of_nonneg_right (le_max_right 0 b) (M n).data.hd.le
    have hbefore : (M n).alpha.val.val r < (w n).star.val:=Hradius r hradius hr1
    have hpositive : 0 < (M n).alpha.val.val r:=
      (mul_pos hca (M n).hxs).trans_le
        (hnBand.2.2.trans ((M n).alpha.val.property.2 hr.1.le))
    let u : PositiveMass:=⟨(M n).alpha.val.val r,hpositive⟩
    have hu1 : u.val ≤ 1:=((M n).alpha.val.property.1 r).2
    have humass : u.val ≤ Cenv*(M n).data.d:=hbefore.le.trans hstarUpper
    obtain ⟨Lnet,hmesh⟩:=
      (uniformMasses_mesh_tendsto.eventually (eventually_le_nhds (M n).hxs)).exists
    obtain ⟨us,hus,hretain,hcoarse,hstar,_hsource,_houter,_hnodes,Hgrid⟩:=
      hnThree source outer Hsource Lnet hmesh [u]
        (by intro v hv; obtain rfl:=List.mem_singleton.mp hv; exact hu1)
    have hu : u∈us:=hretain u (by simp)
    let U:=fun k=>retainedMassPrefixIndex source.val (finiteCutMasses us k)
    refine ⟨u,rfl,us,hus,hu,Lnet,hcoarse,hmesh,U,?_⟩
    filter_upwards [Hgrid] with jGrid hjGrid
    dsimp only [U] at hjGrid ⊢
    obtain ⟨hs,hU,Hfinite⟩:=hjGrid
    have ho:=finiteCutMasses_ordered us hus jGrid
    have hiStar:=actual_retained_mass_strict_index (finiteCutMasses us jGrid) ho u (w n).star
      (finiteCutMasses_nodes us jGrid hu) (finiteCutMasses_nodes us jGrid hstar) hbefore
    have Hi:=nativeRetainedCut_partitionPoint (finiteCutMasses us jGrid) ho u
      (finiteCutMasses_nodes us jGrid hu)
    have hmi : partitionPoint 0 (finiteCutMasses us jGrid)
        (retainedMassPrefixIndex u.val (finiteCutMasses us jGrid)) ≤ Cenv*(M n).data.d:=by
      rw [Hi]
      exact humass
    exact ⟨hiStar.trans hs,hU,Hfinite _ hiStar hmi⟩
  have hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0):=by
    simpa only [hfixed] using hdlim
  exact actual_high_wall_fractional_radius_scalar_gap_of_calibrated_reader_prices_along
    pReader hpReader Bclock hm hdelta hmargin hcl hcu hAz hC0 hCt hab hca hT
    hCm.le hCr.le hCtaylor.le dim hdim M hfixed hTeq hxlim hband
    e (Filter.Eventually.of_forall he) He Hprices dphys ephys

end OAI.SKFluctuations.LaplaceWindowFormalization
