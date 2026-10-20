module

public import ComparisonActualHighWallCriticalMassEq22FractionalReaderAlong
public import ComparisonActualHighWallTargetThreeFractionalPricesOnStrongMasterAlong
public import ComparisonActualHighWallStrongWindowSourcesAlong
public import ComparisonActualHighWallCategoryOrders

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 48000000
set_option backward.isDefEq.respectTransparency false

theorem actual_high_wall_critical_mass_Eq22_from_physical_readers_along
    {m delta cl cu Az C0 Ct D Bclock T0 Ctarget : ℝ}
    (hCtarget : 0 < Ctarget)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D) (hT0 : 0 < T0)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum
      (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0))
    (hT : ∀n,T0 ≤ (M n).data.T) :
    Tendsto (fun n=>
      (∫u in 0..Ctarget*(M n).data.d,
        |(M n).originalMassScalarResidual u|)/(M n).data.d^4)
      atTop (𝓝 0) := by
  let c:=cu*Az+1
  have hc : 0 < c := by dsimp only [c]; positivity
  have hcout : cu*Az < c := by dsimp only [c]; linarith
  obtain ⟨L,Cenv,Csource,Cs,hL,henv,hsource,hCs,hbandRoom,w,Hwindow⟩:=
    exists_actual_high_wall_strong_window_sources_along
      Ctarget 0 1 c (1/2) hCtarget.le (by norm_num) (by norm_num) hc (by norm_num)
      hm hdelta hroom hcl hcu hAz hC0 hCt hT0
      dim hdim M hfixed hdlim hsRatio hT
  have hw : ∀ᶠn in atTop,ActualHighWallOverlapMinimum.IsActualHighWallCalibratedSlowWindow
      (M n) ((M n).data.d) L Cs (w n) := Hwindow.mono (fun _ hn=>hn.1)
  have hcutgap : Cenv < Csource := by
    obtain ⟨n,hn⟩:=Hwindow.exists
    obtain ⟨source,outer,hSourceMass,_hOuterMass,Hgeometry⟩:=hn.2.2.2.2
    have H:=Hgeometry.low_lt_source
    rw [hSourceMass] at H
    by_contra hbad
    have hle : Csource ≤ Cenv:=le_of_not_gt hbad
    exact H.not_ge (mul_le_mul_of_nonneg_right hle (M n).data.hd.le)
  obtain ⟨q,dOrder,eta,hq,hdOrder,hOrder,htheta1,htheta2,hdeficit,heta,hgap⟩:=
    actual_high_wall_category_orders hm hdelta
  let cK:=3*T0*(starMassBandConstant cu Az/cu)/16
  have hA : 0 < starMassBandConstant cu Az := star_mass_band_constant_pos hcu hAz
  have hcK : 0 < cK := by dsimp only [cK]; positivity
  have hKroom : cK ≤ 3*T0*(starMassBandConstant cu Az/cu)/8 := by
    dsimp only [cK]
    have HP : 0 < 3*T0*(starMassBandConstant cu Az/cu) := by positivity
    linarith
  obtain ⟨pReader,hpReader,Cm,Cr,Ctaylor,hCm,hCr,hCtaylor,e,he,He,Hreader⟩:=
    eventually_actual_high_wall_original_target_three_fractional_prices_on_same_strong_master_along
      dOrder hdOrder q hq hOrder htheta1 htheta2 hdeficit
      Cenv Csource (1/2) (4+2*cu) 1 henv hsource hcutgap (by norm_num) heta
      hm hdelta hroom hgap hcl hcu hAz hC0 hCt hD
      (by norm_num) (by norm_num) (by linarith) (by norm_num; linarith) hL
      hc hcout hcK hT0 hKroom hbandRoom
      dim hdim M hfixed hdlim hsRatio hT Cs hCs w hw
  apply actual_high_wall_critical_mass_Eq22_of_uniform_fractional_reader_prices_along
    pReader hpReader hCtarget hCm.le hCr.le hCtaylor.le
    hm hdelta hroom hcl hcu hAz hC0 hCt hD
    dim hdim M hfixed hdlim hsRatio e He (Eventually.of_forall he)
  filter_upwards [Hwindow,Hreader] with n hnWindow hnReader
  intro u huTarget
  obtain ⟨source,outer,_hSourceMass,_hOuterMass,Hgeometry⟩:=hnWindow.2.2.2.2
  have huStar : u.val < (w n).star.val:=huTarget.trans hnWindow.2.1
  have huSource : u.val < source.val:=
    (huStar.trans_le hnWindow.2.2.1).trans Hgeometry.low_lt_source
  have huOne : u.val ≤ 1:=huSource.le.trans
    (Hgeometry.source_lt_outer.le.trans Hgeometry.outer_le_one)
  obtain ⟨Lnet,hLnet⟩:=exists_nat_one_div_lt (M n).hxs
  have hmesh : ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs := by
    simpa only [Nat.cast_add,Nat.cast_one,one_div] using hLnet.le
  obtain ⟨us,hus,hretain,_hcoarse,hstar,hsourceRet,_houterRet,_hnodes,Hgrid⟩:=
    hnReader source outer Hgeometry Lnet hmesh [u]
      (by intro v hv; obtain rfl:=List.mem_singleton.mp hv; exact huOne)
  have hu : u∈us:=hretain u (List.mem_singleton_self u)
  let U : ℕ→ℕ:=fun k=>retainedMassPrefixIndex source.val (finiteCutMasses us k)
  refine ⟨us,hus,hu,U,?_⟩
  filter_upwards [Hgrid] with k hk
  dsimp only at hk
  let as:=finiteCutMasses us k
  let i:=retainedMassPrefixIndex u.val as
  let star:=retainedMassPrefixIndex (w n).star.val as
  have ho:=finiteCutMasses_ordered us hus k
  have Htarget:=finiteCutMasses_nodes us k hu
  have Hstar:=finiteCutMasses_nodes us k hstar
  have hi : i < star:=actual_retained_mass_strict_index as ho u (w n).star Htarget Hstar huStar
  have Hmass : partitionPoint 0 as i=u.val:=nativeRetainedCut_partitionPoint as ho u Htarget
  have hmi : partitionPoint 0 as i ≤ Cenv*(M n).data.d := by
    rw [Hmass]
    exact huStar.le.trans hnWindow.2.2.1
  obtain ⟨hs,hU,Hprices⟩:=hk
  have Hthree:=Hprices i hi hmi
  change i<U k ∧ U k≤as.length ∧ _
  exact ⟨hi.trans hs,hU,Hthree⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
