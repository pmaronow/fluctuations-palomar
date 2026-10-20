module

public import ComparisonActualHighWallConstantForestCubicPricesAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 36000000
set_option backward.isDefEq.respectTransparency false

 theorem ActualHighWallConstantForestCubicPricesOnGrid.mono
    {n level : ℕ} {m delta cl cu Az C0 Ct D Bclock C C' : ℝ}
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {as : List PositiveMass} {star U : ℕ} {hs : star < U} {hU : U ≤ as.length}
    (H : ActualHighWallConstantForestCubicPricesOnGrid level C M as star U hs hU)
    (HCC : C ≤ C') :
    ActualHighWallConstantForestCubicPricesOnGrid level C' M as star U hs hU := by
  dsimp only [ActualHighWallConstantForestCubicPricesOnGrid] at H ⊢
  exact ⟨H.1.trans (mul_le_mul_of_nonneg_right HCC (pow_nonneg M.data.hd.le 3)),
    H.2.1.trans (mul_le_mul_of_nonneg_right HCC (sq_nonneg M.data.d)),
    H.2.2.trans (mul_le_mul_of_nonneg_right HCC (pow_nonneg M.data.hd.le 4))⟩

 theorem eventually_actual_high_wall_constant_forest_all_levels_cubic_prices_along
    {m delta cl cu Az C0 Ct D Bclock L eta c cK : ℝ}
    (depth dOrder : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (htheta1 : 1 ≤ 4/p) (htheta2 : 4/p ≤ 2)
    (hdeficit : 2-4/p ≤ actualMassSavingExponent m delta/128)
    (Cmass Ccut Rmacro F Cx : ℝ) (hCm : 1 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    (hCx : 0 < Cx) (heta : 0 < eta)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) (hL : 0 < L)
    (hc : 0 < c) (hcout : cu*Az < c) (hcK : 0 < cK)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0))
    (Cs : ℝ) (hCs : 0 < Cs) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,ActualHighWallOverlapMinimum.IsActualHighWallCalibratedSlowWindow
      (M n) ((M n).data.d) L Cs (w n)) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses Lnet,u∈us) →
      ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀source outer : PositiveMass,
        ActualHighWallStrongSourceMasses (M n) Cmass Ccut Cx c Rmacro source outer →
        source∈us → outer∈us →
        (∀j ≤ nativeDyadicCutDepth source.val,nativeDyadicMassCut source.val source.property j∈us) →
        (w n).star.val ≤ Cmass*(M n).data.d →
        cK*(M n).data.d ≤ actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let U:=retainedMassPrefixIndex source.val as
        ∃hs : star < U,∃hU : U ≤ as.length,
          ∀level < depth,ActualHighWallConstantForestCubicPricesOnGrid level C (M n) as star U hs hU := by
  let P (level : ℕ) (C : ℝ) (n : ℕ) : Prop :=
    ∀(Lnet : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses Lnet,u∈us) →
      ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀source outer : PositiveMass,
        ActualHighWallStrongSourceMasses (M n) Cmass Ccut Cx c Rmacro source outer →
        source∈us → outer∈us →
        (∀j ≤ nativeDyadicCutDepth source.val,nativeDyadicMassCut source.val source.property j∈us) →
        (w n).star.val ≤ Cmass*(M n).data.d →
        cK*(M n).data.d ≤ actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let U:=retainedMassPrefixIndex source.val as
        ∃hs : star < U,∃hU : U ≤ as.length,
          ActualHighWallConstantForestCubicPricesOnGrid level C (M n) as star U hs hU
  have Hprice : ∀level < depth,∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,P level C n:=by
    intro level hlevel
    exact eventually_actual_high_wall_constant_forest_level_cubic_prices_along
      (D:=D) level dOrder hd p hp hOrder htheta1 htheta2 hdeficit Cmass Ccut Rmacro F Cx hCm hCcut
      hCx heta hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius hL
      hc hcout hcK dim hdim M hfixed hdlim hsRatio Cs hCs w hw
  have Hmono : ∀level C C' n,C ≤ C' → P level C n → P level C' n:=by
    intro level C C' n HCC HP
    dsimp only [P] at HP ⊢
    intro Lnet us hus hret hmesh hstar source outer Hgeometry hsource houter hnodes hmass hclock
    filter_upwards [HP Lnet us hus hret hmesh hstar source outer Hgeometry hsource houter hnodes hmass hclock]
      with jGrid hj
    obtain ⟨hs,hU,H⟩:=hj
    exact ⟨hs,hU,H.mono HCC⟩
  obtain ⟨C,hC,Hfamily⟩:=exists_uniform_positive_finite_level_price_envelope depth P Hprice Hmono
  refine ⟨C,hC,?_⟩
  filter_upwards [Hfamily] with n hn
  intro Lnet us hus hret hmesh hstar source outer Hgeometry hsource houter hnodes hmass hclock
  have Hlevels:=fun level : Fin depth=>hn level.val level.isLt Lnet us hus hret hmesh hstar
    source outer Hgeometry hsource houter hnodes hmass hclock
  have Hfine:=Filter.eventually_all.mpr Hlevels
  filter_upwards [Hfine] with jGrid hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex source.val as
  have ho:=finiteCutMasses_ordered us hus jGrid
  obtain ⟨hstar0,hs,hUV,hV,_⟩:=Hgeometry.retained_source_geometry as ho (w n).star
    (finiteCutMasses_nodes us jGrid hstar) (finiteCutMasses_nodes us jGrid hsource)
    (finiteCutMasses_nodes us jGrid houter) hmass
  have hU : U ≤ as.length:=hUV.le.trans hV
  refine ⟨hs,hU,?_⟩
  intro level hlevel
  obtain ⟨hs',hU',H⟩:=hj ⟨level,hlevel⟩
  exact H

end OAI.SKFluctuations.Cavity
