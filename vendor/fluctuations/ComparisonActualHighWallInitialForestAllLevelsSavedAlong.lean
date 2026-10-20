module

public import ComparisonActualHighWallInitialForestSavedLevelAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 48000000

structure ActualHighWallInitialForestSavedLevelConstants (level : ℕ) where
  Ca : ℝ
  Cg : ℝ
  Cl : ℝ
  Cj : ℝ
  C4 : ℝ
  CY : ℝ
  Ch : ℝ
  Cgl : ℝ
  Cjl : ℝ
  Cd : ℝ
  C : Fin (1+level) → ℝ
  CiU : Fin (1+level) → ℝ
  CiB : Fin (1+level) → ℝ
  CiM : Fin (1+level) → ℝ
  Cf : ℝ
  Cr : ℝ
  Cfirst : ℝ
  Cfr : ℝ
  hCa : 0 < Ca
  hCg : 0 < Cg
  hCl : 0 < Cl
  hCj : 0 < Cj
  hC4 : 0 < C4
  hCY : 0 < CY
  hCh : 0 < Ch
  hCgl : 0 < Cgl
  hCjl : 0 < Cjl
  hCd : 0 < Cd
  hC : ∀a, 0 < C a ∧ 0 < CiU a ∧ 0 < CiB a ∧ 0 < CiM a
  hCf : 0 < Cf
  hCr : 0 < Cr
  hCfirst : 0 < Cfirst
  hCfr : 0 < Cfr

def ActualHighWallInitialForestSavedLevelConstants.PriceOnGrid
    {n level : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (P : ActualHighWallInitialForestSavedLevelConstants level) (eta Ccut cK : ℝ)
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i star U : ℕ) (hi : i < star)
    (hs : star < U) (hU : U ≤ as.length) : Prop :=
  ActualHighWallInitialForestSavedLevelPricesOnGrid
    P.Ca P.Cg P.Cl P.Cj P.C4 P.CY P.Ch P.Cgl P.Cjl P.Cd
    P.C P.CiU P.CiB P.CiM P.Cf P.Cr P.Cfirst P.Cfr eta Ccut cK
    M as i star U hi hs hU

theorem exists_actual_high_wall_initial_forest_all_levels_saved_prices_along
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
    ∃P : (j : Fin depth) → ActualHighWallInitialForestSavedLevelConstants j.val,
      ∀ᶠn in atTop, ∀(Lnet : ℕ) (us : List PositiveMass),
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
        ∀j : Fin depth, ∃hs : star < U, ∃hU : U ≤ as.length,
          ∀i : ℕ,∀hi : i < star,partitionPoint 0 as i ≤ Cmass*(M n).data.d →
            (P j).PriceOnGrid eta Ccut cK (M n) as i star U hi hs hU := by
  classical
  let Stage (j : Fin depth) (P : ActualHighWallInitialForestSavedLevelConstants j.val) (n : ℕ) : Prop :=
    ∀(Lnet : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses Lnet,u∈us) →
      ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀source outer : PositiveMass,
        ActualHighWallStrongSourceMasses (M n) Cmass Ccut Cx c Rmacro source outer →
        source∈us → outer∈us →
        (∀k ≤ nativeDyadicCutDepth source.val,nativeDyadicMassCut source.val source.property k∈us) →
        (w n).star.val ≤ Cmass*(M n).data.d →
        cK*(M n).data.d ≤ actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let U:=retainedMassPrefixIndex source.val as
        ∃hs : star < U, ∃hU : U ≤ as.length,
          ∀i : ℕ,∀hi : i < star,partitionPoint 0 as i ≤ Cmass*(M n).data.d →
            P.PriceOnGrid eta Ccut cK (M n) as i star U hi hs hU
  have Hexists : ∀j : Fin depth,
      ∃P : ActualHighWallInitialForestSavedLevelConstants j.val,
        ∀ᶠn in atTop, Stage j P n := by
    intro j
    obtain ⟨Ca,Cg,Cl,Cj,C4,CY,Ch,Cgl,Cjl,Cd,
      hCa,hCg,hCl,hCj,hC4,hCY,hCh,hCgl,hCjl,hCd,
      C,CiU,CiB,CiM,Cf,Cr,Cfirst,Cfr,hC,hCf,hCr,hCfirst,hCfr,H⟩ :=
      eventually_actual_high_wall_initial_forest_saved_level_prices_along
        (D:=D) j.val dOrder hd p hp hOrder htheta1 htheta2 hdeficit
        Cmass Ccut Rmacro F Cx hCm hCcut hCx heta hm hdelta hroom hgap
        hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius hL
        hc hcout hcK dim hdim M hfixed hdlim hsRatio Cs hCs w hw
    let P : ActualHighWallInitialForestSavedLevelConstants j.val :=
      ⟨Ca,Cg,Cl,Cj,C4,CY,Ch,Cgl,Cjl,Cd,C,CiU,CiB,CiM,Cf,Cr,Cfirst,Cfr,
        hCa,hCg,hCl,hCj,hC4,hCY,hCh,hCgl,hCjl,hCd,hC,hCf,hCr,hCfirst,hCfr⟩
    refine ⟨P,?_⟩
    simpa only [Stage,ActualHighWallInitialForestSavedLevelConstants.PriceOnGrid,P] using H
  let P : (j : Fin depth) → ActualHighWallInitialForestSavedLevelConstants j.val :=
    fun j => Classical.choose (Hexists j)
  have HP : ∀j : Fin depth,∀ᶠn in atTop,Stage j (P j) n :=
    fun j => Classical.choose_spec (Hexists j)
  refine ⟨P,?_⟩
  have Hn : ∀ᶠn in atTop,∀j : Fin depth,Stage j (P j) n :=
    Filter.eventually_all.mpr HP
  filter_upwards [Hn] with n hn
  intro Lnet us hus hret hmesh hstar source outer Hgeometry hsource houter hnodes hmass hclock
  have Hgrid : ∀ᶠjGrid in atTop,∀j : Fin depth,
      let as:=finiteCutMasses us jGrid
      let star:=retainedMassPrefixIndex (w n).star.val as
      let U:=retainedMassPrefixIndex source.val as
      ∃hs : star < U, ∃hU : U ≤ as.length,
        ∀i : ℕ,∀hi : i < star,partitionPoint 0 as i ≤ Cmass*(M n).data.d →
          (P j).PriceOnGrid eta Ccut cK (M n) as i star U hi hs hU := by
    apply Filter.eventually_all.mpr
    intro j
    exact hn j Lnet us hus hret hmesh hstar source outer Hgeometry hsource houter hnodes hmass hclock
  exact Hgrid

end OAI.SKFluctuations.Cavity
