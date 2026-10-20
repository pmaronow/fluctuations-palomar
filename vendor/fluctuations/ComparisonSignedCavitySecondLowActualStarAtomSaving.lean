module

public import ComparisonSignedCavitySecondLowInheritedRawAtomBudget
public import ComparisonSignedCavitySharpOriginalLowRadius

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option maxHeartbeats 18000000

theorem actual_second_low_star_error_atom_saving
    {m delta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Cf : ℝ}
    (aDegree rBound : ℕ) (Cmass Couter Cpay : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    (hCouter : 0 ≤ Couter) (hCpay : 0 ≤ Cpay)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cs (w n)) :
    ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1)→(w n).star∈us→
      (∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs→
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          U ≤ as.length→star < U→partitionPoint 0 as U ≤ Couter*W n→
          l∈Icc (0:ℝ) 1→t∈Icc (0:ℝ) 1→T.leaves ≤ rBound→
        ∀(G : ActualNaturalBoundaryShape n aDegree T)
          (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x : ℝ),(M n).xs ≤ x→x ≤ W n→
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x (W n) initial e)→
        ∀(u z s0 w0 s1 w1 : T.Slot) (vOrd : ℝ),
          T.splitIndex u z=star→T.splitIndex s0 w0 < U→
          s0≠w0→s1≠w1→vOrd∈Icc (0:ℝ) 1→
          Cpay*|T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
            (nativeOldInitialRowProduct n T (G.canonicalMinimumSource (M n) forms).restProduct
              (nativeSmallCutOldErrorRestKernel n U b h K) u z
              (fun i : Fin 2=>nativeSmallCutOrdinaryRestKernel n U b h K (![false,true] i) (![vOrd,0] i))
              ![s0,s1] ![w0,w1]) 0| ≤
            ((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*(M n).xs^2*
              sourceMonomialScale x (W n) initial := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_second_low_actual_raw_atom_budget
    (D:=D) aDegree rBound Bclock Temp Cf Cmass hTemp hCf hCm
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  have hCerr : 0 ≤ Cerr:=actualLowErrorComparisonConstant_nonneg _ hTemp
  let R:=Cpay*C*(1+Couter)*Cerr
  have hR : 0 ≤ R:=by dsimp [R];positivity
  have HR:=eventually_actual_sharp_star_original_low_radius_saving hm hdelta hC0
    R hR M W hcanonical hWlim w hw
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [HC,HR,Hsource,HW] with n hn hc hs hw1
  have hxsW : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have hW : 0 < W n:=(M n).hxs.trans_le hxsW
  intro L us hus hstar hret hmesh
  filter_upwards [hn (M n) hs (hxsW.trans hw1) L us hus hret hmesh,
    hc us hus hstar] with jGrid hgrid hsave
  dsimp only at hgrid hsave ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let rho:=nativeOriginalCutLowErrorRadius n (M n).bf (M n).hf as star+1/(n+1:ℕ)
  have hrho : 0 ≤ rho:=add_nonneg (Real.sqrt_nonneg _) (by positivity)
  intro U T l t hU hstarU houter hl ht hT G forms initial x hxsx hxW hmass
    u z s0 w0 s1 w1 vOrd heq hOrd hne0 hne1 hv
  have Hraw:=hgrid U T l t hU hl ht hT G forms initial x (W n) hxsx hxW hmass
    u z (heq ▸ hstarU) s0 w0 s1 w1 vOrd hOrd hne0 hne1 hv
  rw [heq] at Hraw
  let p0:=sourceMonomialScale x (W n) initial
  have hp0 : 0 ≤ p0:=by
    dsimp [p0]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos ((M n).hxs.trans_le hxsx) hW initial e).le
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hnatural : 0 ≤ (M n).xs+partitionPoint 0 as (T.splitIndex s0 w0):=
    add_nonneg (M n).hxs.le (partitionPoint_mem as ho _).1
  have hsmall : (M n).xs+partitionPoint 0 as (T.splitIndex s0 w0) ≤ (1+Couter)*W n:=by
    have Hmass:=(partitionPoint_mono as ho hOrd.le).trans houter
    nlinarith only [hxsW,Hmass]
  change R*rho ≤ ((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*((M n).xs^2/W n) at hsave
  apply (mul_le_mul_of_nonneg_left Hraw hCpay).trans
  calc
    Cpay*(C*(Cerr*rho)*((M n).xs+partitionPoint 0 as (T.splitIndex s0 w0))*p0) ≤
        Cpay*(C*(Cerr*rho)*((1+Couter)*W n)*p0) := by gcongr
    _= (R*rho)*W n*p0 := by dsimp [R];ring
    _≤ (((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*((M n).xs^2/W n))*W n*p0 := by gcongr
    _= _ := by dsimp [p0];field_simp [hW.ne']

end OAI.SKFluctuations.Cavity
