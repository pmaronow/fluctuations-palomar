module

public import ComparisonSignedCavityCalibratedCanonicalSavedCubic
public import ComparisonSignedCavityCanonicalMarkedOldProduct
public import ComparisonSignedCavityActualGammaHighBound

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_gamma_canonical_saved_cubic
    (a : ℕ) (Bclock Temp Cmass Ccal : ℝ)
    (hTemp : 0≤Temp) (hCmass : 0≤Cmass) (hCcal : 1≤Ccal)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃Cp C : ℝ,0 < Cp ∧ 0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs≤1 →
        M.xs^2≤Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
          partitionPoint 0 as (pre.length+mid.length)≤Cmass*W →
        ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (s e b : T.Slot) (U : ℕ),
          0 < mid.length → pre.length+mid.length < U →
          NativePersistentLowForks pre.length (pre.length+mid.length) U T → U≤T.splitIndex s e →
          (T.splitIndex s b=pre.length ∨ T.splitIndex s b=pre.length+mid.length) →
        ∀v : ℝ,W≤v → M.R (partitionPoint 0 as (T.splitIndex s e))=v →
          M.R (partitionPoint 0 as (pre.length+mid.length))≤v/2 → M.z≤v/2 →
        ∀(G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm)
          (initial : Finset (Fin a)),
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale M.xs W initial e) →
        ∀(i j : T.Slot),i≠j → partitionPoint 0 (pre++(mid++tail)) (T.splitIndex i j)≤Cmass*W →
          |fullScalarCutGamma T U (retainedStarMixedClock n M.bf M.hf as) s e*
            nativeOriginalFreshResidual n T s e b 0 (pre.length+mid.length) 0 q 0
            (fun σ=>ActualNaturalBoundaryShape.canonicalLowRestFactor M i j σ*
              (G.canonicalMinimumSource M f).restProduct σ)|≤
            C*(n:ℝ)^(-eta)*(W*M.xs^2*(Cp^a*sourceMonomialScale M.xs W initial)) := by
  obtain ⟨Cp,Cr,hCp,hCr,HR⟩:=eventually_calibrated_canonical_saved_cubic
    a Bclock Temp Cmass Ccal hTemp hCmass hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  obtain ⟨Cg,hCg,HG⟩:=eventually_actual_minimum_bare_scalar_gamma_bound
    Bclock Temp hTemp hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,Cg*Cr,hCp,mul_pos hCg hCr,?_⟩
  filter_upwards [HR,HG] with n hnR hnG
  intro M hb hh hxs hcompare L us hus hret hmesh
  filter_upwards [hnR M hb hh hxs hcompare L us hus hret hmesh,
    hnG M hb hh hxs L us hus hret hmesh] with k hkR hkG
  dsimp only at hkR hkG ⊢
  intro pre mid tail hcut hmass T s e b U hmid hU hT hse hsb v hWv hvr hlow hz
    G f initial hmassG i j hij hmassLow
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
  have hW : 0 < W:=M.hxs.trans_le (le_max_left _ _)
  by_cases hsame : s=e
  · subst e
    simp only [nativeOriginalFreshResidual_same_zero,mul_zero,abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCg.le hCr.le)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      (mul_nonneg (mul_nonneg hW.le (sq_nonneg M.xs))
        (mul_nonneg (pow_nonneg hCp.le _) (mul_nonneg (pow_nonneg M.hxs.le _) (pow_nonneg hW.le _))))
  · have HK:=hcut.symm ▸ hkG
    have Hgamma:=HK T U (by omega) s e hsame
      (by simpa only [hcut,hvr] using (le_max_left _ _).trans hWv)
      (by simpa only [hcut,hvr] using (show M.z≤v by have hv:=hW.trans_le hWv;linarith))
    have Hgamma' : |fullScalarCutGamma T U
        (retainedStarMixedClock n M.bf M.hf (finiteCutMasses us k)) s e|≤Cg*v := by
      simpa only [hcut,hvr] using Hgamma
    exact hkR pre mid tail hcut hmass T s e b U hmid hU hT hse hsb v hWv hvr hlow hz
      G f initial hmassG i j hij hmassLow _ Cg hCg.le Hgamma'

end OAI.SKFluctuations.Cavity
