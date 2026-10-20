module

public import ComparisonSignedCavityActualCanonicalStarTwoLevelProjection
public import ComparisonSignedCavityInheritedCanonicalExteriorMoments
public import ComparisonSignedCavityInheritedStarTwoLevelProjection

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_canonical_star_two_level_projection_fourth
    (a : ℕ) (Bclock Temp Cf Cmass Ccal : ℝ) (hCf : 0 ≤ Cf) (hTemp : 0 ≤ Temp)
    (hCm : 0 ≤ Cmass) (hCcal : 1 ≤ Ccal)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail)))
          (G : ActualNaturalBoundaryShape n a T) (f : Fin a → NativeSourceFactorForm)
          (initial : Finset (Fin a)) (x : ℝ),
          M.xs ≤ x → x ≤ W → (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀(s : T.cavityLeft.Slot)
          (E : NativeCanonicalExteriorSource n a pre mid tail T s (G.canonicalMinimumSource M f) 0 q 0)
          (e : E.Es.Slot) (t : E.D.Slot),E.target ≠ t →
        ∀v : ℝ,W ≤ v →
          M.R (partitionPoint 0 as (pre.length+mid.length+E.D.splitIndex E.target t))=v →
          M.R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → M.z ≤ v/2 →
          let qi:=fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j)
          let qs:=nativeStarSuffixClock n pre mid q
          (∫z,nativeTwoLevelProjectionFourth n E.Es E.Ei E.D (fun ζ η=>E.H η ζ) e E.target t qs qi qs
            (exteriorForestStarRoot z) (exteriorForestIRoot z) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
            (Cp*(n:ℝ)^(-eta)*savedWeightedExteriorScale M.xs W v
              (M.xs+partitionPoint 0 as (pre.length+mid.length))*(Ch^a*sourceMonomialScale x W initial))^4 := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_star_two_level_projection_fourth
    (D:=D) Bclock Temp Cf Ccal hCf hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  obtain ⟨Ch,hCh,HH⟩:=eventually_actual_minimum_inherited_canonical_exterior_eighth
    (D:=D) a Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,Ch,hCh,?_⟩
  filter_upwards [HP,HH] with n hp hh
  intro M hsource hxs hcompare L us hus hret hmesh
  filter_upwards [hp M hsource hxs hcompare L us hus hret hmesh,
    hh M hsource hxs L us hus hret hmesh] with k hkP hkH
  dsimp only at hkP hkH ⊢
  intro pre mid tail hcut T G f initial x hxsx hxW hmass s E e t hst v hWv hvr hstar hz
  have Hproj:=hkP pre mid tail hcut E.Ei E.Es E.D E.H e E.target t hst v hWv hvr hstar hz
  have Hmoment:=hkH pre mid tail hcut T G f initial x _ hxsx hxW hmass s E
  have Hsqrt:=Real.sqrt_le_sqrt Hmoment
  have hsquare (p : ℝ) : Real.sqrt (p^8)=p^4 := by
    rw [show p^8=(p^4)^2 by ring,Real.sqrt_sq (by positivity)]
  rw [hsquare] at Hsqrt
  have HB:=mul_le_mul_of_nonneg_left Hsqrt
    (show 0 ≤ (Cp*(n:ℝ)^(-eta)*savedWeightedExteriorScale M.xs
      (max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))) v
      (M.xs+partitionPoint 0 (finiteCutMasses us k) (pre.length+mid.length)))^4 by positivity)
  calc
    _ ≤ _ := Hproj
    _ ≤ _ := HB
    _ = _ := by ring

end OAI.SKFluctuations.Cavity
