module

public import ComparisonSignedCavityActualCanonicalTwoLevelProjection
public import ComparisonActualHighWallCanonicalExteriorMoments
public import ComparisonActualHighWallTwoLevelProjection

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_high_wall_canonical_two_level_projection_fourth
    (a : ℕ) (Bclock Cmass : ℝ) (hCm : 0 ≤ Cmass)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let W:=M.data.d
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail)))
          (G : ActualNaturalBoundaryShape n a T) (f : Fin a → NativeSourceFactorForm)
          (initial : Finset (Fin a)) (x : ℝ),
          M.xs ≤ x → x ≤ W → (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀(s : T.cavityLeft.Slot)
          (E : NativeCanonicalExteriorSource n a pre mid tail T s (G.canonicalHighWallSource M f) 0 q 0)
          (e : E.Ei.Slot) (t : E.D.Slot),E.target ≠ t →
        ∀v : ℝ,W ≤ v →
          M.data.wallRadius M.alpha (partitionPoint 0 as (pre.length+mid.length+E.D.splitIndex E.target t))=v →
          M.data.wallRadius M.alpha (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → M.z ≤ v/2 →
          let qi:=fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j)
          let qs:=nativeStarSuffixClock n pre mid q
          (∫z,nativeTwoLevelProjectionFourth n E.Ei E.Es E.D E.H e E.target t qi qs qs
            (exteriorForestIRoot z) (exteriorForestStarRoot z) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
            (Cp*(n:ℝ)^(-eta)*savedWeightedExteriorScale M.xs W v
              (M.xs+partitionPoint 0 as pre.length)*(Ch^a*sourceMonomialScale x W initial))^4 := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_high_wall_two_level_projection_fourth
    (D:=D) Bclock hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  obtain ⟨Ch,hCh,HH⟩:=eventually_actual_high_wall_canonical_exterior_eighth
    (D:=D) a Bclock Cmass hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,Ch,hCh,?_⟩
  filter_upwards [HP,HH] with n hp hh
  intro M hfixed L us hus hret hmesh
  filter_upwards [hp M hfixed L us hus hret hmesh,
    hh M hfixed L us hus hret hmesh] with k hkP hkH
  dsimp only at hkP hkH ⊢
  intro pre mid tail hcut T G f initial x hxsx hxW hmass s E e t hst v hWv hvr hstar hz
  have Hproj:=hkP pre mid tail hcut E.Ei E.Es E.D E.H e E.target t hst v hWv hvr hstar hz
  have hxEq : x=M.data.d:=by rw [hfixed] at hxsx;exact le_antisymm hxW hxsx
  have hmassD e : G.sourceLowMass e≤Cmass*M.data.d:=by
    simpa only [hxEq,sourceFactorScale,ite_self] using hmass e
  have Hmoment:=hkH pre mid tail hcut T G f hmassD s E
  have Hscale : sourceMonomialScale x M.data.d initial=M.data.d^a:=by
    rw [hxEq,sourceMonomialScale_self]
  rw [←Hscale] at Hmoment
  have Hsqrt:=Real.sqrt_le_sqrt Hmoment
  have hsquare (p : ℝ) : Real.sqrt (p^8)=p^4 := by
    rw [show p^8=(p^4)^2 by ring,Real.sqrt_sq (by positivity)]
  rw [hsquare] at Hsqrt
  have HB:=mul_le_mul_of_nonneg_left Hsqrt
    (show 0 ≤ (Cp*(n:ℝ)^(-eta)*savedWeightedExteriorScale M.xs
      (M.data.d) v
      (M.xs+partitionPoint 0 (finiteCutMasses us k) pre.length))^4 by positivity)
  calc
    _ ≤ _ := Hproj
    _ ≤ _ := HB
    _ = _ := by ring

end OAI.SKFluctuations.Cavity
