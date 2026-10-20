module

public import ComparisonSignedCavityRestAllHighResampling
public import ComparisonSignedCavityCanonicalRestProductRates
public import ComparisonSignedCavityActualRestPhysicalRaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem native_sampled_rest_root_variance_eq (n : ℕ) (b h : ℝ→ℝ≥0) (as : List PositiveMass) :
    (fun i=>Real.toNNReal (restFiniteRealVariance n
      (Sum.elim (fun _=>(b (partitionPoint 0 as 0):ℝ))
        (fun _=>(h (partitionPoint 0 as 0):ℝ))) i))=
      restFiniteVariance n (nativeSampledRestClock n b h 0) := by
  rw [←restFiniteVariance_toNNReal]
  congr 1
  funext i
  cases i <;> simp [partitionPoint,nativeSampledRestClock]

theorem eventually_actual_minimum_bare_rest_all_high_resampling
    (ell : ℕ) (Bclock Temp Ccal Rmacro F : ℝ)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∀ᶠn : ℕ in atTop,
      ∀a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      (∀u,a.b u=Temp) → (∀u,a.h u=0) → a.xs ≤ 1 →
      a.xs^2 ≤ Ccal^2*laplaceComparisonStrength a.context.d a.lam a.xs→
      ∀(L : ℕ) (us : List PositiveMass),(∀v∈us,v.val ≤ 1) →
        (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ a.xs →
      ∀ᶠj : ℕ in atTop,
        let as:=finiteCutMasses us j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(a.bf (partitionPoint 0 as j):ℝ)) (fun _=>(a.hf (partitionPoint 0 as j):ℝ))
        let Q:=fun j=>restFiniteRealVariance n (q j)
        let W:=max a.xs (Real.sqrt (laplaceComparisonStrength a.context.d a.lam a.xs))
        ∀(low high : ℕ),high ≤ as.length→W ≤ Rmacro/2→
          4*W ≤ a.R (partitionPoint 0 as high)→
          a.z ≤ min (a.R (partitionPoint 0 as high)/8) (Rmacro/4)→
          a.R (partitionPoint 0 as low) ≤ min (a.R (partitionPoint 0 as high)/8) (Rmacro/4)→
          originalBoundaryResamplingMoment n (ell+1) as Q low high ≤ 
            (2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*a.xs) W
              (partitionPoint 0 as high))^(2*(ell+1)) := by
  obtain ⟨Cr,hCr,HR⟩:=eventually_actual_minimum_bare_rest_physical_raw_ratio (D:=D)
    ell Bclock Temp hm hdelta hroom hcl hcu hAz hC0 hCt
  have HS:=eventually_actual_rest_all_high_resampling_from_raw (delta:=delta) (Az:=Az) (Ct:=Ct) (D:=D)
    ell Bclock Ccal Rmacro F Cr hCr.le hm hgap hcl hcu hC0 hCcal hmacro hRhalf hFmass hFradius
  filter_upwards [HR,HS] with n hraw hsave
  intro M hb hh hxs hcompare L us hus hret hmesh
  filter_upwards [hraw M hb hh hxs L us hus hret hmesh,hsave M hcompare us hus] with k hk hksave
  dsimp only at hksave ⊢
  apply hksave
  rw [←native_sampled_rest_root_variance_eq n M.bf M.hf (finiteCutMasses us k)] at hk
  exact hk

theorem eventually_actual_minimum_canonical_rest_product_resampling
    (a : ℕ) (ha : 0 < a) (Bclock Temp Cmass Ccal Rmacro F : ℝ)
    (hTemp : 0 ≤ Temp) (hCm : 0 ≤ Cmass)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,1 ≤ C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (f : Fin a → NativeSourceFactorForm) (initial : Finset (Fin a)) (v : ℝ),
          0 < v → W ≤ Rmacro/2 →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale M.xs W initial e) →
        ∀(j' : Fin a → T.Slot) (hne : ∀e,G.i e≠j' e),
          (∀e,T.splitIndex (G.i e) (G.j e)=T.splitIndex (G.i e) (j' e)) →
          (∀e,G.j e≠j' e →
            let rh:=M.R (partitionPoint 0 as (T.splitIndex (G.j e) (j' e)))
            4*W ≤ rh ∧ M.z ≤ min (rh/8) (Rmacro/4) ∧
            M.R (G.sourceLowMass e) ≤ min (rh/8) (Rmacro/4) ∧
            v ≤ partitionPoint 0 as (T.splitIndex (G.j e) (j' e))) →
        T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun σ=>((G.canonicalMinimumSource M f).restProduct σ-
            ((G.retarget j' hne).canonicalMinimumSource M f).restProduct σ)^2) 0 ≤
          ((a:ℝ)*(1+Temp)*(2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs) W v)/M.xs*
            (C^a*sourceMonomialScale M.xs W initial))^2 := by
  have hell : a-1+1=a:=by omega
  obtain ⟨Cr,hCr,HR⟩:=eventually_actual_minimum_bare_rest_physical_raw_ratio (D:=D)
    (a-1) Bclock Temp hm hdelta hroom hcl hcu hAz hC0 hCt
  simp only [hell] at HR
  obtain ⟨C,hC,HP⟩:=eventually_actual_canonical_rest_product_from_raw (D:=D) a ha
    Bclock Temp Cmass Ccal Rmacro F Cr hTemp hCm hCr.le hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  refine ⟨C,hC,?_⟩
  filter_upwards [HR,HP] with n hraw hprod
  intro M hb hh hxs hcompare L us hus hret hmesh
  filter_upwards [hraw M hb hh hxs L us hus hret hmesh,
    hprod M hb hh hxs hcompare L us hus hret hmesh] with k hk hkprod
  dsimp only at hkprod ⊢
  apply hkprod
  rw [←native_sampled_rest_root_variance_eq n M.bf M.hf (finiteCutMasses us k)] at hk
  exact hk

end OAI.SKFluctuations.Cavity
