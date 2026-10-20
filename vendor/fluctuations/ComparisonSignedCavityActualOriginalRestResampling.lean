module

public import ComparisonSignedCavityActualRestBoundaryResampling

@[expose] public section

noncomputable section
set_option maxHeartbeats 9000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

def nativeRestEndpointDifference (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (b s e : T.Slot) (σ : T.cavityLeft.Assignment) : ℝ :=
  deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot b),false))
    (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot s),false))-
  deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot b),false))
    (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot e),false))

theorem native_rest_endpoint_coincidence_zero (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (b s : T.Slot) (σ : T.cavityLeft.Assignment) :
    nativeRestEndpointDifference n T b s s σ=0 := by
  simp only [nativeRestEndpointDifference,sub_self]

theorem native_rest_old_product_endpoint_cauchy (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (q : ℕ → RestCoordinate n → ℝ) (P : T.cavityLeft.Assignment → ℝ)
    (b s e : T.Slot) {p r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r)
    (hP : T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>|P σ|^2) 0 ≤ p^2)
    (hD : T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>|nativeRestEndpointDifference n T b s e σ|^2) 0 ≤ r^2) :
    |T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>P σ*nativeRestEndpointDifference n T b s e σ) 0| ≤ p*r := by
  simp only [sq_abs] at hP hD
  have HDnonneg : 0 ≤ T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>nativeRestEndpointDifference n T b s e σ^2) 0:=by
    unfold ClockTree.disorderExpect
    exact Finset.sum_nonneg fun σ _=>mul_nonneg
      ((T.cavityLeft.disorderWeight_probability (restWeight_pos n) (restFeature n) ho 0 q 0).1 σ)
      (sq_nonneg _)
  have H:=(T.cavityLeft.disorderExpect_mul_sq_le (restWeight_pos n) (restFeature n) ho
    0 q P (nativeRestEndpointDifference n T b s e) 0).trans
    (mul_le_mul hP hD HDnonneg (sq_nonneg p))
  rw [←mul_pow] at H
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hp hr)).mp (by simpa only [sq_abs] using H)

theorem eventually_actual_minimum_original_rest_endpoint_resampling
    (ell : ℕ) (Bclock Temp Ccal Rmacro F : ℝ)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∀ᶠn : ℕ in atTop,
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
        ∀(T : ClockTree (Spin n×Bool) as) (b s e : T.Slot),s≠e →
          T.splitIndex b s=T.splitIndex b e → T.splitIndex b s<T.splitIndex s e →
          W ≤ Rmacro/2 →
          4*W ≤ M.R (partitionPoint 0 as (T.splitIndex s e)) →
          M.z ≤ min (M.R (partitionPoint 0 as (T.splitIndex s e))/8) (Rmacro/4) →
          M.R (partitionPoint 0 as (T.splitIndex b s)) ≤
            min (M.R (partitionPoint 0 as (T.splitIndex s e))/8) (Rmacro/4) →
        T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun σ=>|nativeRestEndpointDifference n T b s e σ|^(2*(ell+1))) 0 ≤
          (2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs) W
            (partitionPoint 0 as (T.splitIndex s e)))^(2*(ell+1)) := by
  have H:=eventually_actual_minimum_bare_rest_all_high_resampling (D:=D) ell Bclock Temp
    Ccal Rmacro F hm hdelta hroom hgap hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  filter_upwards [H,eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro M hb hh hxs hcompare L us hus hret hmesh
  filter_upwards [hn M hb hh hxs hcompare L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro T b s e hse hlow hsplit hW hhigh hz hl
  exact native_original_full_rest_resampling_le n (ell+1) hn0 T
    (finiteCutMasses_ordered us hus k) _ b s e hse hlow hsplit
    (hk (T.splitIndex b s) (T.splitIndex s e) (T.splitIndex_le_clockLength _ _) hW hhigh hz hl)

theorem eventually_actual_minimum_original_rest_old_product_resampling
    (a : ℕ) (ha : 0 < a) (Bclock Temp Cmass Ccal Rmacro F : ℝ)
    (hTemp : 0 ≤ Temp) (hCm : 0 ≤ Cmass)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
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
          (f : Fin a → NativeSourceFactorForm) (initial : Finset (Fin a)),
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale M.xs W initial e) →
        ∀(b s e : T.Slot),s≠e →
          T.splitIndex b s=T.splitIndex b e → T.splitIndex b s<T.splitIndex s e →
          W ≤ Rmacro/2 →
          4*W ≤ M.R (partitionPoint 0 as (T.splitIndex s e)) →
          M.z ≤ min (M.R (partitionPoint 0 as (T.splitIndex s e))/8) (Rmacro/4) →
          M.R (partitionPoint 0 as (T.splitIndex b s)) ≤
            min (M.R (partitionPoint 0 as (T.splitIndex s e))/8) (Rmacro/4) →
        |T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun σ=>(G.canonicalMinimumSource M f).restProduct σ*
            nativeRestEndpointDifference n T b s e σ) 0| ≤
          (C^a*sourceMonomialScale M.xs W initial)*
            (2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs) W
              (partitionPoint 0 as (T.splitIndex s e))) := by
  obtain ⟨C,hC,HP⟩:=eventually_actual_minimum_bare_canonical_rest_even_moment (D:=D)
    a 1 ha (by norm_num) Bclock Temp Cmass hTemp hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  have HD:=eventually_actual_minimum_original_rest_endpoint_resampling (D:=D) 0
    Bclock Temp Ccal Rmacro F hm hdelta hroom hgap hcl hcu hAz hC0 hCt
    hCcal hmacro hRhalf hFmass hFradius
  refine ⟨C,hC,?_⟩
  filter_upwards [HP,HD] with n hp hd
  intro M hb hh hxs hcompare L us hus hret hmesh
  filter_upwards [hp M hb hh hxs L us hus hret hmesh,
    hd M hb hh hxs hcompare L us hus hret hmesh] with k hkP hkD
  dsimp only at hkP hkD ⊢
  intro T G f initial hmass b s e hse hlow hsplit hW hhigh hz hl
  have hxspos:=M.hxs
  have hWpos : 0 < max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs)):=
    M.hxs.trans_le (le_max_left _ _)
  have Hmom:=hkP T G f initial M.xs _ le_rfl (le_max_left _ _) hmass
  have Herr:=hkD T b s e hse hlow hsplit hW hhigh hz hl
  apply native_rest_old_product_endpoint_cauchy n T (finiteCutMasses_ordered us hus k)
    _ (G.canonicalMinimumSource M f).restProduct b s e
  · unfold sourceMonomialScale
    positivity
  · unfold savedExteriorScale
    positivity
  · simpa only [show 2*1=2 by norm_num] using Hmom
  · simpa only [show 2*(0+1)=2 by norm_num] using Herr

end OAI.SKFluctuations.Cavity
