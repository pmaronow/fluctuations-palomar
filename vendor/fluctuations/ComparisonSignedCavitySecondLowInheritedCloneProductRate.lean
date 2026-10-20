module

public import ComparisonSignedCavitySecondLowInheritedTwoLowCloneBudget
public import ComparisonSignedCavityActualBoundaryScalarRates

@[expose] public section

noncomputable section
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

private theorem clone_source_scale_nonneg {a : ℕ} {x W : ℝ}
    (hx : 0 ≤ x) (hW : 0 ≤ W) (initial : Finset (Fin a)) :
    0 ≤ sourceMonomialScale x W initial := by
  unfold sourceMonomialScale
  positivity

theorem saved_boundary_layer_flexible_scale_le {xs x W v p0 B : ℝ}
    (hxs : 0 < xs) (hW : 0 < W) (hv : 0 < v)
    (hxsx : xs ≤ x) (hxW : x ≤ W) (hp0 : 0 ≤ p0) (hB : 0 ≤ B) :
    v*(W*savedExteriorScale (B*xs) W v)*(p0*savedExteriorScale (B*xs) W v/x) ≤
      B^6*(p0*W*xs^2) := by
  rw [actual_saved_exterior_calibrated_first]
  have hsave:0 ≤ savedExteriorScale xs W v:=by unfold savedExteriorScale;positivity
  calc
    _=B^6*(v*(W*savedExteriorScale xs W v)*(p0*savedExteriorScale xs W v/x)):=by ring
    _ ≤ B^6*(v*(W*savedExteriorScale xs W v)*(p0*savedExteriorScale xs W v/xs)):=by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hB 6)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left (mul_nonneg hp0 hsave) hxs hxsx
    _ ≤ B^6*(p0*W*xs^2):=mul_le_mul_of_nonneg_left
      (saved_boundary_layer_scale_le hxs hW hv (hxsx.trans hxW) hp0) (pow_nonneg hB 6)

private theorem clone_rest_product_gram {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n) as) (ho : MassOrdered 0 as) (q : ℕ→RestCoordinate n→ℝ)
    (P F : T.Assignment→ℝ) {sp sf : ℝ} (hsp : 0 ≤ sp) (hsf : 0 ≤ sf)
    (hP:T.disorderExpect (restWeight n) (restFeature n) 0 q (fun σ=>P σ^2) 0 ≤ sp^2)
    (hF:T.disorderExpect (restWeight n) (restFeature n) 0 q (fun σ=>F σ^2) 0 ≤ sf^2) :
    |T.disorderExpect (restWeight n) (restFeature n) 0 q (fun σ=>P σ*F σ) 0| ≤ sp*sf := by
  have HH:=T.disorderExpect_mul_sq_le (restWeight_pos n) (restFeature n) ho 0 q P F 0
  have hFn:0 ≤ T.disorderExpect (restWeight n) (restFeature n) 0 q (fun σ=>F σ^2) 0:=by
    unfold ClockTree.disorderExpect
    exact Finset.sum_nonneg fun σ _=>mul_nonneg
      ((T.disorderWeight_probability (restWeight_pos n) (restFeature n) ho 0 q 0).1 σ) (sq_nonneg _)
  have HS: (T.disorderExpect (restWeight n) (restFeature n) 0 q (fun σ=>P σ*F σ) 0)^2 ≤ (sp*sf)^2:=by
    calc
      _ ≤ _:=HH
      _ ≤ sp^2*T.disorderExpect (restWeight n) (restFeature n) 0 q (fun σ=>F σ^2) 0:=
        mul_le_mul_of_nonneg_right hP hFn
      _ ≤ sp^2*sf^2:=mul_le_mul_of_nonneg_left hF (sq_nonneg _)
      _=_:=by ring
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hsp hsf)).mp (by simpa only [sq_abs] using HS)

theorem eventually_actual_minimum_inherited_second_low_clone_product_rate
    (a : ℕ) (Bclock Temp Cf Cmass Ccal Rmacro F : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (forms : Fin a→NativeSourceFactorForm) (initial : Finset (Fin a))
          (f c z : T.Slot) (cut : ℕ) (x v : ℝ),
          M.xs ≤ x → x ≤ W → 0 < v → W ≤ Rmacro/2 → cut ≤ as.length →
          T.splitIndex c f < cut → T.splitIndex c z < cut →
          (∀e,T.splitIndex c (G.i e) < cut) →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          partitionPoint 0 as (T.splitIndex f c) ≤ Cmass*W →
          partitionPoint 0 as (T.splitIndex z c) ≤ Cmass*W →
          4*W ≤ M.R (partitionPoint 0 as cut) →
          M.z  ≤  min (M.R (partitionPoint 0 as cut)/8) (Rmacro/4) →
          (∀e,cut ≤ T.splitIndex c (G.j e) →
            M.R (G.sourceLowMass e)  ≤  min (M.R (partitionPoint 0 as cut)/8) (Rmacro/4)) →
          M.R (partitionPoint 0 as (T.splitIndex f c))  ≤  min (M.R (partitionPoint 0 as cut)/8) (Rmacro/4) →
          M.R (partitionPoint 0 as (T.splitIndex z c))  ≤  min (M.R (partitionPoint 0 as cut)/8) (Rmacro/4) →
          v ≤ partitionPoint 0 as cut →
        let p:=nativeCloneBlockAtSlot T c cut
        let P0:=(G.canonicalMinimumSource M forms).restProduct
        let F0:=fun σ=>ActualNaturalBoundaryShape.canonicalLowRestFactor M f c σ*
          ActualNaturalBoundaryShape.canonicalLowRestFactor M z c σ
        |v*p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun σ=>(P0 (p.restOldRestrict σ)-P0 (p.restNewRestrict σ))*
            (F0 (p.restOldRestrict σ)-F0 (p.restNewRestrict σ))) 0| ≤
          C*((n:ℝ)^(-eta))^2*W*M.xs^2*sourceMonomialScale x W initial := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_rest_clone_budget
    (D:=D) a Bclock Temp Cf Cmass Ccal Rmacro F hTemp hCf hCm hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  obtain ⟨Cf2,hCf2,HF⟩:=eventually_actual_minimum_inherited_two_LOW_rest_clone_budget
    (D:=D) Bclock Temp Cf Cmass Ccal Rmacro F hTemp hCf hCm hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  let C:=1+8*(a:ℝ)*(1+Temp)^2*Cp^a*Cf2^2*(2*C0)^6
  have hC:0 < C:=by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [HP,HF] with n hp hf
  intro M HS hxs hcompare L us hus hret hmesh
  filter_upwards [hp M HS hxs hcompare L us hus hret hmesh,
    hf M HS hxs hcompare L us hus hret hmesh] with k hpk hfk
  dsimp only at hpk hfk ⊢
  intro T G forms initial f c z cut x v hxsx hxW hv hWmacro hcut Hcf Hcz Hout Hmass Hmf Hmz
    Hhigh Hz Hlow Hrf Hrz Hvmass
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
  let p:=nativeCloneBlockAtSlot T c cut
  let P0:=(G.canonicalMinimumSource M forms).restProduct
  let F0:=fun σ=>ActualNaturalBoundaryShape.canonicalLowRestFactor M f c σ*
    ActualNaturalBoundaryShape.canonicalLowRestFactor M z c σ
  let p0:=sourceMonomialScale x W initial
  let save:=(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs) W v
  let sp:=(a:ℝ)*(1+Temp)*(2*save)/x*(Cp^a*p0)
  let sf:=4*(1+Temp)*Cf2^2*W*save
  have hx:0 < x:=M.hxs.trans_le hxsx
  have hW:0 < W:=hx.trans_le hxW
  have hp0:0 ≤ p0:=clone_source_scale_nonneg hx.le hW.le initial
  have hsave:0 ≤ save:=mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (savedExteriorScale_pos (mul_pos (by positivity) M.hxs) hW hv).le
  have hsp:0 ≤ sp:=by dsimp [sp];positivity
  have hsf:0 ≤ sf:=by dsimp [sf];positivity
  have HP0:=hpk T G forms initial c cut x v hxsx hxW hv hWmacro hcut Hout Hmass Hhigh Hz Hlow Hvmass
  have HP1:p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 (fun j=>Sum.elim (fun _=>(M.bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
        (fun _=>(M.hf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)))
      (fun σ=>(P0 (p.restOldRestrict σ)-P0 (p.restNewRestrict σ))^2) 0 ≤ sp^2:=by
    convert HP0 using 1
    congr 1
    dsimp only [sp,save,p0,W]
    ring
  have HGram:=clone_rest_product_gram p.tree.cavityLeft (finiteCutMasses_ordered us hus k) _
    (fun σ=>P0 (p.restOldRestrict σ)-P0 (p.restNewRestrict σ))
    (fun σ=>F0 (p.restOldRestrict σ)-F0 (p.restNewRestrict σ)) hsp hsf
    HP1
    (hfk T f c z cut v hv hWmacro hcut Hcf Hcz Hmf Hmz Hhigh Hz Hrf Hrz Hvmass)
  rw [abs_mul,abs_of_pos hv]
  apply (mul_le_mul_of_nonneg_left HGram hv.le).trans
  have Hscale:=saved_boundary_layer_flexible_scale_le M.hxs hW hv hxsx hxW hp0
    (by positivity : 0 ≤ 2*C0)
  have Hcoef:0 ≤ 8*(a:ℝ)*(1+Temp)^2*Cp^a*Cf2^2*((n:ℝ)^(-eta))^2:=by positivity
  calc
    v*(sp*sf)= (8*(a:ℝ)*(1+Temp)^2*Cp^a*Cf2^2*((n:ℝ)^(-eta))^2)*
      (v*(W*savedExteriorScale ((2*C0)*M.xs) W v)*
        (p0*savedExteriorScale ((2*C0)*M.xs) W v/x)):=by dsimp [sp,sf,save];ring
    _ ≤ (8*(a:ℝ)*(1+Temp)^2*Cp^a*Cf2^2*((n:ℝ)^(-eta))^2)*
      ((2*C0)^6*(p0*W*M.xs^2)):=mul_le_mul_of_nonneg_left Hscale Hcoef
    _=(C-1)*(((n:ℝ)^(-eta))^2*W*M.xs^2*p0):=by dsimp [C];ring
    _ ≤ C*(((n:ℝ)^(-eta))^2*W*M.xs^2*p0):=mul_le_mul_of_nonneg_right
      (by linarith : C-1 ≤ C) (by positivity)
    _=C*((n:ℝ)^(-eta))^2*W*M.xs^2*p0:=by ring

end OAI.SKFluctuations.Cavity
