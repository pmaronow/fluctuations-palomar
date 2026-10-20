module

public import ComparisonSignedCavityActualOmittedSiteProduct
public import ComparisonSignedCavityActualLowErrorSaving

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem eventually_actual_minimum_bare_product_omitted_site_square
    (a : ℕ) (ha : 0 < a) (Bclock Temp Cmass : ℝ) (hTemp : 0 ≤ Temp) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠ jGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
        ∀(G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm)
          (initial : Finset (Fin a)) (x W : ℝ),M.xs ≤ x → x ≤ W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          T.disorderExpect (fullWeight n) (fullFeature n) 0
            (finitePhysicalCavitySquareVariance n U as b h l t)
            (fun σ=>((G.canonicalMinimumSource M f).product σ-
              (G.canonicalMinimumSource M f).restoredProduct σ)^2) 0 ≤
              (((a:ℝ)*(1+Temp)/((n+1:ℕ)*x))*(C^a*sourceMonomialScale x W initial))^2 := by
  obtain ⟨Cf,hCf,HF⟩:=eventually_actual_minimum_bare_canonical_square_even_moment
    (D:=D) 1 a (by norm_num) ha Bclock Temp Cmass hTemp hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=2*(Cf+(1+Temp)+1)
  have hC : 0 < C:=by dsimp [C];positivity
  have Hsite:=NativeOverlapMinimum.eventually_omitted_site_below_saved_scale
    (m:=m) (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) (saving:=0) hC0 (show (0:ℝ) < 5/6+m by linarith)
  refine ⟨C,hC,?_⟩
  filter_upwards [HF,Hsite] with n hn hsite
  intro M hbareb hbareh hxs1 L us hus hret hmesh
  filter_upwards [hn M hbareb hbareh hxs1 L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T l t hl ht G f initial x W hxsx hxW hmass
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let GC:=G.canonicalMinimumSource M f
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hx : 0 < x:=M.hxs.trans_le hxsx
  have Hbeta (e : Fin a) : |GC.β e| ≤ 1+Temp := by
    have H:=M.bare_source_clock_bounds hcl hAz Temp hbareb hbareh
      (partitionPoint_mem as ho (T.splitIndex (G.i e) (G.j e)))
    exact native_source_slope_bound (f e) H.1 H.2.1
  have Hfactor (e : Fin a) : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as b h l t)
      (fun σ=>|GC.deletedFactor e σ|^(2*a)) 0 ≤
        (Cf*sourceFactorScale x W initial e)^(2*a) := by
    let r:=sourceFactorScale x W initial e
    have hr : M.xs ≤ r:=hxsx.trans (source_factor_scale_ge_initial hxW initial e)
    have H:=hgrid U T l t hl ht (G.edgeShape e) (fun _=>f e) ∅ r r hr le_rfl (by
      intro j
      simpa only [ActualNaturalBoundaryShape.sourceLowMass,ActualNaturalBoundaryShape.edgeShape,
        sourceFactorScale,Finset.notMem_empty,↓reduceIte,r] using hmass e)
    simpa [GC,ActualNaturalBoundaryShape.deletedFactor,ActualNaturalBoundaryShape.product,
      ActualNaturalBoundaryShape.canonicalMinimumSource,ActualNaturalBoundaryShape.edgeShape,
      ActualNaturalBoundaryShape.sourceLowMass,fullBoundaryAffineProduct,sourceMonomialScale,r,as,b,h,
      show 1* a=a by omega] using H
  have HS : 1/(n+1:ℕ) ≤ x := by
    have H:=hsite M x hxsx
    simpa only [neg_zero,Real.rpow_zero,one_mul] using H
  have H:=native_omitted_site_product_square n a ha T ho 0
    (finitePhysicalCavitySquareVariance n U as b h l t) 0 GC
    (sourceFactorScale x W initial) x Cf (1+Temp) hx hCf (by positivity)
    (fun e=>source_factor_scale_ge_initial hxW initial e) HS Hbeta Hfactor
  rw [source_factor_scale_product] at H
  simpa only [GC,C,div_eq_mul_inv,mul_assoc] using H

theorem actual_omitted_product_cubic_ratio_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (hC0 : 0 < C0)
    (W : ℝ) (hxW : M.xs ≤ W) :
    (1/(n+1:ℕ):ℝ)/(M.xs^3*W) ≤ C0^4*M.context.N^(-((1:ℝ)/3+4*m)) := by
  have H:=M.canonical_high_mass_inverse_power hC0 4
  simp only [Nat.cast_ofNat,show (4:ℝ)/6=(2:ℝ)/3 by norm_num] at H
  have HM:=mul_le_mul_of_nonneg_left H (Real.rpow_nonneg M.context.hN.le (-((1:ℝ)/3)))
  have Hpow : M.context.N^(-((1:ℝ)/3))=M.context.N^((2:ℝ)/3)/M.context.N := by
    calc
      _=M.context.N^(((2:ℝ)/3)-1):=by congr 1;ring
      _=M.context.N^((2:ℝ)/3)/M.context.N^((1:ℝ)):=Real.rpow_sub M.context.hN _ _
      _=_:=by rw [Real.rpow_one]
  have HE : M.context.N^(-((1:ℝ)/3))*(1/(M.context.N^((2:ℝ)/3)*M.xs^4))=
      (1/(n+1:ℕ):ℝ)/M.xs^4 := by
    rw [Hpow]
    have hP:=(Real.rpow_pos_of_pos M.context.hN ((2:ℝ)/3)).ne'
    have hx:=M.hxs.ne'
    have hN:=M.context.hN.ne'
    change _=(1/M.context.N)/M.xs^4
    field_simp
  have HR : M.context.N^(-((1:ℝ)/3))*(C0^4*M.context.N^(-(4:ℝ)*m))=
      C0^4*M.context.N^(-((1:ℝ)/3+4*m)) := by
    rw [mul_left_comm,←Real.rpow_add M.context.hN]
    congr 2
    ring
  rw [HE,HR] at HM
  have hW : 0 < W:=M.hxs.trans_le hxW
  have hx:=M.hxs
  have HX : M.xs^4 ≤ M.xs^3*W := by
    calc
      _=M.xs^3*M.xs:=by ring
      _≤_:=mul_le_mul_of_nonneg_left hxW (pow_nonneg M.hxs.le 3)
  exact (div_le_div_of_nonneg_left (by positivity) (by positivity) HX).trans HM

theorem eventually_actual_omitted_product_cubic_cost_saved
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ n : ℕ in atTop,
      ∀ M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀ W : ℝ,M.xs ≤ W →
        A/((n+1:ℕ)*M.xs) ≤ ((n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(W*M.xs^2) := by
  have H:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=A*C0^4) (d:=1)
      (q:=-((1:ℝ)/3+4*m)) (r:=-(1:ℝ)/6) zero_lt_one (by linarith))
  filter_upwards [H] with n hn
  intro M W hxW
  have hx:=M.hxs
  have hW:=hx.trans_le hxW
  have HR:=mul_le_mul_of_nonneg_left (actual_omitted_product_cubic_ratio_le M hC0 W hxW) hA
  have HN : A*((1/(n+1:ℕ):ℝ)/(M.xs^3*W)) ≤ ((n+1:ℕ):ℝ)^(-(1:ℝ)/6) := by
    apply HR.trans
    simpa only [NativeOverlapContext.N,mul_assoc,one_mul] using hn
  have HE : A/((n+1:ℕ)*M.xs)/(W*M.xs^2)=A*((1/(n+1:ℕ):ℝ)/(M.xs^3*W)) := by
    field_simp
  rw [←HE] at HN
  exact (div_le_iff₀ (show 0 < W*M.xs^2 by positivity)).mp HN

theorem eventually_actual_minimum_bare_product_omitted_site_saved_cubic
    (a : ℕ) (ha : 0 < a) (Bclock Temp Cmass : ℝ) (hTemp : 0 ≤ Temp) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠ jGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
        ∀(G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm)
          (initial : Finset (Fin a)) (W : ℝ),M.xs ≤ W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale M.xs W initial e) →
          T.disorderExpect (fullWeight n) (fullFeature n) 0
            (finitePhysicalCavitySquareVariance n U as b h l t)
            (fun σ=>((G.canonicalMinimumSource M f).product σ-
              (G.canonicalMinimumSource M f).restoredProduct σ)^2) 0 ≤
              (((n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(W*M.xs^2)*
                (C^a*sourceMonomialScale M.xs W initial))^2 := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_bare_product_omitted_site_square
    (D:=D) a ha Bclock Temp Cmass hTemp hCmass hm hdelta hroom hcl hcu hAz hC0 hCt
  have HA:=eventually_actual_omitted_product_cubic_cost_saved
    (m:=m) (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock)
    hm hC0 ((a:ℝ)*(1+Temp)) (by positivity)
  refine ⟨C,hC,?_⟩
  filter_upwards [H,HA] with n hn hcost
  intro M hbareb hbareh hxs1 L us hus hret hmesh
  filter_upwards [hn M hbareb hbareh hxs1 L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T l t hl ht G f initial W hxW hmass
  apply (hgrid U T l t hl ht G f initial M.xs W le_rfl hxW hmass).trans
  have hx:=M.hxs
  have hW:=hx.trans_le hxW
  have HS : 0 ≤ C^a*sourceMonomialScale M.xs W initial := by
    rw [←source_factor_scale_product]
    exact mul_nonneg (pow_nonneg hC.le _) (Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos hx hW initial e).le)
  exact pow_le_pow_left₀ (by positivity)
    (mul_le_mul_of_nonneg_right (hcost M W hxW) HS) 2

end OAI.SKFluctuations.Cavity
