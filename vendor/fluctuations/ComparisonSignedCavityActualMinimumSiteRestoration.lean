module

public import ComparisonSignedCavityActualMinimumOmittedSiteProduct

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem eventually_actual_minimum_bare_site_pair_restoration_saved_cubic
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
        ∀(U : ℕ) (K : ℕ→ℝ) (T : ClockTree (Spin n×Bool) as),
        ∀(G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm)
          (initial : Finset (Fin a)) (W : ℝ),M.xs ≤ W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale M.xs W initial e) →
        ∀s t : T.Slot,
          let q:=cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K
          |T.disorderExpect (fullWeight n) (fullFeature n) 0 q
              (fun σ=>spinValue (T.atSlot σ s).2*spinValue (T.atSlot σ t).2*
                (G.canonicalMinimumSource M f).product σ) 0-
            T.disorderExpect (fullWeight n) (fullFeature n) 0 q
              (fun σ=>orderedOverlap (n+1) (joinSpin (T.atSlot σ s)) (joinSpin (T.atSlot σ t))*
                (G.canonicalMinimumSource M f).product σ) 0| ≤
            2*(((n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(W*M.xs^2)*(C^a*sourceMonomialScale M.xs W initial)) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_bare_product_omitted_site_saved_cubic
    (D:=D) a ha Bclock Temp Cmass hTemp hCmass hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hbareb hbareh hxs1 L us hus hret hmesh
  filter_upwards [hn M hbareb hbareh hxs1 L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U K T G f initial W hxW hmass s t
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let GC:=G.canonicalMinimumSource M f
  let B:=((n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(W*M.xs^2)*(C^a*sourceMonomialScale M.xs W initial)
  have hx:=M.hxs
  have hW:=hx.trans_le hxW
  have hB : 0 ≤ B := by
    dsimp only [B]
    rw [←source_factor_scale_product]
    exact mul_nonneg (by positivity) (mul_nonneg (pow_nonneg hC.le _) (Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos hx hW initial e).le))
  have HP:=hgrid U T 1 1 (by norm_num) (by norm_num) G f initial W hxW hmass
  change T.disorderExpect (fullWeight n) (fullFeature n) 0
    (cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h
      (finitePhysicalMixedClock (n+1) as b h))
    (fun σ=>(GC.product σ-GC.restoredProduct σ)^2) 0 ≤ B^2 at HP
  rw [native_full_endpoint_scalar_clock_independent n U _ b h _ K] at HP
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HE:=native_original_deleted_site_pair_eq_overlap_add_omission n a U T ho b h K GC s t
  dsimp only at HE
  rw [HE]
  simpa only [b,h,as,GC,B,add_sub_cancel_left,add_sub_cancel_right] using
    native_original_omitted_site_row_abs_le n a U T ho b h K GC s t B hB HP

end OAI.SKFluctuations.Cavity
