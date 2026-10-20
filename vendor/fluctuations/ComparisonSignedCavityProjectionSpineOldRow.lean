module

public import ComparisonSignedCavityObservedProjectionSpine
public import ComparisonSignedCavityHighFreshRowInterchange

@[expose] public section

noncomputable section
set_option maxHeartbeats 30000000
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S B : Type} [Fintype ι] [Fintype S] [Nonempty S] [Fintype B] [Nonempty B]
variable {as : List PositiveMass}

omit [Nonempty S] [Fintype B] in
theorem NativeProjectionSpine.old_signed_row
    {A T : ClockTree (S×B) as} {base : NativeGeneratedTest A} {P : NativeGeneratedTest T}
    {star : ℕ} (h : NativeProjectionSpine base star P)
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a₀ : ℝ} (ho : MassOrdered a₀ as) (aRow : ℝ)
    (R : S→S→ℝ) (C : ℕ→ℝ) (q : ℕ→ι→ℝ≥0)
    (J : (ι→ℝ)→A.cavityLeft.Assignment→S→ℝ) (x : ι→ℝ) (H : ℕ→Bool→ℝ) :
    ((nativeHighMarkedRows T P.target star aRow).map fun p=>p.coeff*
      H (p.tree.splitIndex (p.embed P.target) p.mark) (decide (p.mark=p.embed P.target))*
      nativeStarFieldTestMean w φ p.tree.cavityLeft (p.tree.cavityLeftSlot (p.embed P.target)) star q
        (fun y σ=>J y (h.restRead (p.restRestrict σ)) (p.restSpin σ)*
          nativeRestGeneratedTestValue T P R C (p.restRestrict σ)) x).sum=
    ((nativeHighMarkedRows A base.target star aRow).map fun r=>r.coeff*
      H (r.tree.splitIndex (r.embed base.target) r.mark) (decide (r.mark=r.embed base.target))*
      nativeStarFieldTestMean w φ r.tree.cavityLeft (r.tree.cavityLeftSlot (r.embed base.target)) star q
        (fun y σ=>J y (r.restRestrict σ) (r.restSpin σ)*
          nativeRestGeneratedTestValue A base R C (r.restRestrict σ)*
          (nativeStarPairFactor w φ as star q (fun u v=>R u v-C star) y
            (A.cavityLeft.atSlot (r.restRestrict σ) (A.cavityLeftSlot base.target)))^h.toothCount) x).sum := by
  induction h generalizing J with
  | base=>simp only [NativeProjectionSpine.restRead,NativeProjectionSpine.toothCount,id_eq,pow_zero,mul_one]
  | @projection T P h a hl ih=>
    let F:=fun u v=>R u v-C star
    let Q:=fun (y:ι→ℝ) (σ:T.cavityLeft.Assignment) (u v:S)=>
      J y (h.restRead σ) u*nativeRestGeneratedTestValue T P R C σ*
        F (T.cavityLeft.atSlot σ (T.cavityLeftSlot P.target)) v
    have HX:=native_high_fresh_signed_row_sum T P.target star hl a aRow hw φ ho q Q x
      (fun cuts diag=>H (cuts P.target) (diag P.target))
    have Hleft : ((nativeHighMarkedRows (nativeFreshAtSlot T a P.target star).tree
        (P.addProjection a star).target star aRow).map fun p=>p.coeff*
      H (p.tree.splitIndex (p.embed (P.addProjection a star).target) p.mark)
        (decide (p.mark=p.embed (P.addProjection a star).target))*
      nativeStarFieldTestMean w φ p.tree.cavityLeft (p.tree.cavityLeftSlot (p.embed (P.addProjection a star).target)) star q
        (fun y σ=>J y ((NativeProjectionSpine.projection h a hl).restRead (p.restRestrict σ))
          (p.restSpin σ)*nativeRestGeneratedTestValue _ (P.addProjection a star) R C (p.restRestrict σ)) x).sum=
      ((nativeHighMarkedRows (nativeFreshAtSlot T a P.target star).tree
        ((nativeFreshAtSlot T a P.target star).embed P.target) star aRow).map fun p=>p.coeff*
      H (p.tree.splitIndex (p.embed ((nativeFreshAtSlot T a P.target star).embed P.target)) p.mark)
        (decide (p.mark=p.embed ((nativeFreshAtSlot T a P.target star).embed P.target)))*
      nativeStarFieldTestMean w φ p.tree.cavityLeft (p.tree.cavityLeftSlot (p.embed ((nativeFreshAtSlot T a P.target star).embed P.target))) star q
        (fun y σ=>Q y ((nativeFreshAtSlot T a P.target star).restRestrict (p.restRestrict σ))
          (p.restSpin σ) ((nativeFreshAtSlot T a P.target star).restSpin (p.restRestrict σ))) x).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro p _
      congr 1
      apply congrArg (fun L=>nativeStarFieldTestMean w φ p.tree.cavityLeft
        (p.tree.cavityLeftSlot (p.embed ((nativeFreshAtSlot T a P.target star).embed P.target))) star q L x)
      funext y σ
      dsimp only [NativeProjectionSpine.restRead]
      rw [native_rest_add_projection_value P a hl R C]
      dsimp only [Q,F]
      ring
    rw [Hleft,HX]
    have Hmiddle : ((nativeHighMarkedRows T P.target star aRow).map fun r=>r.coeff*
      H (r.tree.splitIndex (r.embed P.target) r.mark) (decide (r.mark=r.embed P.target))*
      (let g:=nativeFreshAtSlot r.tree a (r.embed P.target) star
      nativeStarFieldTestMean w φ g.tree.cavityLeft (g.tree.cavityLeftSlot.toFun (g.embed (r.embed P.target))) star q
        (fun y σ=>Q y (r.restRestrict (g.restRestrict σ)) (r.restSpin (g.restRestrict σ)) (g.restSpin σ)) x)).sum=
      ((nativeHighMarkedRows T P.target star aRow).map fun r=>r.coeff*
      H (r.tree.splitIndex (r.embed P.target) r.mark) (decide (r.mark=r.embed P.target))*
      nativeStarFieldTestMean w φ r.tree.cavityLeft (r.tree.cavityLeftSlot (r.embed P.target)) star q
        (fun y σ=>(J y (h.restRead (r.restRestrict σ)) (r.restSpin σ)*
          nativeStarPairFactor w φ as star q F y
            (A.cavityLeft.atSlot (h.restRead (r.restRestrict σ)) (A.cavityLeftSlot base.target)))*
          nativeRestGeneratedTestValue T P R C (r.restRestrict σ)) x).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro r _
      congr 1
      have Hfresh:=native_star_field_fresh_selector_factor r.tree (r.embed P.target) star hl a
        hw φ ho q
        (fun y σ=>J y (h.restRead (r.restRestrict σ)) (r.restSpin σ)*
          nativeRestGeneratedTestValue T P R C (r.restRestrict σ))
        (fun _ σ=>T.cavityLeft.atSlot (r.restRestrict σ) (T.cavityLeftSlot P.target)) F x
      dsimp only at Hfresh
      dsimp only [Q]
      convert Hfresh.trans ?_ using 1
      apply congrArg (fun L=>nativeStarFieldTestMean w φ r.tree.cavityLeft
        (r.tree.cavityLeftSlot (r.embed P.target)) star q L x)
      funext y σ
      rw [h.restTargetRead]
      ring
    rw [Hmiddle,ih (fun y σ u=>J y σ u*nativeStarPairFactor w φ as star q F y
      (A.cavityLeft.atSlot σ (A.cavityLeftSlot base.target)))]
    apply congrArg List.sum
    apply List.map_congr_left
    intro r _
    congr 1
    apply congrArg (fun L=>nativeStarFieldTestMean w φ r.tree.cavityLeft
      (r.tree.cavityLeftSlot (r.embed base.target)) star q L x)
    funext y σ
    dsimp only [NativeProjectionSpine.toothCount,F]
    rw [pow_succ]
    ring

end OAI.SKFluctuations.Hierarchy.ClockTree
