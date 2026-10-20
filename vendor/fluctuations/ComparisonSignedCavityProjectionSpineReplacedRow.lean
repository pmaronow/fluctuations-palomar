module

public import ComparisonSignedCavityProjectionSpineOldRow

@[expose] public section

noncomputable section
set_option maxHeartbeats 30000000
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S B : Type} [Fintype ι] [Fintype S] [Nonempty S] [Fintype B] [Nonempty B]
variable {as : List PositiveMass}

theorem NativeProjectionSpine.replaced_signed_row
    {A T : ClockTree (S×B) as} {base : NativeGeneratedTest A} {P : NativeGeneratedTest T}
    {star : ℕ} (h : NativeProjectionSpine base star P)
    (hA : NativeTargetStarSingleton A base.target star)
    (hT : NativeTargetStarSingleton T P.target star)
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (aRow : ℝ) (ho : MassOrdered aRow as)
    (R : S→S→ℝ) (C : ℕ→ℝ) (q : ℕ→ι→ℝ≥0)
    (J : (ι→ℝ)→A.cavityLeft.Assignment→S→ℝ) (x : ι→ℝ) (H : ℕ→Bool→ℝ) :
    ((nativeHighMarkedRows T P.target star aRow).map fun p=>p.coeff*
      H (p.tree.splitIndex (p.embed P.target) p.mark) (decide (p.mark=p.embed P.target))*
      nativeStarFieldTestMean w φ p.tree.cavityLeft (p.tree.cavityLeftSlot (p.embed P.target)) star q
        (fun y σ=>J y (h.restRead (p.restRestrict σ)) (p.restSpin σ)*
          nativeRestGeneratedTestValue T P R C
            (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.target) (p.restRestrict σ) (p.restSpin σ))) x).sum=
    ((nativeHighMarkedRows A base.target star aRow).map fun r=>r.coeff*
      H (r.tree.splitIndex (r.embed base.target) r.mark) (decide (r.mark=r.embed base.target))*
      nativeStarFieldTestMean w φ r.tree.cavityLeft (r.tree.cavityLeftSlot (r.embed base.target)) star q
        (fun y σ=>J y (r.restRestrict σ) (r.restSpin σ)*
          nativeRestGeneratedTestValue A base R C
            (nativeReplaceAtSlot A.cavityLeft (A.cavityLeftSlot base.target) (r.restRestrict σ) (r.restSpin σ))*
          (nativeStarPairFactor w φ as star q (fun u v=>R u v-C star) y
            (r.restSpin σ))^h.toothCount) x).sum := by
  let F:=fun u v=>R u v-C star
  let Jswap:=fun (y:ι→ℝ) (σ:A.cavityLeft.Assignment) (u:S)=>
    J y (nativeReplaceAtSlot A.cavityLeft (A.cavityLeftSlot base.target) σ u)
      (A.cavityLeft.atSlot σ (A.cavityLeftSlot base.target))
  have Hsource : ((nativeHighMarkedRows T P.target star aRow).map fun p=>p.coeff*
      H (p.tree.splitIndex (p.embed P.target) p.mark) (decide (p.mark=p.embed P.target))*
      nativeStarFieldTestMean w φ p.tree.cavityLeft (p.tree.cavityLeftSlot (p.embed P.target)) star q
        (fun y σ=>J y (h.restRead (p.restRestrict σ)) (p.restSpin σ)*
          nativeRestGeneratedTestValue T P R C
            (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.target) (p.restRestrict σ) (p.restSpin σ))) x).sum=
    ((nativeHighMarkedRows T P.target star aRow).map fun p=>p.coeff*
      H (p.tree.splitIndex (p.embed P.target) p.mark) (decide (p.mark=p.embed P.target))*
      nativeStarFieldTestMean w φ p.tree.cavityLeft (p.tree.cavityLeftSlot (p.embed P.target)) star q
        (fun y σ=>Jswap y (h.restRead (p.restRestrict σ)) (p.restSpin σ)*
          nativeRestGeneratedTestValue T P R C (p.restRestrict σ)) x).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    obtain ⟨hp,hh⟩:=(mem_nativeHighMarkedRows T P.target star aRow p).mp hp
    congr 1
    have HX:=native_target_singleton_full_rest_star_field_exchange T P.target star hT hw φ ho
      p hp hh q (fun y σ u=>J y (h.restRead σ) u*nativeRestGeneratedTestValue T P R C
        (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.target) σ u)) x
    rw [HX]
    apply congrArg (fun L=>nativeStarFieldTestMean w φ p.tree.cavityLeft
      (p.tree.cavityLeftSlot (p.embed P.target)) star q L x)
    funext y σ
    rw [nativeReplaceAtSlot_restore,h.restRead_replace_target]
    dsimp only [Jswap]
    rw [h.restTargetRead]
  rw [Hsource,h.old_signed_row hw φ ho aRow R C q Jswap x H]
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  obtain ⟨hr,hhA⟩:=(mem_nativeHighMarkedRows A base.target star aRow r).mp hr
  congr 1
  have HR:=native_target_singleton_full_rest_star_field_exchange A base.target star hA hw φ ho
    r hr hhA q (fun y σ u=>Jswap y σ u*nativeRestGeneratedTestValue A base R C σ*
      (nativeStarPairFactor w φ as star q F y
        (A.cavityLeft.atSlot σ (A.cavityLeftSlot base.target)))^h.toothCount) x
  convert HR using 1
  apply congrArg (fun L=>nativeStarFieldTestMean w φ r.tree.cavityLeft
    (r.tree.cavityLeftSlot (r.embed base.target)) star q L x)
  funext y σ
  dsimp only [Jswap,F]
  rw [nativeReplaceAtSlot_restore,nativeReplaceAtSlot_self]

end OAI.SKFluctuations.Hierarchy.ClockTree
