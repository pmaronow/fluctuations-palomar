module

public import ComparisonSignedCavityProjectionSpineDisorderRow
public import ComparisonSignedCavityStarFieldMeanLinearity

@[expose] public section

noncomputable section
set_option maxHeartbeats 30000000
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S B : Type} [Fintype ι] [Fintype S] [Nonempty S] [Fintype B] [Nonempty B]
variable {as : List PositiveMass}

omit [Fintype B] [Nonempty B] in
theorem native_signed_disorder_row_sub
    (T : ClockTree (S×B) as) (s : T.Slot) (star : ℕ)
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (v : ι→ℝ) (q : ℕ→ι→ℝ)
    (L : List (MarkedPlacement T)) (c : MarkedPlacement T→ℝ)
    (J K : (p : MarkedPlacement T)→(ι→ℝ)→p.tree.cavityLeft.Assignment→ℝ)
    (hJ : ∀p σ,BddSmooth 0 (fun y=>J p y σ))
    (hK : ∀p σ,BddSmooth 0 (fun y=>K p y σ)) (x : ι→ℝ) :
    (L.map fun p=>c p*nativeStarFieldDisorderMean w φ p.tree.cavityLeft
      (p.tree.cavityLeftSlot (p.embed s)) star v q (fun y σ=>J p y σ-K p y σ) x).sum=
    (L.map fun p=>c p*nativeStarFieldDisorderMean w φ p.tree.cavityLeft
      (p.tree.cavityLeftSlot (p.embed s)) star v q (J p) x).sum-
    (L.map fun p=>c p*nativeStarFieldDisorderMean w φ p.tree.cavityLeft
      (p.tree.cavityLeftSlot (p.embed s)) star v q (K p) x).sum := by
  simp_rw [native_star_field_disorder_mean_sub _ _ _ hw φ ho v q _ _ (hJ _) (hK _),mul_sub]
  induction L with
  | nil=>simp
  | cons p L ih=>simp only [List.map_cons,List.sum_cons]; rw [ih]; ring

theorem NativeProjectionSpine.paired_signed_disorder_row
    {A T : ClockTree (S×B) as} {base : NativeGeneratedTest A} {P : NativeGeneratedTest T}
    {star : ℕ} (h : NativeProjectionSpine base star P)
    (hA : NativeTargetStarSingleton A base.target star)
    (hT : NativeTargetStarSingleton T P.target star)
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (aRow : ℝ) (ho : MassOrdered aRow as)
    (R : S→S→ℝ) (C : ℕ→ℝ) (v : ι→ℝ) (q : ℕ→ι→ℝ)
    (J : (ι→ℝ)→A.cavityLeft.Assignment→S→ℝ) (hJ : ∀σ u,BddSmooth 0 (fun y=>J y σ u)) (x : ι→ℝ) (H : ℕ→Bool→ℝ) :
    ((nativeHighMarkedRows T P.target star aRow).map fun p=>p.coeff*
      H (p.tree.splitIndex (p.embed P.target) p.mark) (decide (p.mark=p.embed P.target))*
      nativeStarFieldDisorderMean w φ p.tree.cavityLeft (p.tree.cavityLeftSlot (p.embed P.target)) star v q
        (fun y σ=>J y (h.restRead (p.restRestrict σ)) (p.restSpin σ)*
          (nativeRestGeneratedTestValue T P R C
            (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.target) (p.restRestrict σ) (p.restSpin σ))-
          nativeRestGeneratedTestValue T P R C (p.restRestrict σ))) x).sum=
    ((nativeHighMarkedRows A base.target star aRow).map fun r=>r.coeff*
      H (r.tree.splitIndex (r.embed base.target) r.mark) (decide (r.mark=r.embed base.target))*
      nativeStarFieldDisorderMean w φ r.tree.cavityLeft (r.tree.cavityLeftSlot (r.embed base.target)) star v q
        (fun y σ=>J y (r.restRestrict σ) (r.restSpin σ)*
          (nativeRestGeneratedTestValue A base R C
              (nativeReplaceAtSlot A.cavityLeft (A.cavityLeftSlot base.target) (r.restRestrict σ) (r.restSpin σ))*
            (nativeStarPairFactor w φ as star (cumulativeIncrements (q 0) (fun j=>q (j+1)))
              (fun u v=>R u v-C star) y (r.restSpin σ))^h.toothCount-
            nativeRestGeneratedTestValue A base R C (r.restRestrict σ)*
            (nativeStarPairFactor w φ as star (cumulativeIncrements (q 0) (fun j=>q (j+1)))
              (fun u v=>R u v-C star) y
              (A.cavityLeft.atSlot (r.restRestrict σ) (A.cavityLeftSlot base.target)))^h.toothCount)) x).sum := by
  have hOld:=h.old_signed_disorder_row hw φ ho aRow R C v q J hJ x H
  have hNew:=h.replaced_signed_disorder_row hA hT hw φ aRow ho R C v q J hJ x H
  have Hdiff:=congrArg₂ (fun a b : ℝ=>a-b) hNew hOld
  simp only [mul_sub] at Hdiff ⊢
  rw [native_signed_disorder_row_sub T P.target star hw φ ho v q _ _
    (fun p y σ=>J y (h.restRead (p.restRestrict σ)) (p.restSpin σ)*
      nativeRestGeneratedTestValue T P R C
        (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.target) (p.restRestrict σ) (p.restSpin σ)))
    (fun p y σ=>J y (h.restRead (p.restRestrict σ)) (p.restSpin σ)*
      nativeRestGeneratedTestValue T P R C (p.restRestrict σ))
    (fun p σ=>(hJ _ _).mul_const _) (fun p σ=>(hJ _ _).mul_const _)]
  rw [native_signed_disorder_row_sub A base.target star hw φ ho v q _ _
    (fun r y σ=>J y (r.restRestrict σ) (r.restSpin σ)*
      (nativeRestGeneratedTestValue A base R C
        (nativeReplaceAtSlot A.cavityLeft (A.cavityLeftSlot base.target) (r.restRestrict σ) (r.restSpin σ))*
      (nativeStarPairFactor w φ as star (cumulativeIncrements (q 0) (fun j=>q (j+1)))
        (fun u v=>R u v-C star) y (r.restSpin σ))^h.toothCount))
    (fun r y σ=>J y (r.restRestrict σ) (r.restSpin σ)*
      (nativeRestGeneratedTestValue A base R C (r.restRestrict σ)*
      (nativeStarPairFactor w φ as star (cumulativeIncrements (q 0) (fun j=>q (j+1)))
        (fun u v=>R u v-C star) y
        (A.cavityLeft.atSlot (r.restRestrict σ) (A.cavityLeftSlot base.target)))^h.toothCount))
    (fun r σ=>(hJ _ _).mul ((native_star_pair_factor_smooth as star hw φ ho _ _ _ 0).pow h.toothCount |>.const_mul _))
    (fun r σ=>(hJ _ _).mul ((native_star_pair_factor_smooth as star hw φ ho _ _ _ 0).pow h.toothCount |>.const_mul _))]
  simpa only [mul_assoc] using Hdiff

end OAI.SKFluctuations.Hierarchy.ClockTree
