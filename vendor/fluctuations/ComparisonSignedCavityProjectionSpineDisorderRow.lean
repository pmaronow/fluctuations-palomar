module

public import ComparisonSignedCavityProjectionSpineReplacedRow
public import ComparisonSignedCavityStarFieldMeanRegularity

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
theorem native_star_field_disorder_list_mean
    (T : ClockTree (S×B) as) (s : T.Slot) (star : ℕ)
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (v : ι→ℝ) (q : ℕ→ι→ℝ)
    (L : List (MarkedPlacement T)) (c : MarkedPlacement T→ℝ)
    (J : (p : MarkedPlacement T)→(ι→ℝ)→p.tree.cavityLeft.Assignment→ℝ)
    (hJ : ∀p σ,BddSmooth 0 (fun y=>J p y σ)) (x : ι→ℝ) :
    (L.map fun p=>c p*nativeStarFieldDisorderMean w φ p.tree.cavityLeft
      (p.tree.cavityLeftSlot (p.embed s)) star v q (J p) x).sum=
    ∫y,(L.map fun p=>c p*nativeStarFieldTestMean w φ p.tree.cavityLeft
      (p.tree.cavityLeftSlot (p.embed s)) star
      (cumulativeIncrements (q 0) (fun j=>q (j+1))) (J p) (x+y)).sum
      ∂Measure.pi (fun i=>gaussianReal 0 (Real.toNNReal (q 0 i-v i))) := by
  rw [native_integral_list_sum]
  · simp only [nativeStarFieldDisorderMean,integral_const_mul]
  · intro p _
    exact (native_star_field_test_mean_integrable p.tree.cavityLeft
      (p.tree.cavityLeftSlot (p.embed s)) star hw φ ho _ (J p) (hJ p) _ x).const_mul (c p)

omit [Fintype B] in
theorem NativeProjectionSpine.old_signed_disorder_row
    {A T : ClockTree (S×B) as} {base : NativeGeneratedTest A} {P : NativeGeneratedTest T}
    {star : ℕ} (h : NativeProjectionSpine base star P)
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a₀ : ℝ} (ho : MassOrdered a₀ as) (aRow : ℝ)
    (R : S→S→ℝ) (C : ℕ→ℝ) (v : ι→ℝ) (q : ℕ→ι→ℝ)
    (J : (ι→ℝ)→A.cavityLeft.Assignment→S→ℝ) (hJ : ∀σ u,BddSmooth 0 (fun y=>J y σ u)) (x : ι→ℝ) (H : ℕ→Bool→ℝ) :
    ((nativeHighMarkedRows T P.target star aRow).map fun p=>p.coeff*
      H (p.tree.splitIndex (p.embed P.target) p.mark) (decide (p.mark=p.embed P.target))*
      nativeStarFieldDisorderMean w φ p.tree.cavityLeft (p.tree.cavityLeftSlot (p.embed P.target)) star v q
        (fun y σ=>J y (h.restRead (p.restRestrict σ)) (p.restSpin σ)*
          nativeRestGeneratedTestValue T P R C (p.restRestrict σ)) x).sum=
    ((nativeHighMarkedRows A base.target star aRow).map fun r=>r.coeff*
      H (r.tree.splitIndex (r.embed base.target) r.mark) (decide (r.mark=r.embed base.target))*
      nativeStarFieldDisorderMean w φ r.tree.cavityLeft (r.tree.cavityLeftSlot (r.embed base.target)) star v q
        (fun y σ=>J y (r.restRestrict σ) (r.restSpin σ)*
          nativeRestGeneratedTestValue A base R C (r.restRestrict σ)*
          (nativeStarPairFactor w φ as star (cumulativeIncrements (q 0) (fun j=>q (j+1))) (fun u v=>R u v-C star) y
            (A.cavityLeft.atSlot (r.restRestrict σ) (A.cavityLeftSlot base.target)))^h.toothCount) x).sum := by
  rw [native_star_field_disorder_list_mean T P.target star hw φ ho,
    native_star_field_disorder_list_mean A base.target star hw φ ho]
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y=>h.old_signed_row hw φ ho aRow R C
      (cumulativeIncrements (q 0) (fun j=>q (j+1))) J (x+y) H
  · intro r σ
    exact ((hJ _ _).mul_const _).mul
      ((native_star_pair_factor_smooth as star hw φ ho _ (fun u v=>R u v-C star) _ 0).pow h.toothCount)
  · intro p σ
    exact (hJ _ _).mul_const _

theorem NativeProjectionSpine.replaced_signed_disorder_row
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
          nativeRestGeneratedTestValue T P R C
            (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.target) (p.restRestrict σ) (p.restSpin σ))) x).sum=
    ((nativeHighMarkedRows A base.target star aRow).map fun r=>r.coeff*
      H (r.tree.splitIndex (r.embed base.target) r.mark) (decide (r.mark=r.embed base.target))*
      nativeStarFieldDisorderMean w φ r.tree.cavityLeft (r.tree.cavityLeftSlot (r.embed base.target)) star v q
        (fun y σ=>J y (r.restRestrict σ) (r.restSpin σ)*
          nativeRestGeneratedTestValue A base R C
            (nativeReplaceAtSlot A.cavityLeft (A.cavityLeftSlot base.target) (r.restRestrict σ) (r.restSpin σ))*
          (nativeStarPairFactor w φ as star (cumulativeIncrements (q 0) (fun j=>q (j+1))) (fun u v=>R u v-C star) y
            (r.restSpin σ))^h.toothCount) x).sum := by
  rw [native_star_field_disorder_list_mean T P.target star hw φ ho,
    native_star_field_disorder_list_mean A base.target star hw φ ho]
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y=>h.replaced_signed_row hA hT hw φ aRow ho R C
      (cumulativeIncrements (q 0) (fun j=>q (j+1))) J (x+y) H
  · intro r σ
    exact ((hJ _ _).mul_const _).mul
      ((native_star_pair_factor_smooth as star hw φ ho _ (fun u v=>R u v-C star) _ 0).pow h.toothCount)
  · intro p σ
    exact (hJ _ _).mul_const _

end OAI.SKFluctuations.Hierarchy.ClockTree
