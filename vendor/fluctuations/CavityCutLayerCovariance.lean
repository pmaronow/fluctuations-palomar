module

public import CavityCutTruncation
public import CavityBoundaryCovariance

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

private theorem signed_list_abs_le {A : Type*} (ps : List A)
    (c f : A → ℝ) {C : ℝ} (hf : ∀ p ∈ ps, |f p| ≤ C) :
    |(ps.map (fun p => c p*f p)).sum| ≤ (ps.map (fun p => |c p|)).sum*C := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons]
    calc
      _ ≤ |c p*f p|+|(ps.map (fun p => c p*f p)).sum| := abs_add_le _ _
      _ ≤ |c p| * C+(ps.map (fun p => |c p|)).sum*C := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left (hf p List.mem_cons_self) (abs_nonneg _))
          (ih (fun q hq => hf q (List.mem_cons_of_mem _ hq)))
      _ = _ := by ring

def actualCutRow {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) (a v : ℝ)
    (P : T.Assignment → ℝ) (F : S → ℝ) (x : ι → ℝ) : ℝ :=
  ((T.cutMarkedAttach a v).map (fun p => p.coeff*p.toPlacement.eval w φ P F x)).sum

def actualBoundaryCovarianceRadius {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (P : T.Assignment → ℝ) (F : S → ℝ) (x : ι → ℝ) : ℝ :=
  Real.sqrt (T.expect w φ (fun σ => (P σ-T.expect w φ P x)^2) x *
    gaussianHierarchyMean w φ (fun σ =>
      (F σ-gaussianHierarchyMean w φ F steps x)^2) steps x)

theorem actual_cut_row_centered_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) {a : ℝ} (ho : OrderedSteps a steps) (v : ℝ)
    (P : T.Assignment → ℝ) (F : S → ℝ) (x : ι → ℝ) :
    |actualCutRow T w φ a v P F x-
        a*T.expect w φ P x*gaussianHierarchyMean w φ F steps x| ≤
      ((T.cutMarkedAttach a v).map (fun p => |p.coeff|)).sum *
        actualBoundaryCovarianceRadius T w φ P F x := by
  let b := T.expect w φ P x*gaussianHierarchyMean w φ F steps x
  have hs : ((T.cutMarkedAttach a v).map (fun p =>
      p.coeff*(p.toPlacement.eval w φ P F x-b))).sum =
        actualCutRow T w φ a v P F x-a*b := by
    have hl (ps : List (ReplicaTree.MarkedPlacement T)) :
        (ps.map (fun p => p.coeff*(p.toPlacement.eval w φ P F x-b))).sum =
        (ps.map (fun p => p.coeff*p.toPlacement.eval w φ P F x)).sum-
        (ps.map (fun p => p.coeff)).sum*b := by
      induction ps with
      | nil => simp
      | cons p ps ih => simp only [List.map_cons, List.sum_cons, ih]; ring
    rw [hl, T.cutMarkedAttach_mass]
    rfl
  have h := signed_list_abs_le (T.cutMarkedAttach a v) (fun p => p.coeff)
    (fun p => p.toPlacement.eval w φ P F x-b) (C := actualBoundaryCovarianceRadius T w φ P F x) ?_
  · rw [hs] at h
    simpa only [b, mul_assoc] using h
  · intro p hp
    unfold actualBoundaryCovarianceRadius
    have hs := actual_preserving_attachment_covariance_sq_le hw φ T ho p
      (T.cutMarkedAttach_preserves hw φ ho v p hp) P F x
    apply (Real.le_sqrt (abs_nonneg _) (mul_nonneg
      (T.expect_nonneg hw φ ho (fun _ => sq_nonneg _) x)
      (gaussianHierarchyMean_nonneg hw φ (fun _ => sq_nonneg _) steps ho x))).mpr
    simpa only [b, sq_abs] using hs

theorem actual_cut_layer_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) {a v z : ℝ} (ho : OrderedSteps a steps)
    (hav : a ≤ v) (hvz : v ≤ z) (hz : z ≤ 2*v)
    (P : T.Assignment → ℝ) (F : S → ℝ) (x : ι → ℝ) :
    |actualCutRow T w φ a z P F x-actualCutRow T w φ a v P F x| ≤
      6*(T.leaves:ℝ)*v*actualBoundaryCovarianceRadius T w φ P F x := by
  let b := a*T.expect w φ P x*gaussianHierarchyMean w φ F steps x
  have h1 := actual_cut_row_centered_abs_le hw φ T ho v P F x
  have h2 := actual_cut_row_centered_abs_le hw φ T ho z P F x
  have hv := T.cutMarkedAttach_layer_variation_le ho hav hvz hz
  calc
    _ = |(actualCutRow T w φ a z P F x-b)-(actualCutRow T w φ a v P F x-b)| := by congr 1; ring
    _ ≤ |actualCutRow T w φ a z P F x-b|+|actualCutRow T w φ a v P F x-b| := abs_sub _ _
    _ ≤ ((T.cutMarkedAttach a z).map (fun p => |p.coeff|)).sum*actualBoundaryCovarianceRadius T w φ P F x+
      ((T.cutMarkedAttach a v).map (fun p => |p.coeff|)).sum*actualBoundaryCovarianceRadius T w φ P F x := add_le_add h2 h1
    _ = (((T.cutMarkedAttach a v).map (fun p => |p.coeff|)).sum+
      ((T.cutMarkedAttach a z).map (fun p => |p.coeff|)).sum)*actualBoundaryCovarianceRadius T w φ P F x := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hv (Real.sqrt_nonneg _)

end OAI.SKFluctuations.Cavity
