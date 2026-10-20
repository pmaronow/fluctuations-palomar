module

public import ComparisonSignedCavitySecondLowObservedPartition

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree
open scoped BigOperators
set_option maxHeartbeats 24000000
attribute [local instance] Classical.propDecidable

def nativeSecondLowPathGamma {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (K : ℕ→ℝ)
    (a z f c e d : T.Slot) (j : Fin 8) : ℝ :=
  match j.val with
  | 0=>fullScalarCutGamma T U K a f*fullScalarCutGamma T U K c e*fullScalarCutGamma T U K d z
  | 1=>fullScalarCutGamma T U K a f*fullScalarCutGamma T U K c d*fullScalarCutGamma T U K e z
  | 2=>fullScalarCutGamma T U K a c*fullScalarCutGamma T U K f e*fullScalarCutGamma T U K d z
  | 3=>fullScalarCutGamma T U K a c*fullScalarCutGamma T U K f d*fullScalarCutGamma T U K e z
  | 4=>fullScalarCutGamma T U K a e*fullScalarCutGamma T U K d f*fullScalarCutGamma T U K c z
  | 5=>fullScalarCutGamma T U K a e*fullScalarCutGamma T U K d c*fullScalarCutGamma T U K f z
  | 6=>fullScalarCutGamma T U K a d*fullScalarCutGamma T U K e f*fullScalarCutGamma T U K c z
  | _=>fullScalarCutGamma T U K a d*fullScalarCutGamma T U K e c*fullScalarCutGamma T U K f z

theorem fullScalarCutMoment_six_edge_orientations {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (K : ℕ→ℝ) (a z f c e d : T.Slot) :
    fullScalarCutMoment T U K [a,z,f,c,e,d]=fullScalarCutMoment T U K [a,z,f,c,d,e] ∧
    fullScalarCutMoment T U K [a,z,f,c,e,d]=fullScalarCutMoment T U K [a,z,c,f,e,d] ∧
    fullScalarCutMoment T U K [a,z,f,c,e,d]=fullScalarCutMoment T U K [a,z,c,f,d,e] ∧
    fullScalarCutMoment T U K [a,z,f,c,e,d]=fullScalarCutMoment T U K [a,z,e,d,f,c] ∧
    fullScalarCutMoment T U K [a,z,f,c,e,d]=fullScalarCutMoment T U K [a,z,e,d,c,f] ∧
    fullScalarCutMoment T U K [a,z,f,c,e,d]=fullScalarCutMoment T U K [a,z,d,e,f,c] ∧
    fullScalarCutMoment T U K [a,z,f,c,e,d]=fullScalarCutMoment T U K [a,z,d,e,c,f] := by
  unfold fullScalarCutMoment scalarCutMoment
  repeat' constructor
  all_goals congr 1;funext σ
  all_goals simp only [List.map_cons,List.map_nil,ClockTree.slotProduct]
  all_goals ring

theorem native_second_low_scalar_factor_all_paths {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (hU : U≤as.length) (K : ℕ→ℝ) (a z f c e d : T.Slot)
    (haz : T.splitIndex a z<U) (hfc : T.splitIndex f c<U) (hed : T.splitIndex e d<U)
    (j : Fin 8) (H : nativeSecondLowBlockPath j (T.cutBlock U hU a) (T.cutBlock U hU z)
      (T.cutBlock U hU f) (T.cutBlock U hU c) (T.cutBlock U hU e) (T.cutBlock U hU d)) :
    fullScalarCutMoment T U K [a,z,f,c,e,d]=nativeSecondLowPathGamma T U K a z f c e d j := by
  have Hcf : T.splitIndex c f<U := by simpa only [T.splitIndex_symm c f] using hfc
  have Hde : T.splitIndex d e<U := by simpa only [T.splitIndex_symm d e] using hed
  have HB (u v : T.Slot) (HH : T.cutBlock U hU u=T.cutBlock U hU v) :
      U≤T.splitIndex u v := (T.cutBlock_eq_iff U hU u v).mp HH
  rcases fullScalarCutMoment_six_edge_orientations T U K a z f c e d with ⟨P₁,P₂,P₃,P₄,P₅,P₆,P₇⟩
  fin_cases j
  all_goals dsimp only [nativeSecondLowBlockPath] at H
  all_goals rcases H with ⟨H₁,H₂,H₃⟩
  · exact native_second_low_path_scalar_factor T ho U hU K a z f c e d haz hfc hed
      (HB _ _ H₁) (HB _ _ H₂) (HB _ _ H₃)
  · rw [P₁]
    exact native_second_low_path_scalar_factor T ho U hU K a z f c d e haz hfc Hde
      (HB _ _ H₁) (HB _ _ H₂) (HB _ _ H₃)
  · rw [P₂]
    exact native_second_low_path_scalar_factor T ho U hU K a z c f e d haz Hcf hed
      (HB _ _ H₁) (HB _ _ H₂) (HB _ _ H₃)
  · rw [P₃]
    exact native_second_low_path_scalar_factor T ho U hU K a z c f d e haz Hcf Hde
      (HB _ _ H₁) (HB _ _ H₂) (HB _ _ H₃)
  · rw [P₄]
    exact native_second_low_path_scalar_factor T ho U hU K a z e d f c haz hed hfc
      (HB _ _ H₁) (HB _ _ H₂) (HB _ _ H₃)
  · rw [P₅]
    exact native_second_low_path_scalar_factor T ho U hU K a z e d c f haz hed Hcf
      (HB _ _ H₁) (HB _ _ H₂) (HB _ _ H₃)
  · rw [P₆]
    exact native_second_low_path_scalar_factor T ho U hU K a z d e f c haz Hde hfc
      (HB _ _ H₁) (HB _ _ H₂) (HB _ _ H₃)
  · rw [P₇]
    exact native_second_low_path_scalar_factor T ho U hU K a z d e c f haz Hde Hcf
      (HB _ _ H₁) (HB _ _ H₂) (HB _ _ H₃)

end OAI.SKFluctuations.Cavity
