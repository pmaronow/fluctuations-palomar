module

public import ComparisonSignedCavitySecondLowScalarPathSupport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree
open scoped BigOperators
set_option maxHeartbeats 18000000
set_option maxRecDepth 12000
attribute [local instance] Classical.propDecidable

def nativeSecondLowBlockPath {α : Type*} (j : Fin 8) (A B f c e d : α) : Prop :=
  match j.val with
  | 0=>A=f ∧ c=e ∧ d=B
  | 1=>A=f ∧ c=d ∧ e=B
  | 2=>A=c ∧ f=e ∧ d=B
  | 3=>A=c ∧ f=d ∧ e=B
  | 4=>A=e ∧ d=f ∧ c=B
  | 5=>A=e ∧ d=c ∧ f=B
  | 6=>A=d ∧ e=f ∧ c=B
  | _=>A=d ∧ e=c ∧ f=B

theorem native_second_low_block_paths_disjoint
    {α : Type*} (A B f c e d : α) (hAB : A≠B) (hfc : f≠c) (hed : e≠d)
    (j l : Fin 8) (Hj : nativeSecondLowBlockPath j A B f c e d)
    (Hl : nativeSecondLowBlockPath l A B f c e d) : j=l := by
  fin_cases j <;> fin_cases l
  all_goals dsimp only [nativeSecondLowBlockPath] at Hj Hl
  all_goals rcases Hj with ⟨H₁,H₂,H₃⟩
  all_goals rcases Hl with ⟨J₁,J₂,J₃⟩
  all_goals first | rfl | (subst_vars; contradiction)

theorem native_second_low_path_partition
    {α : Type*} (A B f c e d : α) (hAB : A≠B) (hfc : f≠c) (hed : e≠d)
    (V : ℝ) (H : V≠0→∃j : Fin 8,nativeSecondLowBlockPath j A B f c e d) :
    V=∑j : Fin 8,if nativeSecondLowBlockPath j A B f c e d then V else 0 := by
  classical
  by_cases HV : V=0
  · simp [HV]
  obtain ⟨j,Hj⟩:=H HV
  rw [Finset.sum_eq_single j]
  · simp [Hj]
  · intro l _ hlj
    have Hl : ¬nativeSecondLowBlockPath l A B f c e d := by
      intro Hlp
      exact hlj (native_second_low_block_paths_disjoint A B f c e d hAB hfc hed l j Hlp Hj)
    simp [Hl]
  · simp

theorem native_second_low_scalar_moment_eq_eight_paths
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (U : ℕ) (hU : U≤as.length) (K : ℕ→ℝ)
    (a z f c e d : T.Slot)
    (haz : T.splitIndex a z<U) (hfc : T.splitIndex f c<U) (hed : T.splitIndex e d<U) :
    fullScalarCutMoment T U K [a,z,f,c,e,d]=
      ∑j : Fin 8,if nativeSecondLowBlockPath j (T.cutBlock U hU a) (T.cutBlock U hU z)
        (T.cutBlock U hU f) (T.cutBlock U hU c) (T.cutBlock U hU e) (T.cutBlock U hU d)
        then fullScalarCutMoment T U K [a,z,f,c,e,d] else 0 := by
  classical
  apply native_second_low_path_partition
  · intro HE
    have HH:=(T.cutBlock_eq_iff U hU a z).mp HE
    omega
  · intro HE
    have HH:=(T.cutBlock_eq_iff U hU f c).mp HE
    omega
  · intro HE
    have HH:=(T.cutBlock_eq_iff U hU e d).mp HE
    omega
  · intro HV
    have HH:=native_second_low_scalar_nonzero_path T ho U hU K a z f c e d haz hfc hed HV
    have HB (u v : T.Slot) (H : U≤T.splitIndex u v) :
        T.cutBlock U hU u=T.cutBlock U hU v:=(T.cutBlock_eq_iff U hU u v).mpr H
    rcases HH with ⟨H₁,H₂,H₃⟩|⟨H₁,H₂,H₃⟩|⟨H₁,H₂,H₃⟩|⟨H₁,H₂,H₃⟩|
      ⟨H₁,H₂,H₃⟩|⟨H₁,H₂,H₃⟩|⟨H₁,H₂,H₃⟩|⟨H₁,H₂,H₃⟩
    · exact ⟨0,HB _ _ H₁,HB _ _ H₂,HB _ _ H₃⟩
    · exact ⟨1,HB _ _ H₁,HB _ _ H₂,HB _ _ H₃⟩
    · exact ⟨2,HB _ _ H₁,HB _ _ H₂,HB _ _ H₃⟩
    · exact ⟨3,HB _ _ H₁,HB _ _ H₂,HB _ _ H₃⟩
    · exact ⟨4,HB _ _ H₁,HB _ _ H₂,HB _ _ H₃⟩
    · exact ⟨5,HB _ _ H₁,HB _ _ H₂,HB _ _ H₃⟩
    · exact ⟨6,HB _ _ H₁,HB _ _ H₂,HB _ _ H₃⟩
    · exact ⟨7,HB _ _ H₁,HB _ _ H₂,HB _ _ H₃⟩

def nativeSecondLowPathMiddle {α : Type*} (j : Fin 8) (f c e d : α) : α :=
  match j.val with
  | 0|1=>c
  | 2|3=>f
  | 4|5=>d
  | _=>e

theorem native_second_low_path_middle_distinct
    {α : Type*} (A B f c e d : α) (hAB : A≠B) (hfc : f≠c) (hed : e≠d)
    (j : Fin 8) (H : nativeSecondLowBlockPath j A B f c e d) :
    nativeSecondLowPathMiddle j f c e d≠A ∧ nativeSecondLowPathMiddle j f c e d≠B := by
  fin_cases j
  all_goals dsimp only [nativeSecondLowBlockPath] at H
  all_goals dsimp only [nativeSecondLowPathMiddle]
  all_goals rcases H with ⟨H₁,H₂,H₃⟩
  all_goals subst_vars; simp_all
  all_goals aesop

end OAI.SKFluctuations.Cavity
