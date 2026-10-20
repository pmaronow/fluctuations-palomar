module

public import CavityRealMomentHolder
public import CavityAttachedTree

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy

 theorem finite_weighted_rpow_moment_le {A : Type*} [Fintype A] (w F : A → ℝ)
    (hw : ∀ a, 0≤w a) (hmass : ∑ a, w a=1)
    {p r B : ℝ} (hp : 0<p) (hpr : p≤r) (hB : 0≤B)
    (hmoment : (∑ a, w a*|F a|^r)≤B^r) :
    (∑ a, w a*|F a|^p)≤B^p := by
  by_cases he : p=r
  · simpa only [he] using hmoment
  have hlt : p<r := lt_of_le_of_ne hpr he
  have hr : 0<r := hp.trans hlt
  have hrp : 0<r-p := sub_pos.mpr hlt
  have hconj : (r/p).HolderConjugate (r/(r-p)) := by
    rw [Real.holderConjugate_iff]
    constructor
    · exact (one_lt_div hp).mpr hlt
    · field_simp
      <;> ring
  have H := finite_weighted_holder w (fun a => |F a|^p) (fun _ => (1:ℝ)) hw hconj
  have hepr : p*(r/p)=r := by field_simp
  have heinv : 1/(r/p)=p/r := by field_simp
  simp only [mul_one,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
    ←Real.rpow_mul (abs_nonneg _),hepr,abs_one,Real.one_rpow,mul_one,hmass,heinv] at H
  have hmnon : 0≤∑ a, w a*|F a|^r := Finset.sum_nonneg fun a _ =>
    mul_nonneg (hw a) (Real.rpow_nonneg (abs_nonneg _) _)
  have HH := Real.rpow_le_rpow hmnon hmoment (div_nonneg hp.le hr.le)
  rw [←Real.rpow_mul hB] at HH
  have hefinal : r*(p/r)=p := by field_simp
  rw [hefinal] at HH
  exact H.trans HH

namespace ClockTree
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]

 theorem disorderExpect_rpow_moment_le {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) (T : ClockTree S as)
    (F : T.Assignment → ℝ) {p r B : ℝ} (hp : 0<p) (hpr : p≤r) (hB : 0≤B)
    (hmoment : T.disorderExpect w φ v q (fun σ => |F σ|^r) x≤B^r) :
    T.disorderExpect w φ v q (fun σ => |F σ|^p) x≤B^p := by
  exact finite_weighted_rpow_moment_le (fun σ=>T.disorderWeight w φ v q σ x) F
    (T.disorderWeight_probability hw φ ho v q x).1
    (T.disorderWeight_probability hw φ ho v q x).2 hp hpr hB hmoment

end ClockTree
end OAI.SKFluctuations.Hierarchy
