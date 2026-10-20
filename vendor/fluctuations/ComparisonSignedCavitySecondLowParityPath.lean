module

public import ComparisonSignedCavityObservedSecondLowJoin
public import Mathlib.Data.List.Count

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
namespace OAI.SKFluctuations.Cavity

theorem native_second_low_even_word_target_first
    {α : Type*} [DecidableEq α] (A B c e d : α)
    (hAB : A≠B) (hAc : A≠c) (hed : e≠d)
    (H : ∀x,Even ([A,B,A,c,e,d].count x)) :
    (c=e ∧ d=B) ∨ (c=d ∧ e=B) := by
  have HA:=H A
  have HB:=H B
  have HC:=H c
  have HE:=H e
  have HD:=H d
  by_cases hEA : e=A
  <;> by_cases hDA : d=A
  <;> by_cases hCB : c=B
  <;> by_cases hEB : e=B
  <;> by_cases hDB : d=B
  <;> by_cases hEC : e=c
  <;> by_cases hDC : d=c
  <;> (have hBA:=hAB.symm
       have hcA : c≠A:=Ne.symm hAc
       have hdE:=hed.symm
       try have hAE : A≠e :=Ne.symm hEA
       try have hAD : A≠d :=Ne.symm hDA
       try have hBC : B≠c :=Ne.symm hCB
       try have hBE : B≠e :=Ne.symm hEB
       try have hBD : B≠d :=Ne.symm hDB
       try have hcE : c≠e :=Ne.symm hEC
       try have hcD : c≠d :=Ne.symm hDC
       simp_all [Nat.even_iff,List.count_cons])

theorem native_second_low_even_word_path
    {α : Type*} [DecidableEq α] (A B f c e d : α)
    (hAB : A≠B) (hfc : f≠c) (hed : e≠d)
    (H : ∀x,Even ([A,B,f,c,e,d].count x)) :
    (A=f ∧ c=e ∧ d=B) ∨ (A=f ∧ c=d ∧ e=B) ∨
    (A=c ∧ f=e ∧ d=B) ∨ (A=c ∧ f=d ∧ e=B) ∨
    (A=e ∧ d=f ∧ c=B) ∨ (A=e ∧ d=c ∧ f=B) ∨
    (A=d ∧ e=f ∧ c=B) ∨ (A=d ∧ e=c ∧ f=B) := by
  by_cases hAf : A=f
  · subst f
    have HR:=native_second_low_even_word_target_first A B c e d hAB hfc hed H
    rcases HR with ⟨he,hd⟩|⟨hd,he⟩ <;> simp_all
  by_cases hAc : A=c
  · subst c
    have HH x : Even ([A,B,A,f,e,d].count x):=by
      convert H x using 1
      simp only [List.count_cons,List.count_nil]
      omega
    have HR:=native_second_low_even_word_target_first A B f e d hAB hfc.symm hed HH
    rcases HR with ⟨he,hd⟩|⟨hd,he⟩ <;> simp_all
  by_cases hAe : A=e
  · subst e
    have HH x : Even ([A,B,A,d,f,c].count x):=by
      convert H x using 1
      simp only [List.count_cons,List.count_nil]
      omega
    have HR:=native_second_low_even_word_target_first A B d f c hAB hed hfc HH
    rcases HR with ⟨he,hd⟩|⟨hd,he⟩ <;> simp_all
  by_cases hAd : A=d
  · subst d
    have HH x : Even ([A,B,A,e,f,c].count x):=by
      convert H x using 1
      simp only [List.count_cons,List.count_nil]
      omega
    have HR:=native_second_low_even_word_target_first A B e f c hAB hed.symm hfc HH
    rcases HR with ⟨he,hd⟩|⟨hd,he⟩ <;> simp_all
  have HA:=H A
  have hBA:=hAB.symm
  have hfA : f≠A:=Ne.symm hAf
  have hcA : c≠A:=Ne.symm hAc
  have heA : e≠A:=Ne.symm hAe
  have hdA : d≠A:=Ne.symm hAd
  simp_all [Nat.even_iff,List.count_cons]

end OAI.SKFluctuations.Cavity
