module

public import LatinAvailability
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

noncomputable section

namespace LatinonEntropy

def historyArray {n : ℕ} (h : LatinHistory n) (hlen : h.length = n)
    (x y : Fin n) : Fin n :=
  (h.reverse.get ⟨x.val,by simpa only [List.length_reverse,hlen] using x.isLt⟩) y

theorem historyArray_row_bijective {n : ℕ} (h : LatinHistory n) (hlen : h.length = n) (x : Fin n) :
    Function.Bijective (historyArray h hlen x) :=
  (h.reverse.get ⟨x.val,by simpa only [List.length_reverse,hlen] using x.isLt⟩).bijective

theorem historyArray_column_bijective {n : ℕ} (h : LatinHistory n) (hlen : h.length = n)
    (hv : LatinHistoryValid h) (y : Fin n) :
    Function.Bijective (fun x => historyArray h hlen x y) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_,rfl⟩
  intro x z he
  let l := h.reverse.map (fun sigma => sigma y)
  have hl : l.Nodup := by
    dsimp only [l]
    rw [List.map_reverse]
    simpa only [List.nodup_reverse] using valid_row_nodup hv y
  have hlenl : l.length = n := by simp only [l,List.length_map,List.length_reverse,hlen]
  have he' : l.get ⟨x.val,by rw [hlenl]; exact x.isLt⟩ =
      l.get ⟨z.val,by rw [hlenl]; exact z.isLt⟩ := by
    simpa only [l,List.get_eq_getElem,List.getElem_map,historyArray] using he
  exact Fin.ext (congrArg (fun k : Fin l.length => k.val) (hl.injective_get he'))

/-- Retaining every chronological row makes the passage to arrays injective. -/
theorem historyArray_injective {n : ℕ} (h g : LatinHistory n)
    (hh : h.length = n) (hg : g.length = n) (he : historyArray h hh = historyArray g hg) : h = g := by
  have hre : h.reverse = g.reverse := by
    apply List.ext_get (by simp only [List.length_reverse,hh,hg])
    intro k hk hk'
    have hkn : k < n := by simpa only [List.length_reverse,hh] using hk
    apply Equiv.ext
    intro y
    exact congrFun (congrFun he ⟨k,hkn⟩) y
  simpa only [List.reverse_reverse] using congrArg List.reverse hre

def LatinArray (n : ℕ) := {L : Fin n → Fin n → Fin n //
  (∀ x, Function.Bijective (L x)) ∧ (∀ y, Function.Bijective (fun x => L x y))}

def historyToLatinArray {n : ℕ} (h : LatinHistory n) (hlen : h.length = n)
    (hv : LatinHistoryValid h) : LatinArray n :=
  ⟨historyArray h hlen,historyArray_row_bijective h hlen,historyArray_column_bijective h hlen hv⟩

theorem historyToLatinArray_injective {n : ℕ} (h g : LatinHistory n)
    (hh : h.length = n) (hg : g.length = n) (hv : LatinHistoryValid h) (gv : LatinHistoryValid g)
    (he : historyToLatinArray h hh hv = historyToLatinArray g hg gv) : h = g :=
  historyArray_injective h g hh hg (congrArg Subtype.val he)

end LatinonEntropy

#print axioms LatinonEntropy.historyArray_column_bijective
#print axioms LatinonEntropy.historyToLatinArray_injective
