import Mathlib.CategoryTheory.Category.Cat

universe u

namespace CategoryTheory


variable {C D : Cat}
variable {a b : C}
variable (F : C ⥤ D)

def isConnected (c : C ) (d : C) : Prop := ∃ _ : c ⟶ d, True
def refl_trans_symm_closure{α : Type u} (r : α → α → Prop) a b := Quot.mk r a = Quot.mk r  b
def isConnectedByZigZag  : C → C → Prop   := refl_trans_symm_closure isConnected

lemma easytransport   (h : isConnected a b) : isConnected (F.obj a) (F.obj b) := by
   obtain ⟨f,_⟩ := h
   exact ⟨F.map f, trivial⟩

lemma transport (h : isConnectedByZigZag a b) : isConnectedByZigZag (F.obj a) (F.obj b) := by
   obtain x := h
   sorry


end CategoryTheory
