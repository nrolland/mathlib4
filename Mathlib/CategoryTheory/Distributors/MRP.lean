import Mathlib.CategoryTheory.Category.Cat

namespace CategoryTheory

variable (B : Cat)

def ok     : Bᵒᵖ ⥤ Bᵒᵖ := 𝟭 (Bᵒᵖ)
def not_ok : Bᵒᵖ ⥤ Bᵒᵖ := 𝟙 (Bᵒᵖ)

end CategoryTheory
