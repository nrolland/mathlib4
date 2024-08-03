import Mathlib.CategoryTheory.Category.Cat

universe u


lemma mylemma {α : Sort u} {s : Setoid α} : (Quotient.lift (Quotient.mk s) (fun _ _ => Quotient.sound)) = fun x => x := sorry


namespace CategoryTheory


variable {C D : Cat}
variable {a b : C}
variable (F : C ⥤ D)

-- relation
def isConnected (c : C ) (d : C) : Prop := ∃ _ : c ⟶ d, True

lemma transport (h : isConnected a b) : isConnected (F.obj a) (F.obj b) := by
   obtain ⟨f,_⟩ := h
   exact ⟨F.map f, trivial⟩

def isConnectedByZigZag  : C → C → Prop   := EqvGen isConnected

lemma transportExt  (h : isConnectedByZigZag a b ) : isConnectedByZigZag (F.obj a) (F.obj b) := by
  induction h
  case rel h => exact (EqvGen.rel _ _ (transport F h))
  case refl => exact EqvGen.refl _
  case symm w => exact EqvGen.symm _ _ w -- case analysis
  case trans f g => exact EqvGen.trans _ _ _ f g

def catisSetoid : Setoid C where
  r := isConnectedByZigZag
  iseqv := EqvGen.is_equivalence isConnected

def toCC (x : C) : Quotient (@catisSetoid C) := Quotient.mk (@catisSetoid C) x

lemma transportExtQuot : isConnectedByZigZag a b → toCC (F.obj a) = toCC (F.obj b) :=
    Quot.sound ∘ transportExt F

-- induction is not case analysis
lemma transportExtQuot' (h: isConnectedByZigZag a b) : toCC (F.obj a) = toCC (F.obj b) := by
  induction h
  case rel a b h => exact (transport F h) |> EqvGen.rel _ _ |> Quot.sound
  case refl x => exact EqvGen.refl _  |> Quot.sound
  case symm w /- different type -/ => exact Quotient.exact w /- not case -/|> EqvGen.symm _ _ |> Quot.sound
  case trans _  _ _ f g => sorry

abbrev liftedMk  {α : Sort u} (s : Setoid α)  := Quotient.lift (Quotient.mk s) (fun _ _ => Quotient.sound)

lemma complex {α : Sort u} {s : Setoid α} : liftedMk s ∘ Quotient.mk s = Quotient.mk s := by funext x; exact Quot.liftBeta  (Quotient.mk s) (fun _ _ => Quotient.sound) x
lemma simple  {α : Sort u} {s : Setoid α} : liftedMk s ∘ Quotient.mk s = Quotient.mk s := rfl


end CategoryTheory
