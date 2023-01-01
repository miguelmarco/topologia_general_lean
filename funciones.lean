import tactic

noncomputable theory

open function


-- definimos la función identidad
def identidad {X : Type} : X → X := λ x, x

-- y lo que significa que dos funciones sean inversas
def inversas  {X Y : Type} (f : X → Y) (g : Y → X ) :=
     g ∘ f = identidad ∧ f ∘ g = identidad


lemma inversas_sii {X Y : Type } (f : X → Y) (g : Y → X ) : inversas f g ↔ inversas g f :=
begin
  unfold inversas,
  itauto,
end



lemma inversa_unica {X Y : Type} (f : X → Y) (g h : Y → X) : inversas f g → inversas f h → g = h :=
begin
  intros h1 h2,
  unfold inversas at *,
  cases h1 with h1a h1b,
  cases h2 with h2a h2b,
  ext,
  have  haux1:  (f ∘ g) x = x,
  {
    unfold identidad at h1b,
    rw h1b,
  },
  rw ← haux1,
  change  ((g ∘ f) ∘ g) x = ((h ∘ f) ∘ g) x,
  rw h1a,
  rw h2a,
end


lemma inversa_de_inyectiva_y_sobreyectiva {X Y : Type} (f : X →  Y) (hin : injective f) (hsob : surjective f ) :
∃ g : Y → X, inversas f g :=
begin
  choose g hg using hsob,
  use g,
  split,
  {
    ext,
    apply hin,
    simp,
    specialize hg (f x),
    rw hg,
    refl,
  },
  ext,
  specialize hg x,
  exact hg,
end


def inversa {X Y : Type} (f : X → Y) (hin :bijective f) : Y → X := (equiv.of_bijective f hin).inv_fun

lemma inversa_es_inversa_izquierda {X Y : Type} (f : X → Y) (hin :bijective f) : (inversa f hin ) ∘ f = identidad :=
begin
  ext,
  apply (equiv.of_bijective f hin).left_inv,
end

lemma inversa_es_inversa_derecha {X Y : Type} (f : X → Y) (hin :bijective f) : f ∘ (inversa f hin )  = identidad :=
begin
  ext,
  apply (equiv.of_bijective f hin).right_inv,
end
