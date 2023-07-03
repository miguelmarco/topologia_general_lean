import .conjuntos
import tactic

noncomputable theory

open function


-- definimos la función identidad
def identidad {X : Type} : X → X := λ x, x

-- demostramos un lema trivial para que el simplificador lo use
@[simp]
lemma identidad_def {X : Type} (x : X) : identidad x = x :=
begin
  refl,
end

-- algunas propiedades de la aplicación identidad
-- las marcamos como `[simp]`  para que el simplificador las use
@[simp]
lemma identidad_neutro_derecha {X Y: Type} (f : X → Y) : f ∘ identidad = f :=
begin
  refl,
end

@[simp]
lemma identidad_neutro_izquierda {X Y : Type} (f : X → Y) : identidad ∘ f = f :=
begin
  refl,
end

-- y como actua la identidad sobre conjuntos
@[simp]
lemma identidad_imagen {X : Type} (U : set X) : identidad '' U = U :=
begin
  ext x,
  simp,
end

@[simp]
lemma identidad_preimagen {X : Type} (U : set X) : identidad ⁻¹' U = U :=
begin
  ext x,
  simp,
end


-- y lo que significa que dos funciones sean inversas
def inversas  {X Y : Type} (f : X → Y) (g : Y → X ) :=
     g ∘ f = identidad ∧ f ∘ g = identidad


-- ser inversas es reflexiva
lemma inversas_sii {X Y : Type } (f : X → Y) (g : Y → X ) : inversas f g ↔ inversas g f :=
begin
  unfold inversas,
  itauto,
end

-- trivialmente, componer con la inversa es la identidad
@[simp]
lemma inversa_cancela_izquierda {X Y : Type} (f : X → Y) (g : Y → X) (h : inversas f g) :
f ∘ g = identidad :=
begin
  cases h with hfg hgf,
  exact hgf,
end

@[simp]
lemma inversa_cancela_izquierda' {X Y : Type} (f : X → Y) (g : Y → X) (h : inversas g f) :
f ∘ g = identidad :=
begin
  cases h with hfg hgf,
  exact hfg,
end

@[simp]
lemma inversa_cancela_derecha {X Y : Type} (f : X → Y) (g : Y → X) (h : inversas f g) :
g ∘ f = identidad :=
begin
  cases h with hfg hgf,
  exact hfg,
end

@[simp]
lemma inversa_cancela_derecha' {X Y : Type} (f : X → Y) (g : Y → X) (h : inversas g f) :
g ∘ f = identidad :=
begin
  cases h with hfg hgf,
  exact hgf,
end



lemma inversa_unica {X Y : Type} (f : X → Y) (g h : Y → X) : inversas f g → inversas f h → g = h :=
begin
  intros h1 h2,
  calc
    g   =  g ∘ identidad :  by {simp,}
    ... =  g ∘ (f ∘ h)   :  by {simp [h2],}
    ... = (g ∘f ) ∘ h    :  by {simp,}
    ... = identidad ∘ h  :  by {simp [h1],}  
    ... = h              :  by {simp,}
end

-- una aplicación inyectiva y sobreyectiva tiene inversa
lemma inversa_de_inyectiva_y_sobreyectiva {X Y : Type} (f : X →  Y) (hin : injective f) (hsob : surjective f ) :
∃ g : Y → X, inversas f g :=
begin
  choose g hg using hsob, -- usamos la suprayectividad, y el axioma de elección, para definir una aplicación en sentido contrario
  use g,
  split,
  {
    ext,
    apply hin,
    simp,
    rw hg,
  },
  {
    ext,
    simp,
    apply hg,
  }
end


def inversa {X Y : Type} (f : X → Y) (hin :bijective f) : Y → X := (equiv.of_bijective f hin).inv_fun

@[simp]
lemma inversa_es_inversa_izquierda {X Y : Type} (f : X → Y) (hin : bijective f) : (inversa f hin ) ∘ f = identidad :=
begin
  ext,
  apply (equiv.of_bijective f hin).left_inv,
end

@[simp]
lemma inversa_es_inversa_derecha {X Y : Type} (f : X → Y) (hin :bijective f) : f ∘ (inversa f hin )  = identidad :=
begin
  ext,
  apply (equiv.of_bijective f hin).right_inv,
end


-- en una aplicación suprayectiva, la imagen de la preimagen es el conjunto
@[simp]
lemma imagen_preimagen_sobre {X Y : Type} (f : X → Y) (hsob :surjective f) (V : set Y):
f '' (f ⁻¹' V) = V :=
begin
  apply doble_contenido,
  {
    apply imagen_preimagen_contenida,
  },
  {
    intros y hy,
    specialize hsob y,
    cases hsob with x hx,
    rw ← hx,
    simp,
    use x,
    simp,
    rw hx,
    exact hy,
  }
end

-- en una aplicación inyectiva, la preimagen de la imagen es el conjunto
@[simp]
lemma preimagen_imagen_inyectiva {X Y : Type} (f : X → Y) (hinj :injective f) (U : set X) :
f ⁻¹' (f '' U) = U :=
begin
  apply doble_contenido,
  {
    intros x hx,
    simp at hx,
    cases hx with x' hx',
    cases hx' with hx'U hxx',
    specialize hinj hxx',
    rw hinj at hx'U,
    exact hx'U,
  },
  {
    apply contenido_en_preimagen_imagen,
  }
end