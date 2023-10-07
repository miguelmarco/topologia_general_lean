import .topologicos
import .cerrados
import tactic

open set
open topologicos
open topologicos.espacio_topologico

variables {X : Type} [espacio_topologico X] {A : set X} 


instance {X : Type} {A : set X}: has_coe (set A) (set X) := { coe :=  λ B, {(↑x) | x ∈ B}}


def restringe {X : Type} {A : set X}: set X → set A := λ B , {x | ↑x ∈ B} 


lemma restringe_coe {X : Type} {A : set X} ( C : set X) : ((coe : A → X)  ⁻¹' C) = (restringe C)  :=
begin
  refl,
end


notation `↓` d := restringe d 


variable B : set X



@[simp]
lemma pert_restringe_iff (B : set X) (x : A) : x ∈ (↓B : set A) ↔ x.val ∈ B :=
begin
  refl,
end

@[simp]
lemma sube_baja (B : set A) : (↓(↑B : set X) : set A) = B :=
begin
  ext x,
  simp,
  cases x with x hx,
  simp,
  split,
  {
    intro h,
    cases h with x' hx',
    cases hx' with hx'B hx'x,
    cases hx'x,
    simp only [subtype.val_eq_coe, subtype.coe_eta],
    exact hx'B,
  },
  {
    intro h,
    use x,
    {
      exact hx,
    },
    {
      simp,
      exact h,
    }
  }
end

@[simp]
lemma baja_sube (B : set X) : ↑(↓B : set A)  = A ∩ B :=
begin
  ext,
  split,
  {
    intro h,
    cases h with x' hx',
    cases hx' with hx'B hx'x,
    cases hx'x,
    rw ←  hx'x at ,
    split,
    {
      exact x'.2,
    },
    {
      exact hx'B,
    },
  },
  {
    intro h,
    cases h with hxA hxB,
    use ⟨x,hxA⟩,
    simp only [pert_restringe_iff, subtype.coe_mk, eq_self_iff_true, and_true],
    exact hxB,
  },
end

@[simp]
lemma pert_inclusion_iff (B: set A) (x : A) : x ∈ B ↔ ↑x ∈ (↑B: set X) :=
begin
  cases x with x hx,
  simp only [subtype.coe_mk],
  split,
  {
    intro h,
    use x,
    {
      exact hx,
    },
    {
      split, 
        exact h,
        refl,
    },
  },
  {
    intro h,
    cases h with x' hx',
    cases hx' with hx'B hx'x,
    cases hx'x,
    cases x' with x'' hx'',
    exact hx'B,
  }
end

lemma sube_contenido (B : set A) : ↑B ⊆ A :=
begin
  intros x hxB,
  cases hxB with x' hx',
  cases hx' with hx'B hx'x,
  rw ← hx'x,
  simp,
end

@[simp]
lemma sube_inter_A (B : set A) : ↑B ∩ A = ↑B :=
begin
  simp,
  apply sube_contenido,
end


@[simp]
lemma union_coe (B C : set X) :  (↓(B ∪ C) : set A) = ↓B ∪ (↓C : set A)   :=
begin
  ext x,
  simp only [pert_restringe_iff, subtype.val_eq_coe, mem_union, baja_sube, mem_inter_iff, subtype.coe_prop, true_and],
end

@[simp]
lemma union_lift (B C : set A) :  ↑(B ∪ C) = ((↑B : set X)  ∪ (↑C : set X)) :=
begin
  ext x,
  split,
  {
    intro h,
    cases h with x' hx',
    cases hx' with hx'BC hx'x,
    cases hx'BC,
    {
      left,
      use x',
      tauto,
    },
    {
      right,
      use x',
      tauto,
    }
  },
  {
    intro h,
    cases h,
    {
      cases h with x' hx',
      cases hx' with hx'B hx'x,
      use x',
      split,
      {
        left,
        exact hx'B,
      },
      {
        exact hx'x,
      },
    },
    {
      cases h with x' hx',
      cases hx' with hx'B hx'x,
      use x',
      split,
      {
        right,
        exact hx'B,
      },
      {
        exact hx'x,
      },
    },
  },
end

@[simp]
lemma union_familia_coe (F : set (set X)) : (↓(⋃₀ F) : set A)= ⋃₀ {(↓U : set A) | U ∈ F} :=
begin
  ext,
  split,
  {
    intro h,
    simp only [exists_prop, pert_inclusion_iff, baja_sube, mem_inter_iff, subtype.coe_prop, mem_sUnion, true_and] at *,
    cases h with U hU,
    cases hU with hUF hxU,
    use ↓U,
    simp only [true_and, subtype.coe_prop, baja_sube, set.mem_set_of_eq, set.mem_inter_iff],
    use U,
    simp [hUF],
    exact hxU,
  },
  {
    intro h,
    cases h with U hU,
    simp at hU,
    cases hU with hU hxU,
    simp,
    cases hU with V hV,
    cases hV with hVF hVU,
    use V,
    split, assumption,
    rw ← hVU at hxU,
    simp at hxU,
    exact hxU,
  }
  
end

@[simp]
lemma inter_coe (B C : set X) : ((↓(B ∩ C)) : set A) = ((↓B : set A) ∩ (↓C : set A) ) :=
begin
  ext,
  simp only [pert_inclusion_iff, baja_sube, mem_inter_iff, subtype.coe_prop, true_and],
end

@[simp]
lemma inter_sube (B C : set A) : ↑(B ∩  C) = ((↑B : set X)  ∩  (↑C : set X)) :=
begin
  ext x,
  split,
  {
    intro hx,
    cases hx with x' hx',
    cases hx' with hx'BC hx'x,
    cases hx'BC with hx'B hx'C,
    rw  ← hx'x,
    split,
    repeat {
      use x',
      tauto,
    },
  },
  {
    intro hx,
    cases hx with hxB hxC,
    cases hxB with x1 hx1,
    cases hx1 with hx1B hx1x,
    cases hxC with x2 hx2,
    cases hx2 with hx2C hx2x,
    use x1,
    split,
    split,
    {
      exact hx1B,
    },
    {
      simp,
      rw hx1x,
      rw ← hx2x,
      simp at hx2C,
      exact hx2C,
    },
    exact hx1x,
  },
end 


instance topologia_inducida {X : Type} [espacio_topologico X] (A : set X)  : espacio_topologico A := 
{ abiertos := {(↓U)  | U ∈ (abiertos : set (set X))},
  abierto_total := 
  begin
    use univ,
    split,  exact abierto_total,
    ext,
    simp only [mem_univ, iff_true],
  end,
  abierto_vacio := 
  begin
    use ∅,
    split, exact abierto_vacio,
    ext,
    simp only [pert_restringe_iff, mem_empty_iff_false],
  end,
  abierto_union := 
  begin
    intros F hF,
    simp at *,
    use ⋃₀ {U : set X | abierto U ∧ ((↓U) : set A) ∈ F},
    simp,
    split,
    {
      apply abierto_union,
      intros U hU,
      exact hU.1,
    },
    {
      ext x,
      split,
      {
        intro hx,
        cases hx with U hU,
        cases hU with hUF hxU,
        cases hUF with V hV,
        cases hV with hV hVU,
        cases hV with hVab hVF,
        use ↓V,
        split, exact hVF,
        rw hVU,
        exact hxU,
      },
      {
        intro hx,
        cases hx with U hU,
        cases hU with hUF hxU,
        specialize hF hUF,
        cases hF with V hV,
        cases hV with hVab hVU,
        use ↓V,
        split,
        use V,
        {
          simp [hVab, hVU, hUF],
        },
        {
          rw hVU,
          exact hxU,
        },
      },
    },
  end,
  abierto_interseccion := 
  begin
    intros U V hU hV,
    simp at *,
    cases hU with UX hUX,
    cases hUX with hUXab hUXU,
    cases hV with VX hVX,
    cases hVX with hVXab hVXV,
    use UX ∩ VX,
    split,
    {
      apply abierto_interseccion,
      assumption,
      assumption,
    },
    {
      simp,
      rw hUXU,
      rw hVXV,
    },
  end,
  }


def  TA (A : set X)  := topologia_inducida A


@[simp]
lemma abierto_inducido_sii (C : set A) : abierto C ↔ ∃ U  ∈ (abiertos : set (set X)),   (↓U : set A) = C:=
begin 
  refl,
end

@[simp]
lemma inducido_compl (U : set X) : ((↓U) : set A)ᶜ = ↓(Uᶜ) :=
begin
  refl,
end


lemma cerrado_inducido_sii (C : set A) : cerrado C ↔ ∃ U  ∈ (cerrados : set (set X)),   (↓U : set A) = C :=
begin
  unfold cerrado,
  simp only [exists_prop, cerrados_def, abierto_def],
  split,
  {
    intro h,
    cases h with U hU,
    cases hU with hUab hUC,
    use Uᶜ,
    split,
    {
      simp [hUab],
    },
    {
      rw [← inducido_compl],
      simp only [hUC, compl_compl],
    }
  },
  {
    simp,
    intros U hUab hUC,
    use Uᶜ,
    --rw restringe_coe,
    simp,
    split,
    {
      exact hUab,
    },
    {
      rw ← hUC,
      refl,
    },
  }
end

def ι : A → X := λ x, x.val



lemma inclusion_continua : continua (ι : A → X ) :=
begin
  intros U hU, 
  use U,
  simp [hU],
  refl,
end

def extiende (X : Type)  (A : set X) : set A →  set X := coe




example (X : Type) [TX : espacio_topologico X] (A : set X) (B : set A) : extiende X A  '' ((extiende ↥A B) '' (@abiertos ↥B (topologia_inducida B))) = (extiende X B) ''  @abiertos (B : set X) (topologia_inducida (B : set X)) :=
begin
  ext U,
  simp only [extiende, mem_image, exists_exists_and_eq_and],
  split,
  {
    intro h,
    cases h with UB hUB,
    cases hUB with hUBab hexUB,
    cases hUBab with UA hUA,
    cases hUA with hUAab hUAUB,
    cases hUAab with UX hUX,
    cases hUX with hUXab hUXUA,
    use ↓UX,
    split,
    {
      use UX,
      split,
      assumption,
      refl,
    },
    {
      simp only [extiende, ←hexUB, ←hUAUB, ←hUXUA, ←inter_assoc, baja_sube, inter_sube, sube_inter_A],
    }
  },
  {
    intro h,
    cases h with UAB hUAB,
    cases hUAB with hUABab hUABU,
    cases hUABab with UX hUXUAB,
    cases hUXUAB with hUXab hUXUAB,
    use ↓↓UX,
    split,
    {
      use ↓UX,
      simp only [eq_self_iff_true, exists_prop, and_true],
      use UX,
      simp only [eq_self_iff_true, exists_prop, and_true],
      exact hUXab,
    },
    {
      rw  ← hUABU,
      rw ← hUXUAB,
      simp[ ← inter_assoc],
    },
  },
end


def aplicacion_restriccion_imagen {X Y : Type} (f : X → Y ) (A : set Y) (hFA : range f ⊆ A ) : X → A :=
begin
  intro x,
  fconstructor,
  {
    exact f x,
  },
  {
    apply hFA,
    use x,
  }
end


notation f `|_` hFA  := aplicacion_restriccion_imagen f _ hFA 



lemma continua_restriccion_imagen (X Y : Type) [espacio_topologico X] [espacio_topologico Y]
      (A : set Y) (f : X → Y ) (hFA : range f ⊆ A )
      (hcont : continua (f |_  hFA) ) :
      continua f 
      :=
begin
  intros U hU,
  have haux : f ⁻¹' U = (f |_ hFA) ⁻¹' ↓U,
  {
    refl,
  },
  {
    rw haux,
    apply hcont,
    use U,
    simp,
    exact hU,
  },
end

lemma continua_a_trozos (X Y : Type) [espacio_topologico X] [espacio_topologico Y] (A B : set X) (f : X → Y)
(hAB : A ∪ B = univ ) (hA : abierto A) (hB : abierto B) (hfA : continua (f ∘ ι : A → Y)) (hfB : continua (f ∘ ι : B → Y)) :
continua f :=
begin
  sorry,
end

