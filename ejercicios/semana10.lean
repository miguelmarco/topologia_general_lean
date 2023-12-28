import ..clausura
import ..interior
import tactic

open topologicos topologicos.espacio_topologico

variables (X Y : Type) [espacio_topologico X] [espacio_topologico Y]


/-
# Ejercicio 3.3.13
Sea f : X → Y una aplicación continua y abierta entre espacios
topológicos. Demuestra que si B ⊂ Y , entonces f ⁻¹ ( clausura B) = clausura (f ⁻¹(B))
-/
lemma ejer_3_3_13 (B : set Y) (f : X → Y) (hfab : abierta f) (hfcont : continua f) :
    f ⁻¹' (clausura B) = clausura (f ⁻¹' B) :=
begin
  sorry,
end

/-
# Ejercicio 3.3.17

Sea (X, TX ) e.t. y S subbase de X; demuestra que si A ⊂ X
es denso en X entonces A ∩ S ≠ ∅ ∀S ∈ S, S ≠ ∅.
-/
lemma ejer_3_3_17 (S : set (set X)) (hS : subbase S) (A : set X) (hA : denso A) :
  ∀ s ∈ S, s ≠ ∅ → A ∩ s ≠ ∅  :=
begin
  sorry,
end



/-
Ejercicio 3.3.20 Sea f : X → Y una aplicación entre dos espacios topológicos.
Demuestra que f es abierta si y sólo si f (Int A) ⊂ Int f (A).
-/
lemma ejer_3_3_20 (f : X → Y) : abierta f ↔ ∀ A , f '' (interior A) ⊆ interior (f '' A) :=
begin
  sorry,
end