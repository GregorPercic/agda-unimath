# Morphisms of finite species

```agda
module species.morphisms-finite-species where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import species.species-of-finite-types

open import univalent-combinatorics.finite-types
```

</details>

## Idea

A homomorphism between two finite species is a pointwise family of maps.

## Definitions

### The type of morphisms between finite species

```agda
hom-species-𝔽 :
  {l1 l2 l3 : Level} → species-𝔽 l1 l2 → species-𝔽 l1 l3 →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
hom-species-𝔽 {l1} F G = (X : 𝔽 l1) → type-𝔽 (F X) → type-𝔽 (G X)
```

### The identity morphisms of finite species

```agda
id-hom-species-𝔽 :
  {l1 l2 : Level} (F : species-𝔽 l1 l2) → hom-species-𝔽 F F
id-hom-species-𝔽 F = λ X x → x
```

### Composition of morphisms of finite species

```agda
comp-hom-species-𝔽 :
  {l1 l2 l3 l4 : Level} (F : species-𝔽 l1 l2) (G : species-𝔽 l1 l3)
  (H : species-𝔽 l1 l4) → hom-species-𝔽 G H →
  hom-species-𝔽 F G → hom-species-𝔽 F H
comp-hom-species-𝔽 F G H f g X = (f X) ∘ (g X)
```

### Homotopies of morphisms of finite species

```agda
htpy-hom-species-𝔽 :
  {l1 l2 l3 : Level} (F : species-𝔽 l1 l2) (G : species-𝔽 l1 l3) →
  (hom-species-𝔽 F G) → (hom-species-𝔽 F G) →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
htpy-hom-species-𝔽 {l1} F G f g = (X : 𝔽 l1) → (f X) ~ (g X)

refl-htpy-hom-species-𝔽 :
  {l1 l2 l3 : Level} (F : species-𝔽 l1 l2) (G : species-𝔽 l1 l3) →
  (f : hom-species-𝔽 F G) → htpy-hom-species-𝔽 F G f f
refl-htpy-hom-species-𝔽 F G f X = refl-htpy
```

## Properties

### Associativity of composition of homomorphisms of finite species

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (F : species-𝔽 l1 l2) (G : species-𝔽 l1 l3)
  (H : species-𝔽 l1 l4) (K : species-𝔽 l1 l5)
  where

  associative-comp-hom-species-𝔽 :
    (h : hom-species-𝔽 H K) (g : hom-species-𝔽 G H) (f : hom-species-𝔽 F G) →
    comp-hom-species-𝔽 F G K (comp-hom-species-𝔽 G H K h g) f ＝
    comp-hom-species-𝔽 F H K h (comp-hom-species-𝔽 F G H g f)
  associative-comp-hom-species-𝔽 h g f = refl

  inv-associative-comp-hom-species-𝔽 :
    (h : hom-species-𝔽 H K) (g : hom-species-𝔽 G H) (f : hom-species-𝔽 F G) →
    comp-hom-species-𝔽 F H K h (comp-hom-species-𝔽 F G H g f) ＝
    comp-hom-species-𝔽 F G K (comp-hom-species-𝔽 G H K h g) f
  inv-associative-comp-hom-species-𝔽 h g f = refl
```

### The unit laws for composition of homomorphisms of finite species

```agda
left-unit-law-comp-hom-species-𝔽 :
  {l1 l2 l3 : Level} (F : species-𝔽 l1 l2) (G : species-𝔽 l1 l3)
  (f : hom-species-𝔽 F G) →
  Id (comp-hom-species-𝔽 F G G (id-hom-species-𝔽 G) f) f
left-unit-law-comp-hom-species-𝔽 F G f = refl

right-unit-law-comp-hom-species-𝔽 :
  {l1 l2 l3 : Level} (F : species-𝔽 l1 l2) (G : species-𝔽 l1 l3)
  (f : hom-species-𝔽 F G) →
  Id (comp-hom-species-𝔽 F F G f (id-hom-species-𝔽 F)) f
right-unit-law-comp-hom-species-𝔽 F G f = refl
```

### Characterization of the identity type of homomorphisms of finite species

```agda
htpy-eq-hom-species-𝔽 :
  {l1 l2 l3 : Level} (F : species-𝔽 l1 l2) (G : species-𝔽 l1 l3)
  (f g : hom-species-𝔽 F G) →
  Id f g → htpy-hom-species-𝔽 F G f g
htpy-eq-hom-species-𝔽 F G f g refl X y = refl

is-torsorial-htpy-hom-species-𝔽 :
  {l1 l2 l3 : Level} (F : species-𝔽 l1 l2) (G : species-𝔽 l1 l3)
  (f : hom-species-𝔽 F G) → is-torsorial (htpy-hom-species-𝔽 F G f)
is-torsorial-htpy-hom-species-𝔽 F G f =
  is-torsorial-Eq-Π (λ X → is-torsorial-htpy (f X))

is-equiv-htpy-eq-hom-species-𝔽 :
  {l1 l2 l3 : Level} (F : species-𝔽 l1 l2) (G : species-𝔽 l1 l3)
  (f g : hom-species-𝔽 F G) →
    is-equiv (htpy-eq-hom-species-𝔽 F G f g)
is-equiv-htpy-eq-hom-species-𝔽 F G f =
  fundamental-theorem-id
    ( is-torsorial-htpy-hom-species-𝔽 F G f)
    ( λ g → htpy-eq-hom-species-𝔽 F G f g)

extensionality-hom-species-𝔽 :
  {l1 l2 l3 : Level} (F : species-𝔽 l1 l2) (G : species-𝔽 l1 l3)
  (f g : hom-species-𝔽 F G) →
  Id f g ≃ htpy-hom-species-𝔽 F G f g
pr1 (extensionality-hom-species-𝔽 F G f g) =
  htpy-eq-hom-species-𝔽 F G f g
pr2 (extensionality-hom-species-𝔽 F G f g) =
  is-equiv-htpy-eq-hom-species-𝔽 F G f g
```

### The type of homomorphisms of finite species is a set

```agda
is-set-hom-species-𝔽 :
  {l1 l2 l3 : Level} (F : species-𝔽 l1 l2) (G : species-𝔽 l1 l3) →
  is-set (hom-species-𝔽 F G)
is-set-hom-species-𝔽 F G f g =
  is-prop-equiv
    ( extensionality-hom-species-𝔽 F G f g)
    ( is-prop-Π
      ( λ X →
        is-prop-Π
          ( λ x p q →
            is-set-is-finite (is-finite-type-𝔽 (G X)) (f X x) (g X x) p q)))

hom-set-species-𝔽 :
  {l1 l2 l3 : Level} (F : species-𝔽 l1 l2) (G : species-𝔽 l1 l3) →
  Set (lsuc l1 ⊔ l2 ⊔ l3)
pr1 (hom-set-species-𝔽 F G) = hom-species-𝔽 F G
pr2 (hom-set-species-𝔽 F G) = is-set-hom-species-𝔽 F G
```
