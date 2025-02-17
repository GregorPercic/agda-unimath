# Commuting triangles of maps

```agda
module foundation.commuting-triangles-of-maps where

open import foundation-core.commuting-triangles-of-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.functoriality-dependent-function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
```

</details>

## Idea

A triangle of maps

```text
 A ----> B
  \     /
   \   /
    V V
     X
```

is said to **commute** if there is a [homotopy](foundation-core.homotopies.md)
between the map on the left and the composite map.

## Properties

### Top map is an equivalence

If the top map is an [equivalence](foundation-core.equivalences.md), then there
is an equivalence between the coherence triangle with the map of the equivalence
as with the inverse map of the equivalence.

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (left : A → X) (right : B → X) (e : A ≃ B)
  where

  equiv-coherence-triangle-maps-inv-top :
    coherence-triangle-maps left right (map-equiv e) ≃
    coherence-triangle-maps right left (map-inv-equiv e)
  equiv-coherence-triangle-maps-inv-top =
    ( equiv-inv-htpy
      ( left ∘ (map-inv-equiv e))
      ( right)) ∘e
    ( equiv-Π
      ( λ b → left (map-inv-equiv e b) ＝ right b)
      ( e)
      ( λ a →
        equiv-concat
          ( ap left (is-retraction-map-inv-equiv e a))
          ( right (map-equiv e a))))

  coherence-triangle-maps-inv-top :
    coherence-triangle-maps left right (map-equiv e) →
    coherence-triangle-maps right left (map-inv-equiv e)
  coherence-triangle-maps-inv-top =
    map-equiv equiv-coherence-triangle-maps-inv-top
```

### Commuting triangles of maps induce commuting triangles of precomposition maps

Given a commuting triangle of maps

```text
       f
   A ----> B
    \  ⇗  /
   h \   / g
      V V
       X
```

there is an induced commuting triangle of
[precomposition maps](foundation-core.precomposition-functions.md)

```text
         (- ∘ g)
  (X → S) ----> (B → S)
        \   ⇗  /
  (- ∘ h) \   / (- ∘ f)
           V V
         (A → S).
```

Note the change of order of `f` and `g`.

```agda
module _
  { l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  ( left : A → X) (right : B → X) (top : A → B)
  where

  precomp-coherence-triangle-maps :
    coherence-triangle-maps left right top →
    (S : UU l4) →
    coherence-triangle-maps
      ( precomp left S)
      ( precomp top S)
      ( precomp right S)
  precomp-coherence-triangle-maps = htpy-precomp

  precomp-coherence-triangle-maps' :
    coherence-triangle-maps' left right top →
    (S : UU l4) →
    coherence-triangle-maps'
      ( precomp left S)
      ( precomp top S)
      ( precomp right S)
  precomp-coherence-triangle-maps' = htpy-precomp
```

### Commuting triangles of maps induce commuting triangles of postcomposition maps

Given a commuting triangle of maps

```text
       f
   A ----> B
    \  ⇗  /
   h \   / g
      V V
       X
```

there is an induced commuting triangle of
[postcomposition maps](foundation-core.postcomposition-functions.md)

```text
         (f ∘ -)
  (S → A) ----> (S → B)
        \   ⇗  /
  (h ∘ -) \   / (g ∘ -)
           V V
         (S → X).
```

```agda
module _
  { l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  ( left : A → X) (right : B → X) (top : A → B)
  where

  postcomp-coherence-triangle-maps :
    (S : UU l4) →
    coherence-triangle-maps left right top →
    coherence-triangle-maps
      ( postcomp S left)
      ( postcomp S right)
      ( postcomp S top)
  postcomp-coherence-triangle-maps S = htpy-postcomp S

  postcomp-coherence-triangle-maps' :
    (S : UU l4) →
    coherence-triangle-maps' left right top →
    coherence-triangle-maps'
      ( postcomp S left)
      ( postcomp S right)
      ( postcomp S top)
  postcomp-coherence-triangle-maps' S = htpy-postcomp S
```
