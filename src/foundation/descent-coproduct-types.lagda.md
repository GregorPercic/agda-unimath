# Descent for coproduct types

```agda
module foundation.descent-coproduct-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-fibers-of-maps
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.families-of-equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.pullbacks
```

</details>

## Theorem

```agda
module _
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A' → A) (g : B' → B) (h : X' → X)
  (αA : A → X) (αB : B → X) (αA' : A' → X') (αB' : B' → X')
  (HA : αA ∘ f ~ h ∘ αA') (HB : αB ∘ g ~ h ∘ αB')
  where

  triangle-descent-square-fiber-map-coprod-inl-fiber :
    (x : A) →
    ( map-fiber-vertical-map-cone αA h (f , αA' , HA) x) ~
    ( map-fiber-vertical-map-cone (ind-coprod _ αA αB) h
      ( map-coprod f g , ind-coprod _ αA' αB' , ind-coprod _ HA HB)
      ( inl x)) ∘
    ( fiber-map-coprod-inl-fiber f g x)
  triangle-descent-square-fiber-map-coprod-inl-fiber x (a' , p) =
    eq-pair-eq-pr2
      ( ap (concat (inv (HA a')) (αA x)) (ap-comp (ind-coprod _ αA αB) inl p))

  triangle-descent-square-fiber-map-coprod-inr-fiber :
    (y : B) →
    ( map-fiber-vertical-map-cone αB h (g , αB' , HB) y) ~
    ( map-fiber-vertical-map-cone (ind-coprod _ αA αB) h
      ( map-coprod f g , ind-coprod _ αA' αB' , ind-coprod _ HA HB)
      ( inr y)) ∘
    ( fiber-map-coprod-inr-fiber f g y)
  triangle-descent-square-fiber-map-coprod-inr-fiber y (b' , p) =
    eq-pair-eq-pr2
      ( ap (concat (inv (HB b')) (αB y)) (ap-comp (ind-coprod _ αA αB) inr p))

module _
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A → X) (g : B → X) (i : X' → X)
  where

  cone-descent-coprod :
    (cone-A' : cone f i A') (cone-B' : cone g i B') →
    cone (ind-coprod _ f g) i (A' + B')
  pr1 (cone-descent-coprod (h , f' , H) (k , g' , K)) = map-coprod h k
  pr1 (pr2 (cone-descent-coprod (h , f' , H) (k , g' , K))) (inl a') = f' a'
  pr1 (pr2 (cone-descent-coprod (h , f' , H) (k , g' , K))) (inr b') = g' b'
  pr2 (pr2 (cone-descent-coprod (h , f' , H) (k , g' , K))) (inl a') = H a'
  pr2 (pr2 (cone-descent-coprod (h , f' , H) (k , g' , K))) (inr b') = K b'

  abstract
    descent-coprod :
      (cone-A' : cone f i A') (cone-B' : cone g i B') →
      is-pullback f i cone-A' →
      is-pullback g i cone-B' →
      is-pullback (ind-coprod _ f g) i (cone-descent-coprod cone-A' cone-B')
    descent-coprod (h , f' , H) (k , g' , K) is-pb-cone-A' is-pb-cone-B' =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone
        ( ind-coprod _ f g)
        ( i)
        ( cone-descent-coprod (h , f' , H) (k , g' , K))
        ( α)
      where
      α :
        is-fiberwise-equiv
          ( map-fiber-vertical-map-cone
            ( ind-coprod (λ _ → X) f g)
            ( i)
            ( cone-descent-coprod (h , f' , H) (k , g' , K)))
      α (inl x) =
        is-equiv-right-map-triangle
          ( map-fiber-vertical-map-cone f i (h , f' , H) x)
          ( map-fiber-vertical-map-cone (ind-coprod _ f g) i
            ( cone-descent-coprod (h , f' , H) (k , g' , K))
            ( inl x))
          ( fiber-map-coprod-inl-fiber h k x)
          ( triangle-descent-square-fiber-map-coprod-inl-fiber
            h k i f g f' g' H K x)
          ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback f i
            ( h , f' , H) is-pb-cone-A' x)
          ( is-equiv-fiber-map-coprod-inl-fiber h k x)
      α (inr y) =
        is-equiv-right-map-triangle
          ( map-fiber-vertical-map-cone g i (k , g' , K) y)
          ( map-fiber-vertical-map-cone
            ( ind-coprod _ f g) i
            ( cone-descent-coprod (h , f' , H) (k , g' , K))
            ( inr y))
          ( fiber-map-coprod-inr-fiber h k y)
          ( triangle-descent-square-fiber-map-coprod-inr-fiber
            h k i f g f' g' H K y)
          ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback g i
            ( k , g' , K) is-pb-cone-B' y)
          ( is-equiv-fiber-map-coprod-inr-fiber h k y)

  abstract
    descent-coprod-inl :
      (cone-A' : cone f i A') (cone-B' : cone g i B') →
      is-pullback (ind-coprod _ f g) i (cone-descent-coprod cone-A' cone-B') →
      is-pullback f i cone-A'
    descent-coprod-inl (h , f' , H) (k , g' , K) is-pb-dsq =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone f i
        ( h , f' , H)
        ( λ a →
          is-equiv-left-map-triangle
          ( map-fiber-vertical-map-cone f i (h , f' , H) a)
          ( map-fiber-vertical-map-cone (ind-coprod _ f g) i
            ( cone-descent-coprod (h , f' , H) (k , g' , K))
            ( inl a))
          ( fiber-map-coprod-inl-fiber h k a)
          ( triangle-descent-square-fiber-map-coprod-inl-fiber
            h k i f g f' g' H K a)
          ( is-equiv-fiber-map-coprod-inl-fiber h k a)
          ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback
            ( ind-coprod _ f g)
            ( i)
            ( cone-descent-coprod ( h , f' , H) (k , g' , K))
            ( is-pb-dsq)
            ( inl a)))

  abstract
    descent-coprod-inr :
      (cone-A' : cone f i A') (cone-B' : cone g i B') →
      is-pullback (ind-coprod _ f g) i (cone-descent-coprod cone-A' cone-B') →
      is-pullback g i cone-B'
    descent-coprod-inr (h , f' , H) (k , g' , K) is-pb-dsq =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone g i
        ( k , g' , K)
        ( λ b →
          is-equiv-left-map-triangle
          ( map-fiber-vertical-map-cone g i (k , g' , K) b)
          ( map-fiber-vertical-map-cone (ind-coprod _ f g) i
            ( cone-descent-coprod (h , f' , H) (k , g' , K))
            ( inr b))
          ( fiber-map-coprod-inr-fiber h k b)
          ( triangle-descent-square-fiber-map-coprod-inr-fiber
            h k i f g f' g' H K b)
          ( is-equiv-fiber-map-coprod-inr-fiber h k b)
          ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback
            ( ind-coprod _ f g)
            ( i)
            ( cone-descent-coprod (h , f' , H) (k , g' , K))
            ( is-pb-dsq)
            ( inr b)))
```
