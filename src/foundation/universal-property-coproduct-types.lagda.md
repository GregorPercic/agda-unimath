# The universal property of coproduct types

```agda
module foundation.universal-property-coproduct-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.equivalences
open import foundation-core.function-extensionality
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.precomposition-functions
```

</details>

## Idea

The universal property and dependent universal property of coproduct types
characterize maps and dependent functions out of coproduct types.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  ev-inl-inr :
    {l3 : Level} (P : A + B → UU l3) →
    ((t : A + B) → P t) → ((x : A) → P (inl x)) × ((y : B) → P (inr y))
  pr1 (ev-inl-inr P s) x = s (inl x)
  pr2 (ev-inl-inr P s) y = s (inr y)

  dependent-universal-property-coprod :
    {l3 : Level} (P : A + B → UU l3) → is-equiv (ev-inl-inr P)
  dependent-universal-property-coprod P =
    is-equiv-is-invertible
      ( λ p → ind-coprod P (pr1 p) (pr2 p))
      ( ind-Σ (λ f g → eq-pair refl refl))
      ( λ s → eq-htpy (ind-coprod _ refl-htpy refl-htpy))

  equiv-dependent-universal-property-coprod :
    {l3 : Level} (P : A + B → UU l3) →
    ((x : A + B) → P x) ≃ (((a : A) → P (inl a)) × ((b : B) → P (inr b)))
  pr1 (equiv-dependent-universal-property-coprod P) = ev-inl-inr P
  pr2 (equiv-dependent-universal-property-coprod P) =
    dependent-universal-property-coprod P

  abstract
    universal-property-coprod :
      {l3 : Level} (X : UU l3) → is-equiv (ev-inl-inr (λ _ → X))
    universal-property-coprod X = dependent-universal-property-coprod (λ _ → X)

  equiv-universal-property-coprod :
    {l3 : Level} (X : UU l3) → (A + B → X) ≃ ((A → X) × (B → X))
  equiv-universal-property-coprod X =
    equiv-dependent-universal-property-coprod (λ _ → X)

  abstract
    uniqueness-coprod :
      {l3 : Level} {Y : UU l3} (i : A → Y) (j : B → Y) →
      ( {l : Level} (X : UU l) →
        is-equiv (λ (s : Y → X) → pair' (s ∘ i) (s ∘ j))) →
      is-equiv (rec-coprod i j)
    uniqueness-coprod i j H =
      is-equiv-is-equiv-precomp
        ( rec-coprod i j)
        ( λ X →
          is-equiv-right-factor
            ( ev-inl-inr (λ _ → X))
            ( precomp (rec-coprod i j) X)
            ( universal-property-coprod X)
            ( H X))

  abstract
    universal-property-coprod-is-equiv-rec-coprod :
      {l3 : Level} (X : UU l3) (i : A → X) (j : B → X) →
      is-equiv (rec-coprod i j) →
      (l4 : Level) (Y : UU l4) →
      is-equiv (λ (s : X → Y) → pair' (s ∘ i) (s ∘ j))
    universal-property-coprod-is-equiv-rec-coprod X i j H l Y =
      is-equiv-comp
        ( ev-inl-inr (λ _ → Y))
        ( precomp (rec-coprod i j) Y)
        ( is-equiv-precomp-is-equiv
          ( rec-coprod i j)
          ( H)
          ( Y))
        ( universal-property-coprod Y)
```
