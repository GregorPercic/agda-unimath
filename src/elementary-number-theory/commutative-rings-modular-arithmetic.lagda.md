# The commutative rings of modular arithmetic

```agda
module elementary-number-theory.commutative-rings-modular-arithmetic where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.groups-of-modular-arithmetic
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import ring-theory.rings
open import group-theory.endomorphism-rings-abelian-groups
open import group-theory.homomorphisms-abelian-groups
open import foundation.function-types
open import foundation.homotopies
```

</details>

## Idea

The integers modulo `n` form a
[commutative ring](commutative-algebra.commutative-rings.md).

## Definition

```agda
ℤ-Mod-Ring : (n : ℕ) → Ring lzero
pr1 (ℤ-Mod-Ring n) = ℤ-Mod-Ab n
pr1 (pr1 (pr2 (ℤ-Mod-Ring n))) = mul-ℤ-Mod n
pr2 (pr1 (pr2 (ℤ-Mod-Ring n))) = associative-mul-ℤ-Mod n
pr1 (pr1 (pr2 (pr2 (ℤ-Mod-Ring n)))) = one-ℤ-Mod n
pr1 (pr2 (pr1 (pr2 (pr2 (ℤ-Mod-Ring n))))) = left-unit-law-mul-ℤ-Mod n
pr2 (pr2 (pr1 (pr2 (pr2 (ℤ-Mod-Ring n))))) = right-unit-law-mul-ℤ-Mod n
pr1 (pr2 (pr2 (pr2 (ℤ-Mod-Ring n)))) = left-distributive-mul-add-ℤ-Mod n
pr2 (pr2 (pr2 (pr2 (ℤ-Mod-Ring n)))) = right-distributive-mul-add-ℤ-Mod n

ℤ-Mod-Commutative-Ring : (n : ℕ) → Commutative-Ring lzero
pr1 (ℤ-Mod-Commutative-Ring n) = ℤ-Mod-Ring n
pr2 (ℤ-Mod-Commutative-Ring n) = commutative-mul-ℤ-Mod n
```

## Properties

```agda
endomorphism-ring-ℤ-Mod : ℕ → Ring lzero
endomorphism-ring-ℤ-Mod n = endomorphism-ring-Ab (ℤ-Mod-Ab n)

ev-endomorphism-ring-ℤ-Mod :
  (n : ℕ) → type-Ring (endomorphism-ring-ℤ-Mod n) → ℤ-Mod n
ev-endomorphism-ring-ℤ-Mod n f =
  map-hom-Ab (ℤ-Mod-Ab n) (ℤ-Mod-Ab n) f (one-ℤ-Mod n)

inv-ev-endomorphism-ring-ℤ-Mod :
  (n : ℕ) → ℤ-Mod n → type-Ring (endomorphism-ring-ℤ-Mod n)
pr1 (inv-ev-endomorphism-ring-ℤ-Mod n x) = mul-ℤ-Mod n x
pr2 (inv-ev-endomorphism-ring-ℤ-Mod n x) y z = left-distributive-mul-add-ℤ-Mod n x y z

is-section-inv-ev-endomorphism-ring-ℤ-Mod :
  (n : ℕ) →
  (ev-endomorphism-ring-ℤ-Mod n ∘ inv-ev-endomorphism-ring-ℤ-Mod n) ~ id
is-section-inv-ev-endomorphism-ring-ℤ-Mod n x = right-unit-law-mul-ℤ-Mod n x

htpy-is-retraction-inv-ev-endomorphism-ring-ℤ-Mod :
  (n : ℕ) → (f : type-Ring (endomorphism-ring-ℤ-Mod n)) →
  htpy-hom-Ab
    ( ℤ-Mod-Ab n)
    ( (ℤ-Mod-Ab n))
    ( inv-ev-endomorphism-ring-ℤ-Mod n
      ( map-hom-Ab (ℤ-Mod-Ab n) (ℤ-Mod-Ab n) f (one-ℤ-Mod n)))
    ( f)
htpy-is-retraction-inv-ev-endomorphism-ring-ℤ-Mod n f y = {!   !}

is-retraction-inv-ev-endomorphism-ring-ℤ-Mod :
  (n : ℕ) →
  (inv-ev-endomorphism-ring-ℤ-Mod n ∘ ev-endomorphism-ring-ℤ-Mod n) ~ id
is-retraction-inv-ev-endomorphism-ring-ℤ-Mod n f = eq-htpy-hom-Ab (ℤ-Mod-Ab n) ((ℤ-Mod-Ab n)) (htpy-is-retraction-inv-ev-endomorphism-ring-ℤ-Mod n f)
```
