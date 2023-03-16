
{-# OPTIONS --without-K #-}

-- the recursive universe Set_mf
-- defined internally in HoTT

open import Level using (suc ; _⊔_)
open import Relation.Binary

data N₀ {𝓁} : Set 𝓁 where

data N₁ {𝓁} : Set 𝓁 where
  ★ : N₁

data ℕ {𝓁} : Set 𝓁 where
  zero : ℕ {𝓁}
  succ : ℕ {𝓁} → ℕ

data List {𝓁} (A : Set 𝓁) : Set 𝓁 where
  ε   : List A
  _∷_ : List A → A → List A 

data _+_ {𝓁} (A B : Set 𝓁) : Set 𝓁 where
  inl : A → A + B
  inr : B → A + B

infix 4 _+_

data _≡_ {𝓁} {A : Set 𝓁} (x : A) : A → Set 𝓁 where
  refl : x ≡ x

transport : ∀ {𝓁 𝓁'} {A : Set 𝓁} {B : A → Set 𝓁'} {a a' : A}
            → a ≡ a' → B a → B a'
transport refl b = b

data Σ {𝓁 𝓁'} (A : Set 𝓁) (B : A → Set 𝓁') : Set (𝓁 ⊔ 𝓁') where
  _,_ : (a : A) → B a → Σ A B

-- the universe of small h-propositions
IsProp : ∀ {𝓁} → Set 𝓁 → Set 𝓁
IsProp A = (a b : A) → a ≡ b

IsSet : ∀ {𝓁} → Set 𝓁 → Set 𝓁
IsSet A = (a b : A) → IsProp (a ≡ b)

hProp : ∀ {𝓁} → Set (suc 𝓁)
hProp {𝓁} = Σ (Set 𝓁) λ A → IsProp A

-- propositional truncation
postulate
  ∥_∥                  : ∀ {𝓁} → Set 𝓁 → Set 𝓁
  ∥∥-is-subsingleton   : ∀ {𝓁} → {A : Set 𝓁} → IsProp (∥ A ∥)
  ∣_∣                 : ∀ {𝓁} → {A : Set 𝓁} → A → ∥ A ∥
  ∥∥-recursion         : ∀ {𝓁} → {A : Set 𝓁} {P : Set 𝓁}
                        → IsProp P → (A → P) → ∥ A ∥ → P
infix 0 ∥_∥

-- quotient type
record hEqRel {𝓁} 𝓁' (A : Set 𝓁) : Set (𝓁 ⊔ suc 𝓁') where
  field
    R        : A → A → Set 𝓁'
    is-equiv : IsEquivalence R
    is-prop  : ∀ x y → IsProp (R x y)

postulate
  _/_ : ∀ {𝓁 𝓁'} → (A : Set 𝓁) (R : hEqRel 𝓁' A) → Set (𝓁 ⊔ 𝓁')
  trunc : ∀ {𝓁 𝓁'} {A : Set 𝓁} {R : hEqRel 𝓁' A} → IsSet (A / R)
  [_] : ∀ {𝓁 𝓁'} {A : Set 𝓁} → A  → (R : hEqRel 𝓁' A) → A / R
  qeq : ∀ {𝓁 𝓁'} {A : Set 𝓁} {R : hEqRel 𝓁' A} {a b : A} → (hEqRel.R R) a b → [ a ] R ≡ [ b ] R
  qeff : ∀ {𝓁 𝓁'} {A : Set 𝓁} {R : hEqRel 𝓁' A} {a b : A} → [ a ] R ≡ [ b ] R → (hEqRel.R R) a b
  qelim : ∀ {𝓁 𝓁' 𝓁''} {A : Set 𝓁} {R : hEqRel 𝓁' A}
          → (P : A / R → Set 𝓁'')
          → (t : ∀ {a} → IsSet (P a))
          → (f : (a : A) → P ([ a ] R))
          → (p : (a b : A) → (r : (hEqRel.R R) a b) → transport {A = A / R} {P} (qeq r) (f a) ≡ f b)
          → (z : A / R) → P z
  qcomp : ∀ {𝓁 𝓁' 𝓁''} {A : Set 𝓁} {R : hEqRel 𝓁' A}
          → (P : A / R → Set 𝓁'')
          → (t : ∀ {a} → IsSet (P a))
          → (f : (a : A) → P ([ a ] R))
          → (p : (a b : A) → (r : (hEqRel.R R) a b) → transport (qeq r) (f a) ≡ f b)
          → (a : A) → qelim P t f p ([ a ] R) ≡ f a

-- a Tarsky inductive-recursive universe
-- closed under all the other constructors

data U : Set₁
T : U → Set₁

data U where
  ⌜hProp₀⌝ : U
  ⌜N₀⌝   : U
  ⌜N₁⌝   : U
  ⌜ℕ⌝    : U
  ⌜∥_∥⌝   : (A : U) → U
  ⌜List⌝ : (A : U) → U
  ⌜Q⌝    : (A : U) (R : T A → T A → U)
            → (IsEquivalence λ x y → T (R x y))
            → (∀ x y → IsProp (T (R x y)))
            → U
  _⌜+⌝_  : (A B : U) → U
  ⌜Σ⌝    : (A : U) (B : T A → U) → U
  ⌜Π⌝    : (A : U) (B : T A → U) → U

T ⌜hProp₀⌝     = hProp
T ⌜N₀⌝         = N₀
T ⌜N₁⌝         = N₁
T ⌜ℕ⌝          = ℕ
T ⌜∥ A ∥⌝       = ∥ T A ∥
T (⌜List⌝ A)   = List (T A)
T (⌜Q⌝ A R is-equiv is-prop) = T A / record
                                    { R = λ x y → T (R x y) 
                                    ; is-equiv = is-equiv
                                    ; is-prop = is-prop }
T (A ⌜+⌝ B)    = T A + T B
T (⌜Σ⌝ A B)    = Σ (T A) (λ a → T (B a))
T (⌜Π⌝ A B)    = (a : T A) → T (B a)