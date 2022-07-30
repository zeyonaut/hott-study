{-# OPTIONS --without-K --exact-split --safe #-}

module SS2022.WS2 where

open import SS2022.Prelude

private variable i j k : Level

-- Q3

lt : ℕ → ℕ → 𝟚
lt nil nil = 𝟎
lt nil (suc y) = 𝟏
lt (suc x) y = 𝟎

-- Q4

choice : {A : Type i} {B : Type j} {F : A → B → Type k}
       → (Σ \(b : B) → (a : A) → F a b) → ((a : A) → Σ \(b : B) → F a b)
choice (b , e) a = b , e a

-- Q5

taut₀ : ¬ (¬ 𝟙)
taut₀ f = f ⋆

taut₁ : {P : Type i} → ¬ (P × (¬ P))
taut₁ (b , e) = e b

taut₂ : {P : Type i} → ¬ (P ↔ (¬ P))
taut₂ (b , e) = b (e (\ p → b p p)) (e (\ p → b p p))