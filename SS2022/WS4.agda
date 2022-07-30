{-# OPTIONS --without-K --exact-split --safe #-}

module SS2022.WS4 where

open import SS2022.Prelude

private variable i j k : Level

-- Q1

data Fin : (n : ℕ) → Type where
  nil : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} → Fin n → Fin (suc n)

a b c : Fin 3
a = nil
b = suc (nil)
c = suc (suc (nil))

-- Q2

Fin' : ℕ → Type
Fin' nil = 𝟘
Fin' (suc z) = 𝟙 + Fin' z

Fin'-elim : (F : (n : ℕ) → Fin' n → Type i) → ((n : ℕ) → F (suc n) (il ⋆)) → ((n : ℕ) → (e : Fin' n) → F (suc n) (ir e)) → (n : ℕ) → (e : Fin' n) → F n e
Fin'-elim F z s (suc n) (il ⋆) = z n
Fin'-elim F z s (suc n) (ir x) = s n x

-- Q3

ι : {n : ℕ} → Fin n → ℕ
ι nil = 0
ι (suc e) = suc (ι e)

ι' : {n : ℕ} → Fin n → ℕ
ι' {suc n} nil = n
ι' {suc n} (suc e) = ι' e

-- Q4

_≤_ : ℕ → ℕ → Type
nil ≤ nil = 𝟙
nil ≤ suc b = 𝟙
suc a ≤ nil = 𝟘
suc a ≤ suc b = a ≤ b

-- Q5

add : ℕ → ℕ → ℕ
add nil nil = nil
add nil (suc b) = suc b
add (suc a) nil = suc a
add (suc a) (suc b) = suc (add a b)

mul : ℕ → ℕ → ℕ
mul nil nil = nil
mul nil (suc b) = nil
mul (suc a) nil = nil
mul (suc a) (suc b) = suc (add (mul a b) (add a b))

div : ℕ → ℕ → Type
div a b = Σ \(n : ℕ) → mul n a ≡ b

is-noncomp : ℕ → Type
is-noncomp p = (n : ℕ) → (div n p) → (n ≡ 1) + (n ≡ p)

twin-prime-conj : Type
twin-prime-conj = (n : ℕ) → Σ \(p : ℕ) → (n ≤ p) × ((is-noncomp p) × (is-noncomp (add p 2)))

-- Goldbach's original conjecture, not the modern, stronger one.
goldbach-conj : Type
goldbach-conj = (n : ℕ) → Σ \((p , q) : ℕ × ℕ) → (add (suc n) (suc n) ≡ add p q) × ((is-noncomp p) × (is-noncomp q))

-- Q7

module _ (least-noncomp-above : (n : ℕ) → Σ \(p : ℕ) → (is-noncomp p) × ((suc n) ≤ p)) where
  noncomp : ℕ → ℕ
  noncomp nil = 1
  noncomp (suc n) = πb (least-noncomp-above (noncomp n))

-- Q8

is-decidable : Type i → Type i
is-decidable A = A + (¬ A)

-- Q9

-- Yes, I really did replace all the primes with noncomps just so I could have a shorter type definition in Q6.
-- ;)
module _ (is-decidable-is-noncomp : (n : ℕ) → is-decidable (is-noncomp n)) where
  -- Counts how many noncomposite numbers are strictly less than its input.
  noncomp-counting : ℕ → ℕ
  noncomp-counting nil = 0
  noncomp-counting (suc z) with is-decidable-is-noncomp z
  ... | il x = suc (noncomp-counting z)
  ... | ir x = noncomp-counting z
