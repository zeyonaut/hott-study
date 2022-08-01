{-# OPTIONS --without-K --exact-split --safe #-}

module SS2022.WS6 where

open import SS2022.Prelude

private variable i j k ℓ : Level

-- Q1

𝟘-isNoncontr : ¬ (isContr 𝟘)
𝟘-isNoncontr = πb

-- Q2

Eq-ℕ : ℕ → ℕ → Type
Eq-ℕ nil nil = 𝟙
Eq-ℕ nil (suc b) = 𝟘
Eq-ℕ (suc a) nil = 𝟘
Eq-ℕ (suc a) (suc b) = Eq-ℕ a b

obs-ap-suc : {a b : ℕ} → Eq-ℕ a b → Eq-ℕ (suc a) (suc b)
obs-ap-suc {nil} {nil} ⋆ = ⋆
obs-ap-suc {suc a} {suc b} p = obs-ap-suc {a} {b} p

ℕ-sr : (n : ℕ) → Eq-ℕ n (suc n) ≡ 𝟘
ℕ-sr nil = ref 𝟘
ℕ-sr (suc n) = ℕ-sr n

path-to-obs-ℕ : (a b : ℕ) → a ≡ b → Eq-ℕ a b
path-to-obs-ℕ _ _ (ref nil) = ⋆
path-to-obs-ℕ _ _ (ref (suc a)) = path-to-obs-ℕ _ _ (ref a)

obs-to-path-ℕ : (a b : ℕ) → Eq-ℕ a b → a ≡ b
obs-to-path-ℕ nil nil ⋆ = ref nil
obs-to-path-ℕ (suc a) (suc b) p = ap suc (obs-to-path-ℕ _ _ p)

lemma : (m n : ℕ) → Eq-ℕ m n ≃ (m ≡ n)
lemma a b = obs-to-path-ℕ a b , (path-to-obs-ℕ a b , f a b) , (path-to-obs-ℕ a b , g a b) where
  f : (x y : ℕ) → path-to-obs-ℕ x y ▹ obs-to-path-ℕ x y ∼ id
  f nil nil (ref nil) = ref (ref nil)
  f (suc x) (suc x) (ref (suc x)) = ap (ap suc) (f x x (ref x))
  
  suc-path-to-obs : (a b : ℕ) (p : a ≡ b) → path-to-obs-ℕ (suc a) (suc b) (ap suc p) ≡ path-to-obs-ℕ a b p
  suc-path-to-obs _ _ (ref x) = ref _

  g : (x y : ℕ) → obs-to-path-ℕ x y ▹ path-to-obs-ℕ x y ∼ id
  g nil nil ⋆ = ref ⋆
  g (suc x) (suc y) a = suc-path-to-obs x y (obs-to-path-ℕ x y a) ∙ g x y a
  
ℕ-isNoncontr : ¬ (isContr ℕ)
ℕ-isNoncontr (a , f) = tr id (ℕ-sr a) (πb (πb (πf (lemma a (suc a)))) (f (suc a)))

-- Q3

contr-types-have-contr-path-types : {A : Type i} → isContr A → (x y : A) → isContr (x ≡ y)
contr-types-have-contr-path-types (center , contraction) x y = (! (contraction x) ∙ contraction y) , \{(ref a) → !-linv (contraction a)}

-- Q4

obs : {S : Type i} {T : Type j} (f : S → T) {x x' : S} (p : x ≡ x') {t : T} (q : f x ≡ t)
    → tr (\s → f s ≡ t) p q ≡ ! (ap f p) ∙ q
obs f (ref s) q = ! (∙-lunit _)

is-hae : {S : Type i} {T : Type j} (f : S → T) → Type (lmax i j)
is-hae f = Σ \g → Σ \((gs , gr) : ((g ▹ f ∼ id) × (f ▹ g ∼ id))) → (f ▹∼ gs) ∼ (gr ∼▹ f)

is-qinv : {S : Type i} {T : Type j} (f : S → T) → Type (lmax i j)
is-qinv f = Σ \f⁻¹ → ((f⁻¹ ▹ f ∼ id) × (f ▹ f⁻¹ ∼ id))

nat-htpy : {S : Type i} {T : Type j} {f g : S → T} (H : f ∼ g) {x y : S} (p : x ≡ y) → ap f p ∙ H y ≡ H x ∙ ap g p
nat-htpy H (ref x) = ∙-lunit _ ∙ ! (∙-runit _)

ap-id : {S : Type i} {T : Type j} {x y : S} (p : x ≡ y) → ap id p ≡ p
ap-id (ref x) = ref (ref x)

equiv→qinv : {S : Type i} {T : Type j} {f : S → T} → is-equiv f → is-qinv f
equiv→qinv {f = f} ((s , ps) , (r , pr)) = s , (ps , (((f ▹ s) ▹∼ !∼ pr) ∙∼ (f ▹∼ ps ∼▹ r) ∙∼ pr))

qinv→hae : {S : Type i} {T : Type j} {f : S → T} → is-qinv f → is-hae f
πb (qinv→hae (g , _)) = g
πb (πf (qinv→hae {f = f} (g , ps , pr))) = (\x → ! (ps (f (g x))) ∙ ap f (pr (g x)) ∙ ps x) , pr
πf (πf (qinv→hae {T = T} {f = f} (g , ps , pr))) = \x →
  ap (\z → ! (ps (f (g (f x)))) ∙
  ap f z ∙ ps (f x)) (! (∙-rcancel (pr x) (nat-htpy pr (pr x) ∙ ap (\y → pr (g (f x)) ∙ y) (ap-id {T = T} (pr x))))) ∙
  ap (\z → ! (ps (f (g (f x)))) ∙ z ∙ ps (f x)) (! (ap-▹ (f ▹ g) f (pr x))) ∙
  ap (\z → ! (ps (f (g (f x)))) ∙ z) (nat-htpy (f ▹∼ ps) (pr x)) ∙
  ∙-assoc _ _ _ ∙
  ap (\z → z ∙ ap f (pr x)) (!-linv _) ∙
  ∙-lunit _

hae→contr : {S : Type i} {T : Type j} {f : S → T} → is-hae f → Π ((fib f) ▹ isContr)
hae→contr {f = f} (g , ((gs , gr) , c)) t =
  (g t , gs t) ,
  \{(s , ref .(f s)) → ≡ₛ→≡ (gr s , (obs f (gr s) (gs (f s))) ∙
                                    ap (\x → ! x ∙ gs (f s)) (! (c s)) ∙
                                    !-linv (gs (f s)))}

-- The base projection of a fibration is an equivalence exactly if each of its fibers is contractible.
q4 : {B : Type i} {F : B → Type j} → is-equiv (πb {F = F}) ↔ Π (F ▹ isContr)
πb (q4 {F = F}) ie b with (equiv→qinv ▹ qinv→hae ▹ hae→contr) ie b
... | ((b' , e') , b'≡b) , f = tr F b'≡b e' , g where
  g : (b₁ : F b) → tr F b'≡b e' ≡ b₁
  g e with ≡→≡ₛ (f ((b , e), ref _))
  ... | ref _ , p = ap (\z → tr F z e) p
πb (πf q4 ic) = (\ b → b , πb (ic b)) , ref
πf (πf q4 ic) = (\ b → b , πb (ic b)) , (\x → ≡ₛ→≡ (ref (πb x) , πf (ic (πb x)) (πf x)))

-- Now, we show that the following is an equivalence:
map4 : {B : Type i} {F : B → Type j} {b : B} → fib (πb {F = F}) b → F b
map4 {F = F} ((b' , e') , p) = tr F p e'

map4-is-equiv : {B : Type i} (F : B → Type j) (b : B) → is-equiv (map4 {F = F} {b = b})
πb (map4-is-equiv F b) = (\e → (b , e) , ref b) , ref
πf (map4-is-equiv F b) = (\e → (b , e) , ref b) , \{((b' , e') , ref b') → ref _}

-- Q5

q5 : {A : Type i} {B : Type j} (f : A → B) → Σ \(e : A → Σ (fib f)) → (is-equiv e) × (f ∼ (e ▹ πb))
πb (q5 f) a = f a , (a , ref (f a))
πb (πb (πf (q5 {B = B} f))) = (\x → πb (πf x)) , \{(.(f a) , a , ref .(f a)) → ref (f a , a , ref (f a))}
πf (πb (πf (q5 {B = B} f))) = (\x → πb (πf x)) , \x → ref x
πf (πf (q5 f)) = \x → ref (f x)
