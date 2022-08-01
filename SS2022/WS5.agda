{-# OPTIONS --without-K --exact-split --safe #-}

module SS2022.WS5 where

open import SS2022.Prelude

private variable i j k ℓ : Level

-- Q1

-- Any retraction induces injectivity:
retr-to-inj : {A : Type i} {B : Type j} {f : A → B} → retr f → inj f
retr-to-inj (f⁻¹ , e) {x} {y} p = ! (e x) ∙ (ap f⁻¹ p) ∙ e y

-- Q2

-- Behold: a commutative triangle!
module com {A : Type i} {B : Type j} {X : Type k} (f : A → X) (g : B → X) (h : A → B) (k : f ∼ h ▹ g) where 
  p1-a : ((sh , _) : sect h) → sh ▹ f ∼ g
  p1-a (sh , ph) = (sh ▹∼ k) ∙∼ (ph ∼▹ g)
  
  p1-b : sect h → sect f → sect g
  p1-b (sh , _) (sf , pf) = sf ▹ h , (sf ▹∼ (!∼ k)) ∙∼ pf
  
  p1-c : sect h → sect g → sect f
  p1-c (sh , ph) (sg , pg) = sg ▹ sh , ((sg ▹ sh) ▹∼ k) ∙∼ (sg ▹∼ ph ∼▹ g) ∙∼ pg

  p2-a : ((rg , _) : retr g) → f ▹ rg ∼ h
  p2-a (rg , pg) = (k ∼▹ rg) ∙∼ (h ▹∼ pg)

  p2-b : retr g → retr f → retr h
  p2-b (rg , pg) (rf , pf) = g ▹ rf , (!∼ k ∼▹ rf) ∙∼ pf

  p2-c : retr g → retr h → retr f
  p2-c (rg , pg) (rh , ph) = rg ▹ rh , (k ∼▹ (rg ▹ rh)) ∙∼ (h ▹∼ pg ∼▹ rh) ∙∼ ph

  p3-a : is-equiv f → is-equiv g → is-equiv h
  p3-a ((sf , psf) , (rf , prf)) ((sg , psg) , (rg , prg)) =
    (g ▹ sf , ((g ▹ sf ▹ h) ▹∼ !∼ prg) ∙∼
              ((g ▹ sf) ▹∼ !∼ k ∼▹ rg) ∙∼
              (g ▹∼ psf ∼▹ rg) ∙∼
              prg) ,
    (g ▹ rf , (!∼ k ∼▹ rf) ∙∼
               prf)

  p3-b : is-equiv g → is-equiv h → is-equiv f
  p3-b ((sg , psg) , (rg , prg)) ((sh , psh) , (rh , prh)) =
    (sg ▹ sh , ((sg ▹ sh) ▹∼ k) ∙∼
               (sg ▹∼ psh ∼▹ g) ∙∼
               psg) ,
    (rg ▹ rh , (k ∼▹ (rg ▹ rh)) ∙∼
               (h ▹∼ prg ∼▹ rh) ∙∼
               prh)

  p3-c : is-equiv h → is-equiv f → is-equiv g
  p3-c ((sh , psh) , (rh , prh)) ((sf , psf) , (rf , prf)) =
    (sf ▹ h , (sf ▹∼ !∼ k) ∙∼
              psf) ,
    (rf ▹ h , (!∼ psh ∼▹ (g ▹ rf ▹ h)) ∙∼
               (sh ▹∼ (!∼ k) ∼▹ (rf ▹ h)) ∙∼
               (sh ▹∼ prf ∼▹ h) ∙∼
               psh)

id-is-equiv : {A : Type i} → is-equiv (id {_} {A})
id-is-equiv = (id , ref) , (id , ref)

-- Any retraction/section of an equivalence is also an equivalence.

retr-equiv : {A : Type i} {B : Type j} (f : A → B) → is-equiv f → ((r , _) : retr f) → is-equiv r
retr-equiv f ief (r , pr) = com.p3-c id r f (!∼ pr) ief id-is-equiv

sect-equiv : {A : Type i} {B : Type j} (f : A → B) → is-equiv f → ((s , _) : sect f) → is-equiv s
sect-equiv f ief (s , ps) = com.p3-a id f s (!∼ ps) id-is-equiv ief

-- Q3

Eq-𝟚 : 𝟚 → 𝟚 → Type
Eq-𝟚 𝟎 𝟎 = 𝟙
Eq-𝟚 𝟎 𝟏 = 𝟘
Eq-𝟚 𝟏 𝟎 = 𝟘
Eq-𝟚 𝟏 𝟏 = 𝟙

φ : {a b : 𝟚} → (a ≡ b) → Eq-𝟚 a b
φ (ref 𝟎) = ⋆
φ (ref 𝟏) = ⋆

-- Proof by 'cheating' :P
φ-is-equiv : (a b : 𝟚) → is-equiv (φ {a} {b})
φ-is-equiv 𝟎 𝟎 = ((\{⋆ → ref 𝟎}) , (\{⋆ → ref ⋆})) , ((\{⋆ → ref 𝟎}) , (\{(ref 𝟎) → ref (ref 𝟎)}))
φ-is-equiv 𝟎 𝟏 = ((\()) , \a → 𝟘-elim' a) , ((\()) , \{()})
φ-is-equiv 𝟏 𝟎 = ((\()) , \a → 𝟘-elim' a) , ((\()) , \{()})
φ-is-equiv 𝟏 𝟏 = ((\{⋆ → ref 𝟏}) , (\{⋆ → ref ⋆})) , ((\{⋆ → ref 𝟏}) , (\{(ref 𝟏) → ref (ref 𝟏)}))

!₂ : 𝟚 → 𝟚
!₂ 𝟎 = 𝟏
!₂ 𝟏 = 𝟎

!₂-is-nontrivial : (b : 𝟚) → ¬ (b ≡ !₂ b)
!₂-is-nontrivial 𝟎 p = φ p
!₂-is-nontrivial 𝟏 p = φ p

-- Q4

const : {D : Type i} → {C : Type j} → C → D → C
const b _ = b

const-is-not-equiv-𝟚 : (b : 𝟚) → ¬ (is-equiv (const {D = 𝟚} b))
const-is-not-equiv-𝟚 b iec = φ (retr-to-inj (πf iec) {𝟎} {𝟏} (ref b))

𝟙-factoring : {A : Type i} (f : 𝟙 → A) (x : 𝟙) → f x ≡ f ⋆
𝟙-factoring f ⋆ = ref (f ⋆)

𝟚≄𝟙 : (f : 𝟚 → 𝟙) → ¬ (is-equiv f)
𝟚≄𝟙 f ief = φ (! (πf (πf ief) 𝟎) ∙ 𝟙-factoring (πb (πf ief)) _ ∙ ! (𝟙-factoring (πb (πf ief)) _) ∙ (πf (πf ief) 𝟏))

-- Q5

!⁻¹ : {A : Type i} {x y : A} → y ≡ x → x ≡ y
!⁻¹ (ref a) = ref a

tr⁻¹ : {B : Type i} (F : B → Type j) {x y : B} → x ≡ y → F y → F x
tr⁻¹ F (ref _) e = e

-- Q6

q6 : {A : Type i} {B : Type j} (f g : A → B) → f ∼ g → is-equiv f ↔ is-equiv g
πb (q6 f g H) ((sf , psf) , (rf , prf)) =
  (sf , (sf ▹∼ !∼ H) ∙∼ psf) ,
  (rf , (!∼ H ∼▹ rf) ∙∼ prf)
πf (q6 f g H) ((sg , psg) , (rg , prg)) =
  (sg , (sg ▹∼ H) ∙∼ psg) ,
  (rg , (H ∼▹ rg) ∙∼ prg)

-- Q7

-- Sections of homotopic equivalences are homotopic.
q7 : {A : Type i} {B : Type j} (e e' : A → B) (iee : is-equiv e) (iee' : is-equiv e') → e ∼ e' → πb (πb iee) ∼ πb (πb iee')
q7 e e' ((s , ps) , (r , pr)) ((s' , ps') , (r' , pr')) H =
  (s ▹∼ !∼ pr') ∙∼ (s ▹∼ !∼ H ∼▹ r') ∙∼ (ps ∼▹ r') ∙∼ (!∼ ps' ∼▹ r') ∙∼ (s' ▹∼ pr')
