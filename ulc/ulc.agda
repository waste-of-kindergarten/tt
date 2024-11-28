module ulc where 
open import Agda.Builtin.String 
open import Agda.Builtin.String.Properties
open import Agda.Builtin.List 
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Relation.Binary.PropositionalEquality as Eq 
open Eq using (_≡_; refl; trans; sym; cong)
open import Data.Sum using (_⊎_; inj₁; inj₂) 
open import Data.Product using (_×_; proj₁; proj₂; _,_ ; ∃; Σ-syntax; ∃-syntax)
open import Level using (Level) renaming (zero to lzero; suc to lsuc)
open import Data.Empty using (⊥)

postulate ≡lem : ∀ {A : Set} {a b : A} → (a ≡ b) ⊎ ¬ (a ≡ b) 

Variable : Set 
Variable = String

data Term : Set where
    var : Variable → Term
    app : Term → Term → Term 
    abst : Variable → Term → Term    

data _∈_ : ∀ {A : Set} → A → List A → Set₁ where 
    head : ∀ {A : Set} {a : A} {l : List A} → a ∈ (a ∷ l)
    next : ∀ {A : Set} {a b : A} {l : List A} → b ∈ l → b ∈ (a ∷ l) 

_∉_ : ∀ {A : Set} → A → List A → Set₁ 
a ∉ l = ¬ (a ∈ l)

¬a∈[] : ∀ {A : Set} → {a : A} → ¬ (a ∈ [])
¬a∈[] ()  

̸≡⟨⟩∉ : ∀ {A : Set} → {a b : A} {l : List A} → ¬ (a ≡ b) → ¬ (a ∈ l) → ¬ (a ∈ (b ∷ l))
̸≡⟨⟩∉ ¬a≡b ¬a∈l a∈b∷l with a∈b∷l
...             | head = ¬a≡b refl 
...             | next a∈l = ¬a∈l a∈l

≡⟨⟩∈ : ∀ {A : Set} → {a b : A} → {l : List A} → a ≡ b →  (a ∈ (b ∷ l))
≡⟨⟩∈ refl = head 

¬a∈l : ∀ {A : Set} {a b : A} {l : List A} → ( ¬ (a ≡ b)) → ¬ (a ∈ l) → ¬ (a ∈ (b ∷ l))
¬a∈l _ ¬a∈l (next a∈l) = ¬a∈l a∈l
¬a∈l ¬a≡b ¬a∈l head = ¬a≡b refl

_∈?_ : ∀ {A : Set} → (a : A) → (l : List A) → Dec (a ∈ l) 
a ∈? []  = no ¬a∈[]
a ∈? (a′ ∷ l)  with a ∈? l 
...                 | yes a∈l = yes (next a∈l) 
...                 | no ¬a∈l with ≡lem {a = a} {b = a′}
...                             |  inj₁ refl = yes (≡⟨⟩∈ refl)
...                             | inj₂ ¬a≡a′ = no (̸≡⟨⟩∉ ¬a≡a′ ¬a∈l)

_∪_ : ∀ {A : Set} → List A → List A → List A
(a ∷ l) ∪ l' with a ∈? l' 
...             | yes a∈l' = l ∪ l'
...             | no ¬a∈l' = a ∷ (l ∪ l') 
[] ∪ l' = l' 

infixr 4 _∪_

_∩_ : ∀ {A : Set} → List A → List A → List A 
(a ∷ l) ∩ l′ with a ∈? l′ 
...             | yes a∈l′ = a ∷ (l ∩ l′)
...             | no ¬a∈l′ = l ∩ l′ 
[] ∩ l′ = l′

infixr 6 _∩_ 

_/_ : ∀ {A : Set} → List A → List A → List A 
(a ∷ l) / l′ with a ∈? l′ 
...             | yes a∈l' = l / l′ 
...             | no ¬a∈l′ = a ∷ (l / l′) 
[] / l′ = [] 

infixr 6 _/_

subTerm : Term -> List Term 
subTerm t@(var s) = t ∷ []
subTerm t@(app t1 t2) = t ∷ (subTerm t1 ∪ subTerm t2) 
subTerm t@(abst s t′) = t ∷ subTerm t′ 

properSubTerm : Term -> List Term 
properSubTerm (var s) = [] 
properSubTerm (app t1 t2) = subTerm t1 ∪ subTerm t2 
properSubTerm (abst s t′) = subTerm t′ 

freeVariable : Term -> List Variable
freeVariable (var x) = x ∷ [] 
freeVariable (app x y) = freeVariable x ∪ freeVariable y 
freeVariable (abst x y) = freeVariable y / (x ∷ [])

boundVariable : Term -> List Variable 
boundVariable (var _) = [] 
boundVariable (app t1 t2) = boundVariable t1 ∪ boundVariable t2 
boundVariable (abst x t) =  x ∷ boundVariable t  

bindVariable : Term -> List Variable 
bindVariable (var _) = [] 
bindVariable (app t1 t2) = bindVariable t1 ∪ bindVariable t2 
bindVariable (abst x t) = x ∷ bindVariable t 

_≡α_ : (x : Term) → Term → Set 
x ≡α y = x ≡ y

reflα : ∀ {x : Term} → x ≡α x 
reflα = refl 

symα : ∀ {x y : Term} → x ≡α y → y ≡α x 
symα = sym 

transα : ∀ {x y z : Term} → x ≡α y → y ≡α z → x ≡α z 
transα = trans

congα : ∀ (f : Term → Term) {x y : Term} → x ≡α y → f x ≡α f y 
congα = cong 

comp1 : ∀ {a b c : Term} → a ≡α b → app a c ≡α app b c 
comp1 {c = c} a≡b = congα (λ x → app x c) a≡b

comp2 : ∀ {a b c : Term} → a ≡α b → app c a ≡α app c b 
comp2 {c = c} a≡b = congα (λ x → app c x) a≡b 

comp3 : ∀ {a b : Term} {c : Variable} → a ≡α b → abst c a ≡α abst c b 
comp3 {c = c} a≡b = congα (λ x → abst c x) a≡b


_∧_ : ∀  {a : Level} {A B : Set a} → Dec A -> Dec B -> Dec (A × B)
yes a ∧ yes b = yes ( a , b )
no ¬a ∧  yes b = no λ ( a′ , b′) → ¬a a′
yes a ∧ no ¬b = no (λ (a′ , b′) → ¬b b′) 
no ¬a ∧ no ¬b = no (λ (a′ , b′) → ¬a a′)

_∨_ : ∀ {a : Level} {A B : Set a} → Dec A → Dec B → Dec (A ⊎ B)
yes a ∨ yes b = yes (inj₁ a)
yes a ∨ no ¬b = yes (inj₁ a) 
no ¬a ∨ yes b = yes (inj₂ b) 
no ¬a ∨ no ¬b = no λ{ (inj₁ a′) → ¬a a′ ; (inj₂ b′) → ¬b b′} 

~_ : ∀ {a : Level} {A : Set a} → Dec A → Dec (¬ A)
~ (yes a) = no (λ ¬a → ¬a a) 
~ (no ¬a) = yes ¬a

rename : Term -> Variable -> Variable -> Term 
rename t x y with ((~ (y ∈? freeVariable t)) ∧ (~ (y ∈? bindVariable t)))  | t 
...            | yes _ | var x′ with ≡lem {a = x′} {b = x}
...                               | inj₁ refl = var y
...                               | inj₂ ¬x′≡x = t
rename t x y   | yes _ | app t1 t2 = app (rename t1 x y) (rename t2 x y)  
rename t x y   | yes _ | abst x′ t′ with ≡lem {a = x′} {b = x}
...                               | inj₁ refl = abst x′ t′
...                               | inj₂ ¬x′≡x = abst x′ (rename t′ x y)  
rename t x y   | no _  | _ = t

postulate rena : ∀ {a : Term} {x y : Variable} → a ≡α (rename a x y)  

substitute : Term  -> Variable -> Term -> Term 
substitute (var x)  x′ t with ≡lem {a = x} {b = x′}
...                     | inj₁ refl = t
...                     | inj₂ ¬x≡x′ = var x  
substitute (app x y)  x′ t = app (substitute x x′ t) (substitute y x′ t) 
substitute (abst x y)  x′ t with x ∈? freeVariable t 
...                           | no _ = abst x (substitute y x′ t) 
...                           | yes _ = abst x y -- the substitution may cause conflicts  

lemmaα1 : ∀ {m1 m2 n1 n2 : Term} → m1 ≡α n1 → m2 ≡α n2 → (app m1 m2) ≡α (app n1 n2) 
lemmaα1 m1≡n1 m2≡n2 = transα (comp1 m1≡n1) (comp2 m2≡n2)

--lemma2 : ∀ {m1 m2 n1 n2 : Term} {x : Variable} → m1 ≡α n1 → m2 ≡α n2 → (substitute m1 x m2) ≡α (substitute n1 x n2) 
--lemma2 m1≡n1 m2≡n2 = {!   !}  

data _→β_ : Term → Term → Set where 
    base : ∀ {x : Variable} {m n : Term} → app (abst x m) n →β substitute m x n 
    comp→1 : ∀ {m n l : Term} → app m l →β app n l  
    comp→2 : ∀ {m n l : Term} → app l m →β app l n 
    comp→3 : ∀ {x : Variable} {m n l : Term} → abst x m →β abst x n 
    refl→ : ∀ {m : Term } → m →β m  


data _↠β_ : Term -> Term -> Set where 
    base : ∀ {m n : Term} → m →β n → m ↠β n
    seq : ∀ {m n p : Term} → m ↠β n → n →β p → m ↠β p 

refl↠ : ∀ {m : Term} → m ↠β m 
refl↠ {m} = base refl→   

trans↠ : ∀ {m n p : Term} → m ↠β n → n ↠β p → m ↠β p   
trans↠ m↠n (base n→βp) = seq m↠n n→βp
trans↠ m↠n (seq n↠p′ p′→p) = seq (trans↠ m↠n n↠p′) p′→p

data _≡β_ : Term → Term → Set where 
    base : ∀ {m n : Term} → m →β n → m ≡β n 
    seq1 : ∀ {m n p : Term} → m ≡β n → n →β p → m ≡β p 
    seq2 : ∀ {m n p : Term} → m ≡β n → p →β n → m ≡β p 

reflβ : ∀ {m : Term} → m ≡β m 
reflβ = base refl→ 

base′ : ∀ {m n : Term} → n →β m → m ≡β n 
base′ n→m = seq2 reflβ n→m 

transβ : ∀ {m n p : Term} → m ≡β n → n ≡β p → m ≡β p 
transβ m≡n (base n→p) = seq1 m≡n n→p
transβ m≡n (seq1 n≡p′ p′→p) = seq1 (transβ m≡n n≡p′) p′→p
transβ m≡n (seq2 n≡p′ p→p′) = seq2 (transβ m≡n n≡p′) p→p′

symβ : ∀ {m n : Term} → m ≡β n → n ≡β m 
symβ (base m→n) = base′ m→n
symβ (seq1 m≡n′ n′→n) = transβ (base′ n′→n) (symβ m≡n′)
symβ (seq2 m≡n′ n→n′) = transβ (base n→n′) (symβ m≡n′) 

lemmaβ1 : ∀ {m n : Term} → m ↠β n ⊎ n ↠β m → m ≡β n 
lemmaβ1 (inj₁ m↠n) with m↠n 
...                 | base m→n = base m→n
...                 | seq m↠n′ n′→n = seq1 (lemmaβ1 (inj₁ m↠n′)) n′→n 
lemmaβ1 (inj₂ n↠m) with n↠m 
...                 | base n→m = base′ n→m
...                 | seq n↠m′ m′→m = transβ (base′ m′→m) (lemmaβ1 (inj₂ n↠m′))

β-reduce : Term → Term 
β-reduce (var x) = var x
β-reduce (app (abst x t1) t2) = substitute t1 x t2 
β-reduce (app t1 t2) = app (β-reduce t1) (β-reduce t2)
β-reduce (abst x t) = abst x (β-reduce t) 

data Reduceable : Term → Set where 
    reduce : ∀ {m : Term} → ∃[ n ] (m ↠β n × ¬ (m ≡ n)) → Reduceable m

β-form : Term → Set
β-form m = ¬ Reduceable m

⊥-elim : ∀ {A : Set} → ⊥ → A 
⊥-elim ()

lemmaβnf : ∀ {m n : Term} → β-form m → m ↠β n → m ≡ n 
lemmaβnf {m} {n} ¬r m↠n with ≡lem {a = m} {b = n}
...                 | inj₁ m≡n = m≡n
...                 | inj₂ ¬m≡n = ⊥-elim (¬r (reduce (n , (m↠n , ¬m≡n)))) 
  
   
 
 