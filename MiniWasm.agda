module MiniWasm {Var : Set} where

-- Var is a set of variables that is used for store / load operation

open import Data.Maybe as MaybeM
open import Function hiding (const)
open import Data.Integer as Int hiding (_+_ ; suc ; _≤_ ; _≤?_ ; +_ ; _⊔_ ; _≰_ ; _*_)
open import Data.Nat as Nat
open import Data.Bool as BoolM hiding (not ; _≤_ ; _≤?_)
open import Data.Unit hiding (_≤_ ;  _≤?_)
open import Data.Product
open import Data.Fin as FinM hiding (_+_ ; _≤_ ; _≤?_)
open import Data.Vec as VecM hiding (_++_ ; length ; _>>=_)
open import Data.List as ListM hiding (and)
open import Relation.Binary.PropositionalEquality as ≡
open import Relation.Binary
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Nullary.Product
open import Data.Empty
open import Data.Sum

data ValueType : Set where
  I32 : ValueType
  I64 : ValueType

data Kind : Set where
  Insn : Kind
  Code : Kind

infixr 9 _∙_
data Syntax : (k : Kind) → Set where
  const : ValueType → ℤ → Syntax Insn
  load : Var → Syntax Insn
  store : Var → Syntax Insn
  add : Syntax Insn
  mul : Syntax Insn
  and : Syntax Insn
  not : Syntax Insn
  nop : Syntax Insn
  br : (l : ℕ) → Syntax Insn
  brif : (l : ℕ) → Syntax Insn
  block : (t : ℕ × ℕ) → (is : Syntax Code) → Syntax Insn
  loop : (t : ℕ × ℕ) → (is : Syntax Code) → Syntax Insn
  ε : Syntax Code
  _∙_ : Syntax Code → Syntax Insn →  Syntax Code

module Typing where
  open Syntax
  open import Data.Nat.Properties
  ResultType = List ValueType
  BlkCtx = List ResultType

  m+n≡o⇒m≤o : ∀ {m n o : ℕ} → m + n ≡ o → m ≤ o
  m+n≡o⇒m≤o m+n≡o = m+n≤o⇒m≤o _ (≤-reflexive m+n≡o)
  +-assoc' : ∀{m} n o → m + (n + o) ≡ m + n + o
  +-assoc' {m} n o = sym (+-assoc m n o)
  m+0≡m : ∀ {m} → m + 0 ≡ m
  m+0≡m {m} = +-identityʳ m
  m≡m+0 : ∀{m} → m ≡ m + 0
  m≡m+0 {m} = sym m+0≡m

  _!!_ : List ℕ → ℕ → Maybe ℕ
  (e ∷ _) !! zero = just e
  (_ ∷ rs) !! (suc l) = rs !! l
  _ !! _ = nothing

  data Q : Set where --quantifier
    uni : Q
    bi : Q

  data _≤Q_ : Q → Q → Set where
    bi≤q : ∀{q} → bi ≤Q q
    uni≤uni : uni ≤Q uni

  symQ : (q : Q) → q ≤Q q
  symQ bi = bi≤q
  symQ uni = uni≤uni

  ≤Q-isPreorder : IsPreorder _≡_ _≤Q_
  ≤Q-isPreorder = record
    { isEquivalence = ≡.isEquivalence
    ; reflexive = λ
      { {uni} refl → uni≤uni
      ; {bi} refl → bi≤q
      }
    ; trans = λ
      { bi≤q bi≤q → bi≤q
      ; bi≤q uni≤uni → bi≤q
      ; uni≤uni uni≤uni → uni≤uni
      }
    }

  _≤Q?_ : Decidable _≤Q_
  uni ≤Q? uni = yes uni≤uni
  bi ≤Q? q = yes bi≤q
  uni ≤Q? bi = no λ ()

  _⊓Q_ : Q → Q → Q
  uni ⊓Q q = q
  _ ⊓Q _ = bi

  toNat : Q → ℕ
  toNat bi = 0
  toNat uni = 1

  extQ : Q → ℕ → ℕ → Set
  extQ uni d e = d ≡ e
  extQ bi _ _ = ⊤

  ext : Q → ℕ × ℕ → ℕ × ℕ → Set
  ext q (a , r) (a' , r') = ∃₂ λ d e → (a + d ≡ a') × (r + e ≡ r') × extQ q d e

  pattern extuni d e = (d , e , refl , refl , refl)
  pattern extbi d e = (d , e , refl , refl , tt)
  pattern extq d e q = (d , e , refl , refl , q)

  castQ : ∀ q {a r} → ext q a r → ext bi a r
  castQ q (d , e , refl , refl , _) = (d , e , refl , refl , tt)
 
  ext? : ∀ q → Decidable (ext q)
  ext? q (a , r) (a' , r') with a ≤? a' | r ≤? r' 
  ... | no na | _ = no $ na ∘ m+n≡o⇒m≤o ∘ λ (_ , _ , ma , _ , _) → ma 
  ... | _ | no nr = no $ nr ∘ m+n≡o⇒m≤o ∘ λ (_ , _ , _ , mr , _) → mr
  ext? bi (a , r) (a' , r') | yes ya | yes yr = yes (a' ∸ a , r' ∸ r , m+[n∸m]≡n ya , m+[n∸m]≡n yr , _)
  ext? uni (a , r) (a' , r') | yes ya | yes yr with a' ∸ a Nat.≟ r' ∸ r
  ext? uni (a , r) (a' , r') | yes ya | yes yr | no neq = no λ{ (d , .d , refl , refl , refl) → neq ( ≡.trans (m+n∸m≡n a d) (sym (m+n∸m≡n r d)))}
  ext? uni (a , r) (a' , r') | yes ya | yes yr | yes eq = yes (a' ∸ a , r' ∸ r , m+[n∸m]≡n ya , m+[n∸m]≡n yr , eq)
 
  ext-IsPreorder : ∀ q → IsPreorder _≡_ (ext q)
  ext-IsPreorder uni = record { isEquivalence = ≡.isEquivalence ; reflexive = λ { refl → 0 , 0 , m+0≡m , m+0≡m , refl} ; trans = λ { (extuni dij .dij) (extuni djk .djk) → dij + djk , dij + djk , +-assoc' dij djk , +-assoc' dij djk , refl }}
  ext-IsPreorder bi = record { isEquivalence = ≡.isEquivalence ; reflexive = λ { refl → 0 , 0 , m+0≡m , m+0≡m , _} ; trans = λ { (extbi dij eij) (extbi djk ejk) → dij + djk , eij + ejk , +-assoc' dij djk , +-assoc' eij ejk , tt}}

  data _<:_ : Q × ℕ × ℕ → Q × ℕ × ℕ → Set where
    <:-intro : ∀{q q' t t'} → q ≤Q q' → ext q t t' → (q , t) <: (q' , t')

  data _<:'_ : Q × ℕ × ℕ → Q × ℕ × ℕ → Set where
    <:'-bi : ∀{q' a r d e} → (bi , a , r) <:' (q' , a + d , r + e)
    <:'-uni : ∀{q a r d} → (q , a , r) <:' (uni , a + d , r + d)

  qt<:unit : ∀ q t → (q , t) <: (uni , t)
  qt<:unit uni t = <:-intro uni≤uni (0 , 0 , m+0≡m , m+0≡m , refl)
  qt<:unit bi t = <:-intro bi≤q (0 , 0 , m+0≡m , m+0≡m , _)
  
  _<:?_ : Decidable _<:_
  (q , t) <:? (q' , t') with q ≤Q? q' | ext? q t t'
  ... | yes p | yes ex = yes (<:-intro p ex)
  ... | no ¬p | _ = no $ ¬p ∘ λ { (<:-intro p _) → p }
  ... | _ | no ¬ex = no $ ¬ex ∘ λ { (<:-intro _ ex) → ex }

  data _<:M_ : Maybe (Q × ℕ × ℕ) → Maybe (Q × ℕ × ℕ) → Set where
    <:nothing : ∀{qt} → qt <:M nothing
    just<: : ∀{qt qt'} → qt <: qt' → just qt <:M just qt'

  _<:M?_ : Decidable _<:M_
  _ <:M? nothing = yes <:nothing
  just qt <:M? just qt' with qt <:? qt'
  ... | yes p = yes (just<: p)
  ... | no ¬p = no λ{(just<: p) → ¬p p}
  nothing <:M? just _ = no λ()

  data _∈_ : ℕ × ℕ → Q × ℕ × ℕ → Set where
    ∈-intro : ∀ {t t0} q → ext q t0 t → t ∈ (q , t0)

  data _∈M_ : ℕ × ℕ → Maybe (Q × ℕ × ℕ) → Set where
    sub : ∀{t qt} → t ∈ qt → t ∈M just qt

  ∈⇒<:uni : ∀{t qt} → t ∈ qt → qt <: (uni , t)
  ∈⇒<:uni (∈-intro uni ex) = <:-intro uni≤uni ex
  ∈⇒<:uni (∈-intro bi ex) = <:-intro bi≤q ex

  <:uni⇒∈ : ∀{t qt} → qt <: (uni , t) → t ∈ qt
  <:uni⇒∈ (<:-intro bi≤q ex) = ∈-intro bi ex
  <:uni⇒∈ (<:-intro uni≤uni ex) = ∈-intro uni ex

  min∈ : (qt : Q × ℕ × ℕ) → let (_ , t) = qt in t ∈ qt
  min∈ (uni , a , r) = ∈-intro uni (0 , 0 , m+0≡m , m+0≡m , refl)
  min∈ (bi , a , r) = ∈-intro bi (0 , 0 , m+0≡m , m+0≡m , tt)

  extQsame : ∀ q d → extQ q d d
  extQsame uni d = refl
  extQsame bi d = tt

  +d+d∈qt : (d : ℕ) → (qt : Q × ℕ × ℕ) → let (_ , a , r) = qt in (a + d , r + d) ∈ qt
  +d+d∈qt d (uni , a , r) = ∈-intro uni (extuni d d)
  +d+d∈qt d (bi , a , r) = ∈-intro bi (extbi d d)

  weaken∈ : ∀ {q a r a0 r0} d → (a0 , r0) ∈ (q , a + d , r + d) → (a0 , r0) ∈ (q , a , r)
  weaken∈ {a = a} {r = r} d (∈-intro uni (extuni d' .d')) rewrite +-assoc a d d' | +-assoc r d d' =  ∈-intro uni (extuni (d + d') (d + d'))
  weaken∈ {a = a} {r = r} d (∈-intro bi (extbi d' e')) rewrite +-assoc a d d' | +-assoc r d e' =  ∈-intro bi (extbi (d + d') (d + e'))

  <:-isPreorder : IsPreorder _≡_ _<:_
  <:-isPreorder = record
    { isEquivalence = isEquivalence
    ; reflexive = λ
      { {uni , _} refl → <:-intro uni≤uni (uniM.reflexive refl)
      ; {bi , _} refl → <:-intro bi≤q (biM.reflexive refl)
      }
    ; trans = λ
      { {uni , _} {uni , _} {uni , _} (<:-intro _ ij) (<:-intro _ jk) → <:-intro uni≤uni (uniM.trans ij jk)
      ; {bi , _} {uni , _} {uni , _} (<:-intro _ ij) (<:-intro _ jk) → <:-intro bi≤q (biM.trans ij (castQ _ jk))
      ; {bi , _} {bi , _} {_ , _} (<:-intro _ ij) (<:-intro _ jk) → <:-intro bi≤q (biM.trans ij jk)
      }
    } where
    module uniM = IsPreorder (ext-IsPreorder uni)
    module biM = IsPreorder (ext-IsPreorder bi)

  <:M-isPreorder : IsPreorder _≡_ _<:M_
  <:M-isPreorder = record
    { isEquivalence = isEquivalence
    ; reflexive = λ
      { {nothing} refl → <:nothing
      ; {just _} refl → just<: (IsPreorder.reflexive <:-isPreorder refl)
      }
    ; trans = λ
      { {_} {_} {nothing} _ _ → <:nothing
      ; {just _} {just _} {just _} (just<: ij) (just<: jk) → just<: (IsPreorder.trans <:-isPreorder ij jk)
      }
    }


  private
    variable
      z : ℤ
      v : Var
      a r : ℕ

  -- Typing rules in Wasm specification style 
  -- Every single instruction (except stack polymorhic e.g. br l) gets one type.
  -- but sequences get many types.

  data _⊢spec_:'_ (rs : List ℕ) : {k : Kind} → Syntax k → ℕ × ℕ → Set where
    const : ∀ t → rs ⊢spec const t z :' (0 , 1)
    load : rs ⊢spec load v :' (0 , 1)
    store : rs ⊢spec store v :' (1 , 0)
    nop : rs ⊢spec nop :'  (0 , 0)
    not : rs ⊢spec not :' (1 , 1)
    and : rs ⊢spec and :' (2 , 1)
    mul : rs ⊢spec mul :' (2 , 1)
    add : rs ⊢spec add :' (2 , 1)
    br : ∀{l u} → rs !! l ≡ just u → ∀ d e → rs ⊢spec br l :' (u + d , e)
    brif : ∀{l u} → rs !! l ≡ just u → rs ⊢spec brif l :' (suc u , u)
    block : ∀ (t : ℕ × ℕ) {is} → let (a , r) = t in (r ∷ rs) ⊢spec is :' (a , r) → rs ⊢spec block (a , r) is :' (a , r)
    loop : ∀ (t : ℕ × ℕ) {is} → let (a , r) = t in (a ∷ rs) ⊢spec is :' (a , r) → rs ⊢spec loop (a , r) is :' (a , r)
    ε : rs ⊢spec ε :' (a , a)
    comp : ∀{is i a m r ai ri d}
      → m ≡ ai + d
      → r ≡ ri + d
      → rs ⊢spec is :' (a , m)
      → rs ⊢spec i :' (ai , ri)
      → rs ⊢spec (is ∙ i) :' (a , r)

  -- Direct style typing rule
  -- Every instruction and sequence gets many types. 
  -- compositions are designed by direct mediating result type
  data _⊢dir_:'_ (rs : List ℕ) : {k : Kind} → Syntax k → ℕ × ℕ → Set where
    const : ∀ t d → rs ⊢dir const t z :' (d , suc d)
    load : ∀ d →  rs ⊢dir load v :' (d , suc d)
    store : ∀ d → rs ⊢dir store v :' (suc d , d)
    nop : ∀ d → rs ⊢dir nop :' (d , d)
    not : ∀ d → rs ⊢dir not :' (suc d , suc d)
    and : ∀ d → rs ⊢dir and :' (suc (suc d) , suc d)
    mul : ∀ d → rs ⊢dir mul :' (suc (suc d) , suc d)
    add : ∀ d → rs ⊢dir add :' (suc (suc d) , suc d)
    br : ∀ {l u} → rs !! l ≡ just u → ∀ d e → rs ⊢dir br l :' (u + d , e)
    brif : ∀ {l u} → rs !! l ≡ just u → ∀ d → rs ⊢dir brif l :' (suc u + d , u + d)
    block : ∀ (t : ℕ × ℕ) {is} → let (a , r) = t in (r ∷ rs) ⊢dir is :' (a , r) → ∀ d → rs ⊢dir block (a , r) is :' (a + d , r + d)
    loop :  ∀ (t : ℕ × ℕ) {is} → let (a , r) = t in (a ∷ rs) ⊢dir is :' (a , r) → ∀ d → rs ⊢dir loop (a , r) is :' (a + d , r + d)
    ε : ∀ d → rs ⊢dir ε :' (d , d)
    comp : ∀{i is a r m} → rs ⊢dir is :' (a , m) → rs ⊢dir i :' (m , r) → rs ⊢dir (is ∙ i) :' (a , r)

  dir⇒specI : ∀{rs a r} → {i : Syntax Insn} → rs ⊢dir i :' (a , r) → ∃ λ d → ∃ λ a' → ∃ λ r' → (a ≡ a' + d) × (r ≡ r' + d) × (rs ⊢spec i :' (a' , r')) 
  dir⇒spec : ∀{rs t} → {is : Syntax Code} → rs ⊢dir is :' t → rs ⊢spec is :' t

  dir⇒specI (const t d) = (d , 0 , 1 , refl , refl , const t)
  dir⇒specI (load d) = (d , 0 , 1 , refl , refl , load)
  dir⇒specI (store d) = (d , 1 , 0 , refl , refl , store)
  dir⇒specI (nop d) = (d , 0 , 0 , refl , refl , nop)
  dir⇒specI (not d) = (d , 1 , 1 , refl , refl , not)
  dir⇒specI (and d) = (d , 2 , 1 , refl , refl , and)
  dir⇒specI (mul d) = (d , 2 , 1 , refl , refl , mul)
  dir⇒specI (add d) = (d , 2 , 1 , refl , refl , add)
  dir⇒specI {rs} {a} {r} (br {u = u} rs!!l≡justu d e) = (0 , a , r , sym (+-identityʳ _) , sym (+-identityʳ _) , br rs!!l≡justu d e)
  dir⇒specI (brif {u = u} rs!!l≡justu d) = (d , suc u  , u , refl , refl , brif rs!!l≡justu)
  dir⇒specI (block (a , r) {is = is} tis d) = (d , a , r , refl , refl , block (a , r) (dir⇒spec tis))
  dir⇒specI (loop (a , r) tis d) = (d , a , r , refl , refl , loop (a , r) (dir⇒spec tis))

  dir⇒spec (ε _) = ε
  dir⇒spec (comp tis ti) with dir⇒specI ti
  ... | (_ , _ , _ , refl , refl , ti') = comp refl refl (dir⇒spec tis) ti'

  spec⇒dirI : ∀{rs a r} → {i : Syntax Insn} → rs ⊢spec i :' (a , r) → ∀ d → rs ⊢dir i :' (a + d , r + d)
  spec⇒dir : ∀{rs t} → {is : Syntax Code} → rs ⊢spec is :' t → rs ⊢dir is :' t

  spec⇒dirI (const t) d = const t d
  spec⇒dirI load d = load d
  spec⇒dirI store d = store d
  spec⇒dirI nop d = nop d
  spec⇒dirI not d = not d
  spec⇒dirI and d = and d
  spec⇒dirI mul d = mul d
  spec⇒dirI add d = add d
  spec⇒dirI {rs} {a} {r} (br {u = u} rs!!l≡justu d' e) d rewrite (+-assoc u d' d) = br rs!!l≡justu (d' + d) (r + d) 
  spec⇒dirI (brif rs!!l≡justu) d = brif rs!!l≡justu d
  spec⇒dirI (block (a , r) tis) d with spec⇒dir tis 
  ... | tis' = block (a , r) tis' d
  spec⇒dirI (loop (a , r) tis) d with spec⇒dir tis
  ... | tis' = loop (a , r) tis' d

  spec⇒dir ε = ε _
  spec⇒dir (comp {d = d} refl refl tis ti) with spec⇒dir tis | spec⇒dirI ti d
  ... | tis' | ti' = comp tis' ti'

  -- Typing rules with qualifiers and subtyping
  -- `uni' and `bi' qualify function types
  -- every instruction gets principal type
  -- all function types can be weakened by subsumption
  -- there are two flavors of subsumption acording to uni
  data _⊢sub_:'_ (rs : List ℕ) : {k : Kind} → Syntax k → Q × ℕ × ℕ → Set where
    const : ∀ t → rs ⊢sub const t z :' (uni , 0 , 1)
    load : rs ⊢sub load v :' (uni , 0 , 1)
    store : rs ⊢sub store v :' (uni , 1 , 0)
    nop : rs ⊢sub nop :' (uni , 0 , 0)
    not : rs ⊢sub not :' (uni , 1 , 1)
    and : rs ⊢sub and :' (uni , 2 , 1)
    mul : rs ⊢sub mul :' (uni , 2 , 1)
    add : rs ⊢sub add :' (uni , 2 , 1)
    br : ∀ {l u} → rs !! l ≡ just u → rs ⊢sub br l :' (bi , u , 0)
    brif : ∀ {l u} → rs !! l ≡ just u → rs ⊢sub brif l :' (uni , suc u , u)
    block : {is : Syntax Code} → (qt : Q × ℕ × ℕ) → let (q , a , r) = qt
      in (r ∷ rs) ⊢sub is :' (q , a , r) → rs ⊢sub block (a , r) is :' (uni , a , r)
    loop :  {is : Syntax Code} → (qt : Q × ℕ × ℕ) → let (q , a , r) = qt
      in (a ∷ rs) ⊢sub is :' (q , a , r) → rs ⊢sub loop (a , r) is :' (uni , a , r)
    ε : rs ⊢sub ε :' (uni , 0 , 0)
    comp : ∀{is i a r m} qis qi
      → rs ⊢sub is :' (qis , a , m)
      → rs ⊢sub i :' (qi , m , r)
      → rs ⊢sub (is ∙ i) :' (qis ⊓Q qi , a , r)
    sub : ∀{k qt qt'} {i : Syntax k} → rs ⊢sub i :' qt → qt <: qt' → rs ⊢sub i :' qt'

  cover : ∀{t rs k} → {i : Syntax k} → rs ⊢dir i :' t → ∃ λ qt → t ∈ qt × rs ⊢sub i :' qt
  cover (const t _) = (uni , 0 , 1) , ∈-intro uni (extuni _ _) , const t
  cover (load d) = (uni , 0 , 1) , ∈-intro uni (extuni _ _) , load
  cover (store d) = (uni , 1 , 0) , ∈-intro uni (extuni _ _) , store
  cover (nop d) = (uni , 0 , 0) , ∈-intro uni (extuni _ _) , nop
  cover (not d) = (uni , 1 , 1) , ∈-intro uni (extuni _ _) , not
  cover (and d) = (uni , 2 , 1) , ∈-intro uni (extuni _ _) , and
  cover (mul d) = (uni , 2 , 1) , ∈-intro uni (extuni _ _) , mul
  cover (add d) = (uni , 2 , 1) , ∈-intro uni (extuni _ _) , add
  cover {rs = rs} {i = br l} (br eq _ _) with rs !! l | inspect (rs !!_) l
  cover {rs = rs} {i = br l} (br refl _ _) | just u | ≡.[ eq ] = (bi , u , 0) , ∈-intro bi (extbi _ _) , br eq
  cover {rs = rs} {i = brif l} (brif eq d) with rs !! l | inspect (rs !!_) l
  cover {rs = rs} {_} {brif l} (brif refl d) | just u | ≡.[ eq ] = (uni , suc u , u) , ∈-intro uni (extuni _ _) , brif eq
  cover (block t tis d) = let _ , ex , tis' = cover tis
    in (uni , t) , ∈-intro uni (extuni _ _) , block (uni , t) (sub tis' (∈⇒<:uni ex))
  cover (loop t tis d) =  let _ , ex , tis' = cover tis
    in (uni , t) , ∈-intro uni (extuni _ _) , loop (uni , t) (sub tis' (∈⇒<:uni ex))
  cover (ε d) = (uni , 0 , 0) ,  ∈-intro uni (extuni _ _) , ε
  cover {t = t} (comp ti tis) = let
    _ , tis∈qtis , tis' = cover tis
    _ , ti∈qti , ti' = cover ti
    in (uni , t) , ∈-intro uni (0 , 0 , m+0≡m , m+0≡m , refl) , comp uni uni (sub ti' (∈⇒<:uni ti∈qti)) (sub tis' (∈⇒<:uni tis∈qtis))

  admissible : ∀{qt t rs k} → {i : Syntax k} → rs ⊢sub i :' qt → t ∈ qt → rs ⊢dir i :' t
  admissible (const t) (∈-intro uni (extuni _ _)) = const t _
  admissible load (∈-intro uni (extuni _ _)) = load _
  admissible store (∈-intro uni (extuni _ _)) = store _
  admissible nop (∈-intro uni (extuni _ _)) = nop _
  admissible not (∈-intro uni (extuni _ _)) = not _
  admissible and (∈-intro uni (extuni _ _)) = and _
  admissible mul (∈-intro uni (extuni _ _)) = mul _
  admissible add (∈-intro uni (extuni _ _)) = add _
  admissible (br l) (∈-intro bi (_ , _ , refl , refl , _)) = br l _ _
  admissible (brif l) (∈-intro uni (extuni _ _)) = brif l _
  admissible (block (q , t) tis) (∈-intro uni (extuni _ _)) = block t (admissible tis (min∈ (q , t))) _
  admissible (loop (q , t) tis) (∈-intro uni (extuni _ _)) = loop t (admissible tis (min∈ (q , t))) _
  admissible ε (∈-intro uni (d , .d , refl , refl , refl)) = ε _
  admissible (comp uni uni tis ti) (∈-intro .uni (d , .d , refl , refl , refl)) = comp (admissible tis (∈-intro uni (d , d , refl , refl , refl))) (admissible ti (∈-intro uni (d , d , refl , refl , refl)))
  admissible (comp uni bi tis ti) (∈-intro .bi (d , e , refl , refl , tt)) = comp (admissible tis (∈-intro uni (d , d , refl , refl , refl))) (admissible ti (∈-intro bi (d , e , refl , refl , tt)))
  admissible (comp bi uni tis ti) (∈-intro .bi (d , e , refl , refl , tt)) = comp (admissible tis (∈-intro bi (d , e , refl , refl , tt))) (admissible ti (∈-intro uni (e , e , refl , refl , refl)))
  admissible (comp bi bi tis ti) (∈-intro .bi (d , e , refl , refl , tt)) = comp (admissible tis (∈-intro bi (d , d , refl , refl , tt))) (admissible ti (∈-intro bi (d , e , refl , refl , tt)))
  admissible (sub ti qt'<:qt) t∈qt =  admissible ti (<:uni⇒∈ (<:.trans qt'<:qt (∈⇒<:uni t∈qt))) where
    module <: = IsPreorder <:-isPreorder

module TypeInference where
  open Syntax
  open Typing
  open import Data.Nat.Properties

  _*Q_ : Q → ℕ → ℕ
  _*Q_ bi n = 0
  _*Q_ uni n = n

  compM : Q × ℕ × ℕ → Q × ℕ × ℕ → Maybe (Q × ℕ × ℕ)
  compM (q1 , a1 , r1) (q2 , a2 , r2) = just (q1 ⊓Q q2 , a1 + (q1 *Q (a2 ∸ r1)) , r2 + (q2 *Q (r1 ∸ a2)))

  infer : List ℕ → {k : Kind} → Syntax k → Maybe (Q × ℕ × ℕ)
  infer rs (const t z) = just (uni , 0 , 1)
  infer rs (load x) = just (uni , 0 , 1)
  infer rs (store x) = just (uni , 1 , 0)
  infer rs add = just (uni , 2 , 1)
  infer rs mul = just (uni , 2 , 1)
  infer rs and = just (uni , 2 , 1)
  infer rs not = just (uni , 1 , 1)
  infer rs nop = just (uni , 0 , 0)
  infer rs (br l) = case (rs !! l) of λ where
    nothing → nothing
    (just e) → just (bi , e , 0)
  infer rs (brif l) = do
    e ← rs !! l
    just (uni , suc e , e)
  infer rs (block (a , r) is) = do
    t ← infer (r ∷ rs) is
    _ ← decToMaybe (t <:? (uni , a , r))
    just (uni , a , r)
  infer rs (loop (a , r) is) = do
    t ← infer (a ∷ rs) is
    _ ← decToMaybe (t <:? (uni , a , r))
    just (uni , a , r)
  infer rs ε = just (uni , 0 , 0)
  infer rs (is ∙ i) = do
    tis ← infer rs is
    ti ← infer rs i
    compM tis ti

  example0' = (uni , 1 , 1) <:? (uni , 2 , 2)
  example0 = infer [] (block (1 , 1) (ε ∙ br 0))
  example1 = infer (1 ∷ []) (br 0)
  example2 = infer (1 ∷ []) (ε ∙ br 0)


  n≡n+[n∸n] : ∀ n → n ≡ n + (n ∸ n)
  n≡n+[n∸n] zero = refl
  n≡n+[n∸n] (suc n) = cong suc (n≡n+[n∸n] n)

  r∸a≡r⊔a∸a : ∀ r a → r ∸ a ≡ (r ⊔ a) ∸ a
  r∸a≡r⊔a∸a r zero = sym (⊔-identityʳ r)
  r∸a≡r⊔a∸a zero (suc a) = sym (n∸n≡0 a)
  r∸a≡r⊔a∸a (suc r) (suc a) = r∸a≡r⊔a∸a r a

  r⊔a∸a≡r∸a : ∀ r a → (r ⊔ a) ∸ a ≡ r ∸ a
  r⊔a∸a≡r∸a r a = sym (r∸a≡r⊔a∸a r a)

  a∸r≡r⊔a∸r : ∀ r a → a ∸ r ≡ (r ⊔ a) ∸ r
  a∸r≡r⊔a∸r zero a = refl
  a∸r≡r⊔a∸r (suc r) zero = sym (n∸n≡0 r)
  a∸r≡r⊔a∸r (suc r) (suc a) = a∸r≡r⊔a∸r r a

  r⊔a≡r+[r⊔a∸r] : ∀ r a → r ⊔ a ≡ r + ((r ⊔ a) ∸ r)
  r⊔a≡r+[r⊔a∸r] zero r = refl
  r⊔a≡r+[r⊔a∸r] (suc r) zero = cong suc (n≡n+[n∸n] r)
  r⊔a≡r+[r⊔a∸r] (suc r) (suc a) = cong suc (r⊔a≡r+[r⊔a∸r] r a)

  r⊔a≡a+[r⊔a∸a] : ∀ r a → r ⊔ a ≡ a + ((r ⊔ a) ∸ a)
  r⊔a≡a+[r⊔a∸a] a zero = refl
  r⊔a≡a+[r⊔a∸a] zero (suc r) = cong suc (n≡n+[n∸n] r)
  r⊔a≡a+[r⊔a∸a] (suc a) (suc r) = cong suc (r⊔a≡a+[r⊔a∸a] a r)

  soundness : ∀{qt k rs} → (is : Syntax k) → infer rs is ≡ just qt → rs ⊢sub is :' qt
  soundness (const t _) refl = const t
  soundness (load _) refl = load
  soundness (store _) refl = store
  soundness add refl = add
  soundness mul refl = mul
  soundness and refl = and
  soundness not refl = not
  soundness nop refl = nop
  soundness {rs = rs} (br l) eq with rs !! l | inspect (rs !!_) l
  soundness {rs = rs} (br l) refl | just u | ≡.[ eq ] =  br eq 
  soundness {rs = rs} (brif l) eq with rs !! l | inspect (rs !!_) l
  soundness {rs = rs} (brif l) refl | just u | ≡.[ eq ] = brif eq
  soundness {rs = rs} (block (a' , r') is) inf with infer (r' ∷ rs) is | inspect (infer (r' ∷ rs)) is
  ... | just (q , a , r) | [ eq ] with (q , a , r) <:? (uni , a' , r')
  soundness {rs = rs} (block (a' , r') is) refl | just (q , a , r) | [ eq ] | yes t<: = block (uni , a' , r') (sub (soundness is eq) t<:)
  soundness {rs = rs} (loop (a' , r') is) inf with infer (a' ∷ rs) is | inspect (infer (a' ∷ rs)) is
  ... | just (q , a , r) | [ eq ] with (q , a , r) <:? (uni , a' , r')
  soundness {rs = rs} (loop (a' , r') is) refl | just (q , a , r) | [ eq ] | yes t<: = loop (uni , a' , r') (sub (soundness is eq) t<:)
  soundness ε refl = ε
  soundness {rs = rs} (is ∙ i) inf with infer rs is | inspect (infer rs) is
  ... | just (qis , ais , ris) | [ eqC ] with infer rs i | inspect (infer rs) i
  ... | just (qi , ai , ri) | [ eqI ] with soundness is eqC | soundness i eqI
  soundness {rs = rs} (is ∙ i) refl | just (uni , ais , ris) | _ | just (uni , ai , ri) | _ | tis | ti =
    comp uni uni
      (sub tis (<:-intro uni≤uni (ai ⊔ ris ∸ ris , ai ⊔ ris ∸ ris , cong (ais +_) (sym (r∸a≡r⊔a∸a ai ris)) , sym (r⊔a≡a+[r⊔a∸a] ai ris) , refl)))
      (sub ti (<:-intro uni≤uni (ai ⊔ ris ∸ ai , ai ⊔ ris ∸ ai , sym (r⊔a≡r+[r⊔a∸r] ai ris) , cong (ri +_) (sym (a∸r≡r⊔a∸r ai ris)) , refl)))
  soundness {rs = rs} (is ∙ i) refl | just (uni , ais , ris) | _ | just (bi , ai , ri) | _ | tis | ti =
    comp uni bi -- (ai ⊔ ris)
      (sub tis (<:-intro uni≤uni (ai ⊔ ris ∸ ris , ai ⊔ ris ∸ ris , cong (ais +_) (sym (r∸a≡r⊔a∸a ai ris)) , sym (r⊔a≡a+[r⊔a∸a] ai ris) , refl)))
      (sub ti (<:-intro bi≤q (ai ⊔ ris ∸ ai , 0 , sym (r⊔a≡r+[r⊔a∸r] ai ris) , refl , _)))
  soundness {rs = rs} (is ∙ i) refl | just (bi , ais , ris) | _ | just (uni , ai , ri) | _ | tis | ti =
    comp bi uni -- (ai ⊔ ris)
      (sub tis (<:-intro bi≤q (0 , ai ⊔ ris ∸ ris , refl , sym (r⊔a≡a+[r⊔a∸a] ai ris) , _)))
      (sub ti (<:-intro uni≤uni (ai ⊔ ris ∸ ai , ai ⊔ ris ∸ ai , sym (r⊔a≡r+[r⊔a∸r] ai ris) , cong (ri +_) (sym (a∸r≡r⊔a∸r ai ris)) , refl)))
  soundness {rs = rs} (is ∙ i) refl | just (bi , ais , ris) | _ | just (bi , ai , ri) | _ | tis | ti =
    comp bi bi -- (ai ⊔ ris)
      (sub tis (<:-intro bi≤q (0 , ai ⊔ ris ∸ ris , refl , sym (r⊔a≡a+[r⊔a∸a] ai ris) , _)))
      (sub ti (<:-intro bi≤q (ai ⊔ ris ∸ ai , 0 , sym (r⊔a≡r+[r⊔a∸r] ai ris) , refl , _)))

  -- rewrite +-identityʳ r2 = {!!}
  lemma-ext : ∀ {q1' d1 e1 q2' d2 e2 a1 r1 a2 r2} →
    extQ q1' d1 e1 →
    extQ q2' d2 e2 →
    r1 + e1 ≡ a2 + d2 →
    ext (q1' ⊓Q q2') (a1 + (q1' *Q (a2 ∸ r1)) , r2 + (q2' *Q (r1 ∸ a2))) (a1 + d1 , r2 + e2)
  lemma-ext {q1' = uni} {d1 = d1} {q2' = uni} {d2 = .d1} {a1 = a1} {r1 = zero} {a2 = zero} {r2 = r2} refl refl refl rewrite +-identityʳ a1 | +-identityʳ r2 = d1 , d1 , refl , refl , refl
  lemma-ext {q1' = uni} {d1 = d1} {q2' = uni} {d2 = d2} {a1 = a1} {r1 = suc r1} {a2 = zero} {r2 = r2} refl refl eq rewrite +-identityʳ a1 | sym eq = d1 , d1 , refl , +-assoc r2 _ _ , refl
  lemma-ext {q1' = uni} {d1 = d1} {q2' = uni} {d2 = d2} {a1 = a1} {r1 = zero} {a2 = suc a2} {r2 = r2} refl refl eq rewrite +-identityʳ r2 | eq = d2 , d2 , +-assoc a1 _ _ , refl , refl
  lemma-ext {q1' = uni} {d1 = d1} {q2' = uni} {d2 = d2} {a1 = a1} {r1 = suc r1} {a2 = suc a2} {r2 = r2} P@refl P'@refl eq = lemma-ext P P' (suc-injective eq)
  lemma-ext {q1' = uni} {d1 = d1} {q2' = bi} {d2 = .d1} {e2 = e2} {a1 = a1} {r1 = zero} {zero} {r2 = r2} refl tt refl rewrite +-identityʳ a1 | +-identityʳ r2 =  d1 , e2 , refl , refl , tt
  lemma-ext {q1' = uni} {d1 = d1} {e1 = e1} {q2' = bi} {d2 = d2} {e2 = e2} {a1 = a1} {r1 = zero} {suc a2} {r2 = r2} refl tt refl rewrite +-identityʳ r2 = d2 , e2 , +-assoc a1 _ _ , refl , tt 
  lemma-ext {uni} {d1 = d1} {_} {bi} {d2 = .(suc (r1 + d1))} {e2 = e2} {a1 = a1} {suc r1} {zero} {r2 = r2} refl tt refl rewrite +-identityʳ a1 | +-identityʳ r2 = d1 , e2 , refl , refl , tt
  lemma-ext {q1' = uni} {q2' = bi} {r1 = suc r1} {suc a2} P@refl tt eq = lemma-ext P tt (suc-injective eq)
  lemma-ext {q1' = bi} {d1 = d1} {q2' = uni} {d2 = d2} {a1 = a1} {r1 = zero} {zero} {r2 = r2} tt refl eq rewrite +-identityʳ a1 | +-identityʳ r2 = d1 , d2 , refl , refl , tt
  lemma-ext {q1' = bi} {d1 = d1} {q2' = uni} {d2 = d2} {a1 = a1} {r1 = zero} {suc a2} {r2 = r2} tt refl eq rewrite +-identityʳ a1 | +-identityʳ r2 = d1 , d2 , refl , refl , tt
  lemma-ext {bi} {d1 = d1} {e1 = e1} {uni} {d2 = _} {a1 = a1} {suc r1} {zero} {r2 = r2} tt refl refl rewrite (+-identityʳ a1) = d1 , e1 , refl , +-assoc r2 _ _ , tt
  lemma-ext {q1' = bi} {q2' = uni} {r1 = suc r1} {suc a2} tt P@refl eq = lemma-ext tt P (suc-injective eq)
  lemma-ext {q1' = bi} {d1 = d1} {q2' = bi} {e2 = e2} {a1 = a1} {r2 = r2} tt tt eq rewrite +-identityʳ a1 | +-identityʳ r2 = d1 , e2 , refl , refl , tt

  module _ where
    module <:M = IsPreorder <:M-isPreorder
    module <: = IsPreorder <:-isPreorder

    completeness : ∀{qt rs k} → {is : Syntax k} → rs ⊢sub is :' qt → infer rs is <:M just qt
    completeness (const t) = <:M.reflexive refl
    completeness load = <:M.reflexive refl
    completeness store = <:M.reflexive refl
    completeness nop = <:M.reflexive refl
    completeness not = <:M.reflexive refl
    completeness and = <:M.reflexive refl
    completeness mul = <:M.reflexive refl
    completeness add = <:M.reflexive refl
    completeness {rs = rs} (br {l = l} x) with rs !! l
    completeness {rs = _} (br refl) | just u = <:M.reflexive refl 
    completeness {rs = rs} (brif {l = l} x) with rs !! l
    completeness {rs = _} (brif refl) | just u = <:M.reflexive refl 
    completeness {rs = rs} (block {is = is} (q , a , r) tis) with infer (r ∷ rs) is | completeness tis
    ... | just (q' , a' , r') | just<: qar'<:qar with (q' , a' , r') <:? (uni , a , r) | dec-true ((q' , a' , r') <:? (uni , a , r)) (<:.trans qar'<:qar (qt<:unit _ _))
    ... | yes qar'<:uniar | _ = <:M.reflexive refl
    completeness {rs = rs} (loop {is = is} (q , a , r) tis) with infer (a ∷ rs) is | completeness tis
    ... | just (q' , a' , r') | just<: qar'<:qar with (q' , a' , r') <:? (uni , a , r) | dec-true ((q' , a' , r') <:? (uni , a , r)) (<:.trans qar'<:qar (qt<:unit _ _))
    ... | yes qar'<:uniar | _ = <:M.reflexive refl
    completeness ε = <:M.reflexive refl
    completeness {rs = rs} (comp {is = is} {i = i} qis qi tis ti) with infer rs is | completeness tis
    ... | just (qis' , ais , ris) | just<: (<:-intro qis< (dis , eis , refl , eq , pis))  with infer rs i | completeness ti
    ... | just (qi' , ai , ri) | just<: (<:-intro qi< (di , ei , refl , refl , pi)) = just<: (<:-intro (⊓Q-mono qis< qi<) (lemma-ext pis pi eq)) where
      ⊓Q-mono : qis' ≤Q qis → qi' ≤Q qi → (qis' ⊓Q qi') ≤Q (qis ⊓Q qi)
      ⊓Q-mono bi≤q _ = bi≤q
      ⊓Q-mono uni≤uni bi≤q = bi≤q
      ⊓Q-mono uni≤uni uni≤uni = uni≤uni
    completeness (sub tis qt<:qt') = <:M.trans (completeness tis) (just<: qt<:qt')

module Semantics {_≟V_ : Decidable (_≡_ {A = Var})} where
  open import Data.Nat.Properties
  open Syntax
  open Typing
  open import Data.Vec as VecM
  open import Data.Empty
  open import Data.Sum
  open import Data.List.Properties using (++-identityʳ)

  ℤtoB : ℤ → Bool
  ℤtoB +0 = false
  ℤtoB _ = true

  Btoℤ : Bool → ℤ
  Btoℤ false = +0
  Btoℤ true = 1ℤ

  Store = Var → ℤ

  updateS : Var → ℤ → Store → Store -- store update
  updateS v z sto v' = if isYes (v ≟V v') then z else sto v'
  lookupS : Var → Store → ℤ -- store lookup
  lookupS v sto = sto v


  pattern success x = (just (inj₁ x))
  pattern jump x = (just (inj₂ x))
  pattern timeout = nothing
  OpeStk = Vec ℤ

  Cfg : ℕ → Set
  Cfg n = Store × OpeStk n

  BCfg : List ℕ → Set
  BCfg rs = Σ ℕ λ l → Σ ℕ λ u → Cfg u  × (rs !! l ≡ just u)

  injL : ∀ {l u} rs → rs !! l ≡ just u → Cfg u → BCfg rs
  injL {l = l} {u = u} rs p cfg = (l , u , cfg , p)

  take'' : ∀ {a d} r → a ≡ r + d → OpeStk a → OpeStk r
  take'' zero _ stk = []
  take'' (suc r) refl (x ∷ stk) = x ∷ take'' r refl stk

  drop'' : ∀ {a d} r → a ≡ r + d → OpeStk a → OpeStk d
  drop'' zero refl stk = stk
  drop'' (suc r) refl (x ∷ stk) = drop'' r refl stk

  module Untyped where

    open import Data.String
    UCfg : Set
    UCfg = Store × List ℤ

    UBCfg = ℕ × UCfg

    data RuntimeError : Set where
      StackUnderflow : RuntimeError
      BranchingOutside : RuntimeError

    takeMaybe : ℕ → List ℤ → Maybe (List ℤ)
    takeMaybe zero zs = just []
    takeMaybe (suc n) [] = nothing
    takeMaybe (suc n) (z ∷ zs) = case takeMaybe n zs of λ where
      (just zs') → just (z ∷ zs')
      nothing → nothing

    branchHelper : (rs : List ℕ) → (l : ℕ) → UCfg → Maybe (UCfg ⊎ UBCfg) ⊎ RuntimeError
    branchHelper rs l (sto , stk) = case rs !! l of λ where
      (just a) → inj₁ (jump (l , sto , ListM.take a stk))
      nothing → inj₂ BranchingOutside

    ⦅_⦆ : {k : Kind} → Syntax k → List ℕ → UCfg → ℕ → Maybe (UCfg ⊎ UBCfg) ⊎ RuntimeError
    ⦅ const t z ⦆ rs (sto , stk) _ = inj₁ (success (sto , z ∷ stk))
    ⦅ load v ⦆ rs (sto , stk) _ =  inj₁ (success (sto , lookupS v sto ∷ stk))
    ⦅ store v ⦆ rs (sto , z ∷ stk) _ = inj₁ (success (updateS v z sto , stk))
    ⦅ add ⦆ rs (sto , z1 ∷ z2 ∷ stk) _ = inj₁ (success (sto , z1  Int.+ z2 ∷ stk))
    ⦅ mul ⦆ rs (sto , z1 ∷ z2 ∷ stk) _ = inj₁ (success (sto , z1 Int.* z2 ∷ stk))
    ⦅ and ⦆ rs (sto , z1 ∷ z2 ∷ stk) _ = inj₁ (success (sto , Btoℤ ((ℤtoB z1) ∧ (ℤtoB z2)) ∷ stk))
    ⦅ not ⦆ rs (sto , z1 ∷ stk) _ = inj₁ (success (sto , Btoℤ (BoolM.not (ℤtoB z1)) ∷ stk))
    ⦅ nop ⦆ rs (sto , stk) _ = inj₁ (success (sto , stk))
    ⦅ br l ⦆ rs (sto , stk) _ = case rs !! l of λ where
      (just a) → inj₁ (jump (l , sto , ListM.take a stk))
      nothing → inj₂ BranchingOutside
    ⦅ brif l ⦆ rs (sto , z ∷ stk) _ = if ℤtoB z
      then (case rs !! l of λ where
        (just a) → inj₁ (jump (l , sto , ListM.take a stk))
        nothing → inj₂ BranchingOutside)
      else inj₁ (success (sto , stk))
    ⦅ block (a , r) is ⦆ rs (sto , stk) n =
      ( case ⦅ is ⦆ (r ∷ rs) (sto , ListM.take a stk) n of λ
      { (inj₁ (success (sto' , stk'))) → inj₁ (success (sto' , stk' ListM.++ ListM.drop a stk))
      ; (inj₁ (jump (zero , sto' , stk'))) → inj₁ (success (sto' , stk' ListM.++ ListM.drop a stk))
      ; (inj₁ (jump (suc l , sto' , stk'))) → inj₁ (jump (l , sto' , stk'))
      ; (inj₁ timeout) → inj₁ timeout
      ; (inj₂ e) → inj₂ e
      })
    ⦅ loop (a , r) is ⦆ rs (sto , stk) (suc n) =
      ( case ⦅ is ⦆ (a ∷ rs) (sto , ListM.take a stk) (suc n) of λ
      { (inj₁ (success (sto' , stk'))) → inj₁ (success (sto' , stk' ListM.++ ListM.drop a stk))
      ; (inj₁ (jump (zero , sto' , stk'))) → ⦅ loop (a , r) is ⦆ rs (sto' , stk' ListM.++ ListM.drop a stk) n
      ; (inj₁ (jump (suc l , sto' , stk'))) → inj₁ (jump (l , sto' , stk'))
      ; (inj₁ timeout) → inj₁ timeout
      ; (inj₂ e) → (inj₂ e)
      })
    ⦅ loop (a , r) is ⦆ rs (sto , stk) zero =
      ( case ⦅ is ⦆ (a ∷ rs) (sto , ListM.take a stk) zero of λ
      { (inj₁ (success (sto' , stk'))) → inj₁ (success (sto' , stk' ListM.++ ListM.drop a stk))
      ; (inj₁ (jump (zero , sto' , stk'))) → inj₁ timeout
      ; (inj₁ (jump (suc l , sto' , stk'))) → inj₁ (jump (l , sto' , stk'))
      ; (inj₁ timeout) → inj₁ timeout
      ; (inj₂ e) → (inj₂ e)
      })
    ⦅ ε ⦆ rs (sto , stk) _ = inj₁ (success (sto , stk))
    ⦅ is ∙ i ⦆ rs (sto , stk) n = case ⦅ is ⦆ rs (sto , stk) n of λ
      { (inj₁ (success (sto' , stk'))) → ⦅ i ⦆ rs (sto' , stk') n
      ; (inj₁ (jump (l , sto' , stk'))) → inj₁ (jump (l , sto' , stk'))
      ; (inj₁ timeout) → inj₁ timeout
      ; (inj₂ e) → (inj₂ e)
      }
    ⦅ _ ⦆ _ _ _ = inj₂ StackUnderflow

  open Untyped
  stripTypeCfg : ∀ {r}→ Cfg r → UCfg
  stripTypeCfg (sto , stk) = (sto , VecM.toList stk)
  
  stripTypeBCfg : ∀ {rs} → BCfg rs → UBCfg
  stripTypeBCfg (l , u , cfg , p) = (l , stripTypeCfg cfg)



  vec-list-take'' : ∀{a} u {d} (p : a ≡ u + d) xs → ListM.take u (toList xs) ≡ toList (take'' u p xs)
  vec-list-take'' zero _ xs = refl
  vec-list-take'' (suc u) refl (x ∷ xs) = cong (x ∷_) (vec-list-take'' u refl xs)

  vec-list-take-drop'' : ∀{a} u {d} (p : a ≡ u + d) xs → toList (take'' u p xs VecM.++ drop'' u p xs) ≡ toList xs
  vec-list-take-drop'' zero refl xs = refl
  vec-list-take-drop'' (suc u) refl (x ∷ xs) = cong (x ∷_) (vec-list-take-drop'' u refl xs)

  vec-list-drop'' : ∀{a} u {d} (p : a ≡ u + d) xs → ListM.drop u (toList xs) ≡ toList (drop'' u p xs)
  vec-list-drop'' zero refl xs = refl
  vec-list-drop'' (suc n) refl (x ∷ xs) =   (vec-list-drop'' n refl xs)

  vec-list-take-drop2'' : ∀{u n} a {d} (p : u ≡ a + d) (tstk' : Vec ℤ n) tstk → (toList tstk' ListM.++ ListM.drop a (toList tstk)) ≡ toList (tstk' VecM.++ drop'' a p tstk)
  vec-list-take-drop2'' {n = zero} a refl [] tstk = vec-list-drop'' a refl tstk
  vec-list-take-drop2'' {n = suc n} a refl (x ∷ tstk') tstk = cong (x ∷_) (vec-list-take-drop2'' a refl tstk' tstk) 

  lemma<ᵇ : ∀ r d → (r Nat.<ᵇ suc (r + d)) ≡ true
  lemma<ᵇ zero d = refl
  lemma<ᵇ (suc r) d = lemma<ᵇ r d

  lemma≤ᵇ : ∀ r d → (r Nat.≤ᵇ r + d) ≡ true
  lemma≤ᵇ zero d = refl
  lemma≤ᵇ (suc r) d = lemma<ᵇ r d

  lemma+∸ : ∀ (a d d' : ℕ) → a + d + d' ∸ a ≡ d + d'
  lemma+∸ a d d' rewrite +-assoc a d d' = 
    begin
      (a + (d + d') ∸ a) ≡⟨ (m+n∸m≡n a (d + d')) ⟩
      (d + d') ∎
    where open ≡-Reasoning

  module NRSemantics where
    NR : Q → ℕ → Set
    NR uni r = Cfg r
    NR bi r = ⊥
 
    ⟦_⟧qt : Q × ℕ × ℕ → List ℕ → Set
    ⟦ (q , a , r) ⟧qt rs = Cfg a → Maybe (NR q r ⊎ BCfg rs)
    ⟦_⟧<: : ∀ {qt qt'} → qt <: qt' → ∀ {rs} → ⟦ qt ⟧qt rs → ⟦ qt' ⟧qt rs
    ⟦ <:-intro {t = a , r} bi≤q (d , e , refl , _) ⟧<: c (sto , stk) = case c (sto , take'' a refl stk) of λ where
      (jump x) → jump x
      timeout → timeout
    ⟦ <:-intro {t = a , r} uni≤uni (d , e , refl , refl , refl) ⟧<: c (sto , stk) = case c (sto , take'' a refl stk) of λ where
      timeout → timeout
      (jump x) → jump x
      (success (sto' , stk')) → success (sto' , stk' VecM.++ drop'' a refl stk)

    ⟦_⟧ : {k : Kind} → {i : Syntax k} → ∀{rs qt} → rs ⊢sub i :' qt → ℕ → ⟦ qt ⟧qt rs
    ⟦ const {z = z} t ⟧ n (sto , stk) = success (sto , z ∷ stk)
    ⟦ load {v = v} ⟧ n (sto , stk) = success (sto , (lookupS v sto) ∷ stk)
    ⟦ store {v = v} ⟧ n (sto , z ∷ stk) = success (updateS v z sto , stk)
    ⟦ nop ⟧ n (sto , stk) = success (sto , stk)
    ⟦ not ⟧ n (sto , (z ∷ stk)) = success (sto , Btoℤ (BoolM.not (ℤtoB z)) ∷ stk)
    ⟦ and ⟧ n (sto , (z1 ∷ z2 ∷ stk)) = success (sto , Btoℤ ((ℤtoB z1) ∧ (ℤtoB z2)) ∷ stk)
    ⟦ mul ⟧ n (sto , (z1 ∷ z2 ∷ stk)) = success (sto , z1 Int.* z2 ∷ stk)
    ⟦ add ⟧ n (sto , (z1 ∷ z2 ∷ stk)) = success (sto , z1 Int.+ z2 ∷ stk)
    ⟦_⟧ {rs = rs} (br {u = u} eq) n (sto , stk) = jump (injL rs eq (sto , stk))
    ⟦_⟧ {rs = rs} (brif {u = u} eq) n (sto , z ∷ stk) = (if ℤtoB z then jump (injL rs eq (sto , stk)) else success (sto , stk)) 
    ⟦ block (uni , a , r) tis ⟧ n (sto , stk) = case ⟦ tis ⟧ n (sto , stk) of λ where
            timeout → timeout
            (success (sto' , stk')) → success (sto' , stk')
            (jump (zero , l , (sto' , stk') , refl)) → success (sto' , stk')
            (jump (suc l , p)) → jump (l , p)
    ⟦ block (bi , a , r) tis ⟧ n (sto , stk) = case ⟦ tis ⟧ n (sto , stk) of λ where
            timeout → timeout
            (jump (zero , l , (sto' , stk') , refl)) → success (sto' , (stk'))
            (jump (suc l , p)) → jump (l , p)
    ⟦ loop (uni , a , r) tis ⟧ (suc n) (sto , stk) = case ⟦ tis ⟧ (suc n) (sto , stk) of λ where
           timeout → timeout
           (success (sto' , stk')) → success (sto' , stk')
           (jump (zero , l , (sto' , stk') , refl)) →  ⟦ (loop (uni , a , r) tis) ⟧ n (sto' , stk')
           (jump (suc l , p)) → jump (l , p) 
    ⟦ loop (bi , a , r) tis ⟧ (suc n) (sto , stk) = case ⟦ tis ⟧ (suc n) (sto , stk) of λ where
           timeout → timeout
           (jump (zero , l , (sto' , stk') , refl)) →  ⟦ (loop (bi , a , r) tis) ⟧ n (sto' , stk')
           (jump (suc l , p)) → jump (l , p) 
    ⟦ loop (uni , a , r) tis ⟧ zero (sto , stk) = case ⟦ tis ⟧ zero (sto , stk) of λ where
           timeout → timeout
           (success (sto' , stk')) → success (sto' , stk')
           (jump (zero , l , (sto' , stk') , refl)) → timeout 
           (jump (suc l , p)) → jump (l , p) 
    ⟦ loop (bi , a , r) tis ⟧ zero (sto , stk) = case ⟦ tis ⟧ zero (sto , stk) of λ where
           timeout → timeout
           (jump (zero , l , (sto' , stk') , refl)) → timeout
           (jump (suc l , p)) → jump (l , p) 

    ⟦ ε ⟧ n (sto , stk) = success (sto , stk)
    ⟦ comp {a = a} {r = r} uni qi tis ti ⟧ n (sto , stk) = case (⟦ tis ⟧ n (sto , stk)) of λ where
      timeout → timeout
      (jump outer) → jump outer
      (success cfg') → ⟦ ti ⟧ n cfg'
    ⟦ comp {a = a} {r = r} bi qi tis ti ⟧ n (sto , stk) = case ⟦ tis ⟧ n (sto , stk) of λ where
      timeout → timeout
      (jump outer) → jump outer
    ⟦_⟧ {rs = rs} (sub ti qt<:qt') n (sto , stk') = ⟦ qt<:qt' ⟧<: {rs = rs}  (⟦ ti ⟧ n) (sto , stk')

      
    stripType : ∀ q r rs → Maybe (NR q r ⊎ BCfg rs) → Maybe (UCfg ⊎ UBCfg) ⊎ RuntimeError
    stripType uni _ _ (success (sto , stk)) = inj₁ (success (sto , VecM.toList stk))
    stripType _ _ rs (jump bcfg) = inj₁ (jump (stripTypeBCfg {rs} bcfg))
    stripType _ _ _ timeout = inj₁ timeout

    feedPassive : ∀ {d q r rs} → (pstk : Vec ℤ d) → Maybe (NR q r ⊎ BCfg rs) → Maybe (NR q (r + d) ⊎ BCfg rs)
    feedPassive {q = uni} pstk (success (sto , tstk)) = success (sto , tstk VecM.++ pstk)
    feedPassive pstk (jump x) = jump x
    feedPassive pstk timeout = timeout

    infer-sem : ∀{k} → (c : Syntax k) → {qt : Q × ℕ × ℕ} → ∀ rs → (rs ⊢sub c :' qt) → ℕ → ⟦ qt ⟧qt rs
    infer-sem c rs tc with TypeInference.infer rs c | inspect (TypeInference.infer rs) c | TypeInference.completeness tc
    ... | just qt0 | ≡.[ eq ] | just<: qt0<:qt = ⟦ sub (TypeInference.soundness c eq) qt0<:qt ⟧


