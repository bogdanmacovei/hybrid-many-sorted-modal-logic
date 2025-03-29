abbrev Agent := String 

inductive Message (σ : Nat) where
| empty : Message σ
| text : String → Message σ
| agent : Agent → Message σ
| symmetricKey : Agent → Agent → Message σ → Message σ
| publicKey : Agent → Message σ
| secretKey : Agent → Message σ
| encrypt : Message σ → Message σ → Message σ
| concat : Message σ → Message σ → Message σ
deriving Repr, BEq

notation " #μ " i => Message.empty i
notation " # " t " # " => Message.text t
notation " pk( " i " ) " => Message.publicKey i
notation " sk( " i " ) " => Message.secretKey i
notation " ⦃| " m " |⦄ " k  => Message.encrypt m k
notation " ag( " i " ) " => Message.agent i 
notation " text( " t " ) " => Message.text t 
notation m₁ " ‖ " m₂ => Message.concat m₁ m₂

inductive Action (σ : Nat) where 
| send : Agent → Agent → Message σ → Action σ 
| recv : Agent → Message σ → Action σ 
| comp : Action σ → Action σ → Action σ 
| reun : Action σ → Action σ → Action σ 
deriving Repr, BEq 

notation " send " i ", " j " ( " μ " ) " => Action.send i j μ 
notation " recv " i " ( " μ " ) " => Action.recv i μ 
notation α₁ " ; " α₂ => Action.comp α₁ α₂ 
notation α₁ " ∪∪ " α₂ => Action.reun α₁ α₂ 

inductive State (σ : Nat) where 
| explicit : Agent → Message σ → State σ 
| add : State σ → State σ → State σ
deriving Repr, BEq 

notation a " ▷ " μ => State.explicit a μ 
notation γ₁ " ⊔ " γ₂ => State.add γ₁ γ₂ 

inductive Formula (σ : Nat) where 
| atom : Fin σ → Formula σ
| true : Formula σ 
| neg : Formula σ → Formula σ 
| imp : Formula σ → Formula σ → Formula σ 
| believe : Agent → Formula σ → Formula σ 
| explicit : Agent → Message σ → Formula σ
| state2form : State σ → Formula σ 
| state : Formula σ → Formula σ 
| action : Action σ → Formula σ → Formula σ 
deriving Repr, BEq 

notation " #ϕ " i => Formula.atom i
notation " ⊤ " => Formula.true 
notation " ~ " φ => Formula.neg φ
notation " ⊥ " => (~⊤)
notation φ " ⟶ " ψ => Formula.imp φ ψ
notation φ " ⋁ " ψ => ((~φ) ⟶ ψ)
notation φ " ⋀ " ψ => ~((~φ) ⋁ (~ψ))
notation " 𝔹 " i " , " φ => Formula.believe i φ
notation " 𝕂 " i " , " φ => (𝔹 i, φ) ⋀ φ 
notation " 𝕏 " i " , " m => Formula.explicit i m
notation " ι " γ => Formula.state2form γ 
notation " ⟨ " γ " ⟩ " => Formula.state γ 
notation " [ " α " ] " φ => Formula.action α φ 

inductive Proof {σ : Nat} : Context σ → Formula σ → Prop  
-- Hilbert basic 
| ax { Γ } { p : Formula σ } (h : Γ.Mem p) : Proof Γ p 
| pl₁ { Γ } { p q : Formula σ } : Proof Γ (p ⟶ (q ⟶ p))
| pl₂ { Γ } { p q r : Formula σ } : Proof Γ $ (p ⟶ (q ⟶ r)) ⟶ ((p ⟶ q) ⟶ (p ⟶ r)) 
| pl₃ { Γ } { p q : Formula σ } : Proof Γ $ ((~p) ⟶ ~q) ⟶ (q ⟶ p)
-- K axiom for programs
| Kα { Γ } { φ ψ : Formula σ } { α : Action σ } : Proof Γ $ ([α](φ ⟶ ψ)) ⟶ (([α]φ) ⟶ ([α]ψ))
-- Belief 
| K𝔹 { Γ } { φ ψ : Formula σ } { a : Agent } : Proof Γ $ (𝔹 a, (φ ⟶ ψ)) ⟶ ((𝔹 a, φ) ⟶ (𝔹 a, ψ))
| D { Γ } { φ : Formula σ } {a : Agent} : Proof Γ $ (𝔹 a, φ) ⟶ ~(𝔹 a, (~φ))
| _4 { Γ } { φ : Formula σ } {a : Agent} : Proof Γ $ (𝔹 a, φ) ⟶ (𝔹 a, (𝔹 a, φ)) 
| _5 { Γ } { φ : Formula σ } {a : Agent} : Proof Γ $ (~(𝔹 a, φ)) ⟶ (𝔹 a, (~(𝔹 a, φ))) 
-- Deduction rules 
| MP { Γ } { p q : Formula σ } (hpq : Proof Γ $ p ⟶ q) (hp : Proof Γ p) : Proof Γ q
| NEC𝔹 { Γ } { φ : Formula σ } { a : Agent } (hφ : Proof Γ φ) : Proof Γ $ 𝔹 a, φ 
| NECα { Γ } { φ : Formula σ } { α : Action σ } (hφ : Proof Γ φ) : Proof Γ $ [α]φ 
-- Actions 
| Acomp_left { Γ } {α₁ α₂ : Action σ } { φ : Formula σ } : Proof Γ $ ([α₁ ; α₂]φ) ⟶ [α₁]([α₂]φ)
| Acopm_right { Γ } {α₁ α₂ : Action σ } { φ : Formula σ } : Proof Γ $ [α₁]([α₂]φ) ⟶ ([α₁ ; α₂]φ)
-- States 
| St₁_left { Γ } { γ₁ γ₂ : State σ } { a : Agent } { m : Message σ } : Proof Γ $ (ι (γ₁ ⊔ ((a ▷ m) ⊔ γ₂))) ⟶ ι ((a ▷ m) ⊔ (γ₁ ⊔ γ₂))
| St₁_right { Γ } { γ₁ γ₂ : State σ } { a : Agent } { m : Message σ } : Proof Γ $ (ι ((a ▷ m) ⊔ (γ₁ ⊔ γ₂))) ⟶  ι (γ₁ ⊔ ((a ▷ m) ⊔ γ₂))
| St₂_left { Γ } { γ : State σ } { a : Agent } { m : Message σ } : Proof Γ $ (ι ((a ▷ m) ⊔ ((a ▷ m) ⊔ γ))) ⟶  ι ((a ▷ m) ⊔ γ)
| St₂_right { Γ } { γ : State σ } { a : Agent } { m : Message σ } : Proof Γ $ (ι ((a ▷ m) ⊔ γ)) ⟶ ι ((a ▷ m) ⊔ ((a ▷ m) ⊔ γ))
| St₃ { Γ } { γ : State σ } { a : Agent } { m : Message σ } : Proof Γ $ (ι ((a ▷ m) ⊔ γ)) ⟶ 𝕏 a, m
-- theorems
| St₁_left' { Γ } { γ₁ γ₂ : State σ } { a : Agent } { m : Message σ } : Proof Γ $ ⟨ι (γ₁ ⊔ ((a ▷ m) ⊔ γ₂))⟩ ⟶  ⟨ι ((a ▷ m) ⊔ (γ₁ ⊔ γ₂))⟩
| St₁_right' { Γ } { γ₁ γ₂ : State σ } { a : Agent } { m : Message σ } : Proof Γ $ ⟨ι ((a ▷ m) ⊔ (γ₁ ⊔ γ₂))⟩ ⟶  ⟨ι (γ₁ ⊔ ((a ▷ m) ⊔ γ₂))⟩
| St₂_left' { Γ } { γ : State σ } { a : Agent } { m : Message σ } : Proof Γ $ ⟨ι ((a ▷ m) ⊔ ((a ▷ m) ⊔ γ))⟩ ⟶  ⟨ι ((a ▷ m) ⊔ γ)⟩
| St₂_right' { Γ } { γ : State σ } { a : Agent } { m : Message σ } : Proof Γ $ ⟨ι ((a ▷ m) ⊔ γ)⟩ ⟶ ⟨ι ((a ▷ m) ⊔ ((a ▷ m) ⊔ γ))⟩
| St₃' { Γ } { γ : State σ } { a : Agent } { m : Message σ } : Proof Γ $ ⟨ι ((a ▷ m) ⊔ γ)⟩ ⟶ ⟨𝕏 a, m⟩

notation Γ " ⊢ " φ => Proof Γ φ 