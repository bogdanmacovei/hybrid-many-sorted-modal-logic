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

/-
  **PROTOCOLS**
-/

open Formula 
open Proof 

inductive ProtocolProof { σ : Nat } : Context σ → Formula σ → Prop 
-- an extension of standard proofs  
| base { Γ } { φ } (proof : Proof Γ φ) : ProtocolProof Γ φ 
-- messages  
| X₁_left { Γ } { a : Agent } { m₁ m₂ : Message σ } : ProtocolProof Γ $ (𝕏 a, (m₁.concat m₂)) ⟶ ((𝕏 a, m₁) ⋀ (𝕏 a, m₂))
| X₁_right { Γ } { a : Agent }{ m₁ m₂ : Message σ } : ProtocolProof Γ $ ((𝕏 a, m₁) ⋀ (𝕏 a, m₂)) ⟶ (𝕏 a, (m₁.concat m₂))
| X₂_left { Γ } { a b : Agent } { k : Message σ } : ProtocolProof Γ $ (𝕏 a, (Message.symmetricKey a b k)) ⟶ (𝕏 b, (Message.symmetricKey b a k))
| X₂_right { Γ } { a b : Agent } { k : Message σ } : ProtocolProof Γ $ (𝕏 b, (Message.symmetricKey b a k)) ⟶ (𝕏 a, (Message.symmetricKey a b k))
| X₃ { Γ } { a b : Agent } { m : Message σ } : ProtocolProof Γ $ ((𝕏 a, ⦃|m|⦄ pk(b)) ⋀ (𝕏 a, sk(b))) ⟶ (𝕏 a, m)
| X₄ { Γ } { a b : Agent } { m : Message σ } : ProtocolProof Γ $ ((𝕏 a, ⦃|m|⦄ sk(b)) ⋀ (𝕏 a, pk(b))) ⟶ (𝕏 a, m)
| X₅ { Γ } { a : Agent } { m₁ m₂ : Message σ } : ProtocolProof Γ $ ((𝕏 a, m₁) ⋀ (𝕏 a, m₂)) ⟶ 𝕏 a, ⦃|m₁|⦄m₂ 
| X₆ { Γ } { a b : Agent } { m k : Message σ } : ProtocolProof Γ $ ((𝕏 a, ⦃|m|⦄ (Message.symmetricKey a b k)) ⋀ (𝕏 a, (Message.symmetricKey a b k))) ⟶ (𝕏 a, m)
| X₇ { Γ } { a : Agent } : ProtocolProof Γ $ (𝕏 a, ag(a))
-- protocol general hypotheses
| H₁ { Γ } { a b e : Agent } {m : Message σ } { γ : State σ } : ProtocolProof Γ $ ⟨ ι ((a ▷ m) ⊔ γ) ⟩ ⟶ [send a,b(⦃| ag(a) ‖  m |⦄pk(b))]⟨ ι ((e ▷ m) ⊔ ((a ▷ m) ⊔ γ)) ⟩ 
| H₂ { Γ } { a b e : Agent } {m : Message σ } { γ : State σ } : ProtocolProof Γ $ ⟨ ι ((e ▷ m) ⊔ γ) ⟩ ⟶ [recv a(⦃| ag(b) ‖ m |⦄pk(a))]⟨ ι ((a ▷ m) ⊔ ((e ▷ m) ⊔ γ)) ⟩  

notation Γ " ⊢ₚ " φ => ProtocolProof Γ φ 

inductive OSSProof { σ : Nat } : Context σ → Formula σ → Prop 
| base { Γ } { φ } (proof : ProtocolProof Γ φ) : OSSProof Γ φ 
| S₁ { Γ } {a b : Agent } { m : Message σ } { γ : State σ } : OSSProof Γ $ ⟨ ι ((a ▷ m) ⊔ γ) ⟩ ⟶ [send a,b(⦃| ag(a) ‖  m |⦄pk(b))]𝔹 a, ⟨ 𝕏 b, m ⟩ 
| S₁' { Γ } {a b : Agent } { m : Message σ } { γ : State σ } { α : Action σ } : OSSProof Γ $ ⟨ ι ((a ▷ m) ⊔ γ) ⟩ ⟶ [(send a,b(⦃| ag(a) ‖  m |⦄pk(b))) ; α]𝔹 a, ⟨ 𝕏 b, m ⟩ 
| S₂ { Γ } { a b : Agent } { m : Message σ } { γ : State σ } : OSSProof Γ $ ⟨ ι γ ⟩ ⟶ [recv b(⦃| ag(a) ‖  m |⦄pk(b))]𝔹 b, ⟨ 𝕏 a, m ⟩ 
| S₂' { Γ } { a b : Agent } { m : Message σ } { α : Action σ } : OSSProof Γ $ [(recv b(⦃| ag(a) ‖  m |⦄pk(b))) ; α]𝔹 b, ⟨ 𝕏 a, m ⟩ 
-- added to simplify 
| MP { Γ } { p q : Formula σ } (hpq : OSSProof Γ $ p ⟶ q) (hp : OSSProof Γ p) : OSSProof Γ q
| NECα { Γ } { φ : Formula σ } { α : Action σ } (hφ : OSSProof Γ φ) : OSSProof Γ $ [α]φ 

notation Γ " ⊢ₒₛₛ " φ => OSSProof Γ φ 


def γᵢₙᵢₜ {σ : Nat} {i r : Agent} : State σ := (i ▷ pk(i)) ⊔ (i ▷ sk(i)) ⊔ (i ▷ pk(i)) ⊔ (r ▷ sk(r))

@[simp]
theorem pl_transitivity {σ : Nat} {p q r : Formula σ} { Γ : Context σ } : 
  (Γ ⊢ₒₛₛ (p ⟶ q)) → 
  (Γ ⊢ₒₛₛ (q ⟶ r)) → 
  (Γ ⊢ₒₛₛ (p ⟶ r)) := by 
  intros hpq hqr
  have h₁ : Γ ⊢ₒₛₛ (p ⟶ q ⟶ r) :=
    OSSProof.MP
      (OSSProof.base (ProtocolProof.base Proof.pl₁))
      hqr
  have h₂ : Γ ⊢ₒₛₛ ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ (p ⟶ r)) :=
    OSSProof.base (ProtocolProof.base Proof.pl₂)
  have h₃ : Γ ⊢ₒₛₛ ((p ⟶ q) ⟶ (p ⟶ r)) :=
    OSSProof.MP h₂ h₁
  exact OSSProof.MP h₃ hpq

@[simp]
theorem dl_th_1 {σ : Nat} { p q r : Formula σ } { α : Action σ } { Γ : Context σ } : 
  (Γ ⊢ₒₛₛ (p ⟶ ([α]q))) → 
  (Γ ⊢ₒₛₛ (p ⟶ ([α]r))) → 
  (Γ ⊢ₒₛₛ (p ⟶ ([α](q ⋀ r)))) := by 
  admit 


@[simp]
theorem dl_th_2 {σ : Nat} { p q r : Formula σ } { α β : Action σ } { Γ : Context σ } : 
  (Γ ⊢ₒₛₛ (p ⟶ ([α][β](q ⋀ r)))) → 
  (Γ ⊢ₒₛₛ (p ⟶ ([α][β]r))) := by 
  intros h

  have prop_formula : Γ ⊢ ((q ⋀ r) ⟶ r) := by
    admit 
  have nec_formula : Γ ⊢ [α][β]((q ⋀ r) ⟶ r) := Proof.NECα (Proof.NECα prop_formula)
  have nec_formula' : Γ ⊢ₒₛₛ [α][β]((q ⋀ r) ⟶ r) :=
    OSSProof.base (ProtocolProof.base nec_formula)
  admit 

@[simp]
theorem dl_th_3 {σ : Nat} { p q : Formula σ } { α β : Action σ } { Γ : Context σ } : 
  (Γ ⊢ₒₛₛ (p ⟶ ([α]([β]q)))) → 
  (Γ ⊢ₒₛₛ (p ⟶ ([α ; β]q))) := by 
  admit 

@[simp]
theorem edl_th_1 {σ : Nat} { p q : Formula σ } { α β : Action σ } {a : Agent} { Γ : Context σ } : 
  (Γ ⊢ₒₛₛ (p ⟶ ([α][β] (𝔹 a, q)))) → 
  (Γ ⊢ₒₛₛ (p ⟶ ([α][β] (𝕂 a, q)))) := by 
  intros h
  unfold 
  admit 
  have htriv : Γ ⊢ₒₛₛ (p ⟶ [α][β]q) :=
    let h₁ : Γ ⊢ₒₛₛ ((𝔹 a, q) ⟶ q) := OSSProof.base (Proof.ax (List.Mem.head _))
    let h₂ := OSSProof.base (Proof.NECα (Proof.NECα h₁))
    pl_transitivity h h₂
  exact htriv


theorem oss { σ : Nat } { Γ : Context σ } { i r e : Agent } { nᵢ : Message σ } : 
  Γ ⊢ₒₛₛ ((⟨ ι ((i ▷ nᵢ) ⊔ (@γᵢₙᵢₜ σ i r)) ⟩) 
    ⟶ ([(send i, r(⦃| ag(i) ‖ nᵢ |⦄pk(r))) ; (recv r(⦃| ag(i) ‖ nᵢ |⦄pk(r)))](𝕂 r, ⟨ 𝕏 i, nᵢ ⟩))) :=  by 
  have S₁ : Γ ⊢ₒₛₛ ⟨ ι ((i ▷ nᵢ) ⊔ (@γᵢₙᵢₜ σ i r)) ⟩ ⟶ [send i,r(⦃| ag(i) ‖  nᵢ |⦄pk(r))]𝔹 i, ⟨ 𝕏 r, nᵢ ⟩ 
    := OSSProof.S₁ 
  have H₁ : Γ ⊢ₒₛₛ ⟨ ι ((i ▷ nᵢ) ⊔ (@γᵢₙᵢₜ σ i r)) ⟩ ⟶ [send i,r(⦃| ag(i) ‖  nᵢ |⦄pk(r))]⟨ ι ((e ▷ nᵢ) ⊔ ((i ▷ nᵢ) ⊔ (@γᵢₙᵢₜ σ i r))) ⟩ 
    := OSSProof.base $ ProtocolProof.H₁ 
  have hl₀ :  Γ ⊢ₒₛₛ ⟨ ι ((i ▷ nᵢ) ⊔ (@γᵢₙᵢₜ σ i r)) ⟩ ⟶ [send i,r(⦃| ag(i) ‖  nᵢ |⦄pk(r))]((𝔹 i, ⟨ 𝕏 r, nᵢ ⟩) ⋀ (⟨ ι ((e ▷ nᵢ) ⊔ ((i ▷ nᵢ) ⊔ (@γᵢₙᵢₜ σ i r))) ⟩ ))
    := dl_th_1 S₁ H₁ 
  have γ₁ : State σ := ((i ▷ nᵢ) ⊔ (@γᵢₙᵢₜ σ i r))
  have H₂ : Γ ⊢ₒₛₛ ⟨ ι ((e ▷ nᵢ) ⊔ ((i ▷ nᵢ) ⊔ (@γᵢₙᵢₜ σ i r))) ⟩ ⟶ [recv r(⦃| ag(i) ‖ nᵢ |⦄pk(r))]⟨ ι ((r ▷ nᵢ) ⊔ ((e ▷ nᵢ) ⊔ ((i ▷ nᵢ) ⊔ (@γᵢₙᵢₜ σ i r)))) ⟩ 
    := OSSProof.base $ ProtocolProof.H₂ 
  have S₂ : Γ ⊢ₒₛₛ ⟨ ι ((e ▷ nᵢ) ⊔ ((i ▷ nᵢ) ⊔ (@γᵢₙᵢₜ σ i r))) ⟩ ⟶ [recv r(⦃| ag(i) ‖ nᵢ |⦄pk(r))](𝔹 r, ⟨ 𝕏 i, nᵢ ⟩) 
    := OSSProof.S₂ 
  have hl₁ : Γ ⊢ₒₛₛ ⟨ ι ((e ▷ nᵢ) ⊔ ((i ▷ nᵢ) ⊔ (@γᵢₙᵢₜ σ i r))) ⟩ ⟶ [recv r(⦃| ag(i) ‖ nᵢ |⦄pk(r))]((⟨ ι ((r ▷ nᵢ) ⊔ ((e ▷ nᵢ) ⊔ ((i ▷ nᵢ) ⊔ (@γᵢₙᵢₜ σ i r))))⟩) ⋀ (𝔹 r, ⟨ 𝕏 i, nᵢ ⟩))
    := dl_th_1 H₂ S₂ 
  have hl₂_K : Γ ⊢ₒₛₛ [send i,r(⦃| ag(i) ‖  nᵢ |⦄pk(r))] (⟨ ι ((e ▷ nᵢ) ⊔ ((i ▷ nᵢ) ⊔ (@γᵢₙᵢₜ σ i r))) ⟩ ⟶ [recv r(⦃| ag(i) ‖ nᵢ |⦄pk(r))]((⟨ ι ((r ▷ nᵢ) ⊔ ((e ▷ nᵢ) ⊔ ((i ▷ nᵢ) ⊔ (@γᵢₙᵢₜ σ i r))))⟩) ⋀ (𝔹 r, ⟨ 𝕏 i, nᵢ ⟩)))
    := OSSProof.NECα hl₁
  have hl₃ : Γ ⊢ₒₛₛ ([send i,r(⦃| ag(i) ‖  nᵢ |⦄pk(r))](⟨ ι ((e ▷ nᵢ) ⊔ ((i ▷ nᵢ) ⊔ (@γᵢₙᵢₜ σ i r))) ⟩)) ⟶ ([send i,r(⦃| ag(i) ‖  nᵢ |⦄pk(r))]( [recv r(⦃| ag(i) ‖ nᵢ |⦄pk(r))]((⟨ ι ((r ▷ nᵢ) ⊔ ((e ▷ nᵢ) ⊔ ((i ▷ nᵢ) ⊔ (@γᵢₙᵢₜ σ i r))))⟩) ⋀ (𝔹 r, ⟨ 𝕏 i, nᵢ ⟩)))) 
    := OSSProof.MP (OSSProof.base (ProtocolProof.base Proof.Kα)) hl₂_K 
  have hl₄ : Γ ⊢ₒₛₛ  ⟨ ι ((i ▷ nᵢ) ⊔ (@γᵢₙᵢₜ σ i r)) ⟩ ⟶ ([send i,r(⦃| ag(i) ‖  nᵢ |⦄pk(r))]( [recv r(⦃| ag(i) ‖ nᵢ |⦄pk(r))]((⟨ ι ((r ▷ nᵢ) ⊔ ((e ▷ nᵢ) ⊔ ((i ▷ nᵢ) ⊔ (@γᵢₙᵢₜ σ i r))))⟩) ⋀ (𝔹 r, ⟨ 𝕏 i, nᵢ ⟩)))) 
    := pl_transitivity H₁ hl₃ 
  have st₃ : Γ ⊢ₒₛₛ (⟨ι ((r ▷ nᵢ) ⊔ ((e ▷ nᵢ) ⊔ ((i ▷ nᵢ) ⊔ (@γᵢₙᵢₜ σ i r))))⟩) ⟶ (⟨𝕏 r, nᵢ⟩) 
    := OSSProof.base (ProtocolProof.base Proof.St₃') 
  have hl₅ : Γ ⊢ₒₛₛ  ⟨ ι ((i ▷ nᵢ) ⊔ (@γᵢₙᵢₜ σ i r)) ⟩ ⟶ ([send i,r(⦃| ag(i) ‖  nᵢ |⦄pk(r))]( [recv r(⦃| ag(i) ‖ nᵢ |⦄pk(r))]((𝔹 r, ⟨ 𝕏 i, nᵢ ⟩))))  
    := dl_th_2 hl₄ 
  have hl₆ : Γ ⊢ₒₛₛ  ⟨ ι ((i ▷ nᵢ) ⊔ (@γᵢₙᵢₜ σ i r)) ⟩ ⟶ ([send i,r(⦃| ag(i) ‖  nᵢ |⦄pk(r))]( [recv r(⦃| ag(i) ‖ nᵢ |⦄pk(r))]((𝕂 r, ⟨ 𝕏 i, nᵢ ⟩))))  
    := edl_th_1 hl₅ 
  have hl₇ : Γ ⊢ₒₛₛ  ⟨ ι ((i ▷ nᵢ) ⊔ (@γᵢₙᵢₜ σ i r )) ⟩ ⟶ ([send i,r(⦃| ag(i) ‖  nᵢ |⦄pk(r)) ; recv r(⦃| ag(i) ‖ nᵢ |⦄pk(r))]((𝕂 r, ⟨ 𝕏 i, nᵢ ⟩))) 
    := dl_th_3 hl₆ 
  exact hl₇ 

/-
  **AUTOMATED GENERATED MODEL**
-/

/-
  **Generate model**
-/

namespace hidden 
def State (σ : Nat) := List (List $ Message σ)

def EmptyMessage (σ : Nat) : Message σ := Message.empty
def EmptyState {σ : Nat} : State σ := [[]]

structure AutomaticallyGeneratedModel (σ : Nat) where
  Agents : List Agent
  States : List $ State σ
  R𝕂 : List $ (Agent × List Nat)
  R𝔹 : List $ (Agent × List Nat)
  RPDLSend : List $ (Agent × Agent × Message σ × List Nat)
  RPDLRecv : List $ (Agent × Message σ × List Nat)
  RPDLGen : List $ (Agent × Message σ × List Nat)

def List.getAtIndex {α : Type} (list : List α) (i : Nat) : Option α :=
  match i with
  | 0 => list.head?
  | i' + 1 => List.getAtIndex (list.tail!) i'

def List.getAtIndex! {α : Type} (list : List α) (i : Nat) (default : α) : α :=
  match List.getAtIndex list i with
  | none => default
  | some result => result

def MessageContext (σ : Nat) := List $ Message σ

def DeductionClosureStep {σ : Nat} (Γ : MessageContext σ) (Γc : MessageContext σ) : MessageContext σ :=
  match Γ with 
  | [] => [] 
  | (m :: tail) => match m with 
    | ⦃|m'|⦄k => if Γc.contains k && !Γc.contains m' then m' :: m :: DeductionClosureStep tail Γc else m :: DeductionClosureStep tail Γc
    | m₁ ‖ m₂ => 
    if Γc.contains (m₁ ‖ m₂) then 
      if Γc.contains m₁ then 
        if Γc.contains m₂ then 
          m :: DeductionClosureStep tail Γc 
        else 
          m :: m₂ :: DeductionClosureStep tail Γc 
      else 
        if Γc.contains m₂ then 
          m :: m₁ :: DeductionClosureStep tail Γc 
        else 
          m :: m₁ :: m₂ :: DeductionClosureStep tail Γc 
    else m :: DeductionClosureStep tail Γc 
    | _ => m :: DeductionClosureStep tail Γc

set_option maxHeartbeats 800000

def DeductionClosure {σ : Nat} (Γ : MessageContext σ) : MessageContext σ := 
  let Γ₀ := DeductionClosureStep Γ Γ
  let Γ₁ := DeductionClosureStep Γ₀ Γ₀ 
  let Γ₂ := DeductionClosureStep Γ₁ Γ₁ 
  Γ₂ 


def MessageInfer {σ : Nat} (Γ : MessageContext σ) (m : Message σ) : Bool := 
  let Γ' := DeductionClosure Γ
  match m with 
  | Message.empty => True
  | m₁ ‖ m₂ => Γ'.contains (m₁ ‖ m₂) || (Γ'.contains m₁ && Γ'.contains m₂) 
  | ⦃|m₁|⦄m₂ => Γ'.contains (⦃|m₁|⦄m₂) || (Γ'.contains m₁ && Γ'.contains m₂)
  | sk(i) => Γ'.contains $ sk(i)
  | pk(i) => Γ'.contains $ pk(i)
  | ag(i) => Γ'.contains $ ag(i)
  | text(t) => Γ'.contains $ text(t)
  | Message.symmetricKey i j k => Γ'.contains $ Message.symmetricKey i j k 

notation Γ " ⊢μ " m => MessageInfer Γ m 

def AwarenessSatisfies {σ : Nat} (M : AutomaticallyGeneratedModel σ) (wIndex : Nat) (agent : Agent) (m : Message σ) : Bool := 
  let modelAgents : List Agent := M.Agents
  let numberOfAgents : Nat := modelAgents.length
  let zippedAgentList := List.zip modelAgents $ List.range numberOfAgents
  let agentStatePosition : Nat := List.getAtIndex! (List.map (fun (_, pos) => pos) (List.filter  (fun (ag, _) => ag == agent) zippedAgentList) ) 0 0
  let currentState : State σ := List.getAtIndex! M.States wIndex EmptyState 
  let currentAgentState := List.getAtIndex! currentState agentStatePosition []
  currentAgentState ⊢μ m 

def ModalKBStates {σ : Nat} (_ : AutomaticallyGeneratedModel σ) (wIndex : Nat) (agent : Agent) (relation : List $ (Agent × List Nat)) : List Nat :=
  let agentRelation : List $ List Nat := ((relation.filter (fun (ag, _) => ag == agent)).map (fun (_, y) => y)).filter (fun list => List.getAtIndex! list 0 0 == wIndex)
  let accessibleStates : List Nat := agentRelation.map (fun list => List.getAtIndex! list 1 0)
  accessibleStates 


def PDLSendStates {σ : Nat} (_ : AutomaticallyGeneratedModel σ) (wIndex : Nat) (i : Agent) (j : Agent) (m : Message σ) (relation : List $ (Agent × Agent × Message σ × List Nat)) : List Nat := 
  let agentRelation : List $ List Nat := ((relation.filter (fun (agi, agj, msg, _) => agi == i && agj == j && msg == m)).map (fun (_, _, _, y) => y)).filter (fun list => List.getAtIndex! list 0 0 == wIndex)
  let accessibleStates : List Nat := agentRelation.map (fun list => List.getAtIndex! list 1 0)
  accessibleStates 

def PDLRecvStates {σ : Nat} (_ : AutomaticallyGeneratedModel σ) (wIndex : Nat) (j : Agent) (m : Message σ) (relation : List $ (Agent × Message σ × List Nat)) : List Nat :=
  let agentRelation : List $ List Nat := ((relation.filter (fun (agj, msg, _) => agj == j && msg == m)).map (fun (_, _, y) => y)).filter (fun list => List.getAtIndex! list 0 0 == wIndex)
  let accessibleStates : List Nat := agentRelation.map (fun list => List.getAtIndex! list 1 0)
  accessibleStates 

def PDLGenStates {σ : Nat} (_ : AutomaticallyGeneratedModel σ) (wIndex : Nat) (j : Agent) (m : Message σ) (relation : List $ (Agent × Message σ × List Nat)) : List Nat :=
  let agentRelation : List $ List Nat := ((relation.filter (fun (agj, msg, _) => agj == j && msg == m)).map (fun (_, _, y) => y)).filter (fun list => List.getAtIndex! list 0 0 == wIndex)
  let accessibleStates : List Nat := agentRelation.map (fun list => List.getAtIndex! list 1 0)
  accessibleStates 

def SatisfiesAtState {σ : Nat} (M : AutomaticallyGeneratedModel σ) (φ : Formula σ) (wIndex : Nat) : Bool :=
  match φ with
  | Formula.atom _ => True 
  | Formula.true => True 
  | φ ⟶ ψ => (SatisfiesAtState M φ wIndex) → (SatisfiesAtState M ψ wIndex)
  | ~φ => !(SatisfiesAtState M φ wIndex) 
  | 𝕏 agent, m => AwarenessSatisfies M wIndex agent m  
  | 𝔹 agent, φ => 
    let accessibleStates := ModalKBStates M wIndex agent M.R𝔹
    let applySatisfaction := accessibleStates.map (fun accessibleState => SatisfiesAtState M φ accessibleState)
    applySatisfaction.foldr (fun x y => x && y) True 
  | [send i, j(m)] φ => 
    let accessibleStates := PDLSendStates M wIndex i j m M.RPDLSend
    let applySatisfaction := accessibleStates.map (fun accessibleState => SatisfiesAtState M φ accessibleState)
    applySatisfaction.foldr (fun x y => x && y) True 
  | [recv j(m)] φ => 
    let accessibleStates := PDLRecvStates M wIndex j m M.RPDLRecv 
    let applySatisfaction := accessibleStates.map (fun accessibleState => SatisfiesAtState M φ accessibleState)
    applySatisfaction.foldr (fun x y => x && y) True 
  | _ => True 

notation M " at " w " ⊧ " φ => SatisfiesAtState M φ w

def Satisfies {σ : Nat} (M : AutomaticallyGeneratedModel σ) (φ : Formula σ) : Bool := 
  let allStates := List.range $ M.States.length 
  let satisfiesAllStates := allStates.map (fun state => M at state ⊧ φ)
  satisfiesAllStates.foldr (fun x y => x && y) True 

notation M " ⊧ " φ => Satisfies M φ 


structure ProtocolAction (σ : Nat) where 
  Sender: Agent
  Receiver: Agent
  Message: Message σ 

instance EmptyProtocolAction {σ : Nat} : ProtocolAction σ := 
{
  Sender := "",
  Receiver := "",
  Message := Message.empty 
}  

structure Protocol (σ : Nat) where
  Agents : List Agent 
  SymmetricKeys : List $ (Agent × Agent × Message σ)
  Specification : List $ ProtocolAction σ 

def GetAllSubMessages {σ : Nat} (m : Message σ) : List $ Message σ := 
  match m with 
  | Message.empty => [] 
  | text(t) => [text(t) ]
  | ag(i) => [ag(i) ]
  | Message.symmetricKey k i j => [Message.symmetricKey k i j]
  | pk(i) => [pk(i) ]
  | sk(i) => [sk(i) ]
  | ⦃|m|⦄k => GetAllSubMessages m ++ [k] 
  | m₁ ‖ m₂ => GetAllSubMessages m₁ ++ GetAllSubMessages m₂   

def GetAllMessagesFromList {σ : Nat} (list : List $ Message σ) : List $ Message σ := 
  match list with 
  | [] => [] 
  | (message :: tail) => 
    match message with 
    | Message.empty => tail 
    | text(t) => text(t) :: tail 
    | ag(i) => ag(i) :: tail 
    | Message.symmetricKey k i j => (Message.symmetricKey k i j) :: tail 
    | pk(i) => pk(i) :: tail 
    | sk(i) => sk(i) :: tail 
    | ⦃|m|⦄k => GetAllSubMessages (⦃|m|⦄k) ++ [⦃|m|⦄k] ++ tail 
    | m₁ ‖ m₂ => GetAllSubMessages (m₁ ‖ m₂) ++ [m₁ ‖ m₂] ++ tail 

def List.removeDuplicates {α : Type} [BEq α] (list : List α) : List α := 
  match list with 
  | [] => []
  | (head :: tail) => if tail.contains head then tail else head :: tail 


def AppendAgentNewKnowledge {σ : Nat} (P : Protocol σ) (agent : Agent) (currentState : State σ) (newKnowledge : List $ Message σ) : State σ := 
  let agentsNumber := P.Agents.length 
  let agentsPositions := List.zip P.Agents $ List.range $ agentsNumber
  let agentPosition := List.getAtIndex! (List.map (fun (_, pos) => pos) (List.filter (fun (ag, _) => ag == agent) agentsPositions)) 0 0
  let stateForAgents := currentState.zip $ List.range $ agentsNumber 
  let newState := stateForAgents.map (fun (ik, pos) => 
    if pos == agentPosition then List.removeDuplicates (List.append ik newKnowledge) else ik 
  )
  newState

def BuildFromActions {σ : Nat} (P : Protocol σ) (currentStateIndex : Nat) (states : List $ State σ) (statesLeft : Nat)
  : (List $ State σ) 
  × (List $ (Agent × Agent × Message σ × List Nat)) 
  × (List $ (Agent × Message σ × List Nat)) := 
  match statesLeft with 
  | 0 => ([], [], [])
  | n + 1 => 
    let currentAction := List.getAtIndex! P.Specification currentStateIndex ({ Sender := "", Receiver := "", Message := Message.empty })
    let sender := currentAction.Sender 
    let receiver := currentAction.Receiver 
    let message := currentAction.Message 
    let lastState := List.getAtIndex! states (states.length - 1) EmptyState 
    let newState := AppendAgentNewKnowledge P sender lastState [message] 
  
    let newUpdatedState := 
      if currentStateIndex != 0 then 
        let lastAction := List.getAtIndex! P.Specification (currentStateIndex - 1) ({ Sender := "", Receiver := "", Message := Message.empty })
        let lastReceiver := lastAction.Receiver 
        let lastMessage := lastAction.Message 
        AppendAgentNewKnowledge P lastReceiver newState [lastMessage]
      else newState 

    (newUpdatedState :: (BuildFromActions P (currentStateIndex + 1) (states.append [newUpdatedState]) n).fst, 
    if message != Message.empty then 
      ((sender, receiver, message, [currentStateIndex, currentStateIndex + 1]) :: (BuildFromActions P (currentStateIndex + 1) (states.append [newUpdatedState]) n).snd.fst) 
    else (BuildFromActions P (currentStateIndex + 1) (states.append [newUpdatedState]) n).snd.fst,
    if message != Message.empty then 
      ((receiver, message, [currentStateIndex, currentStateIndex + 1]) :: (BuildFromActions P (currentStateIndex + 1) (states.append [newUpdatedState]) n).snd.snd) 
    else (BuildFromActions P (currentStateIndex + 1) (states.append [newUpdatedState]) n).snd.snd
    )

def BuildModel {σ : Nat} (P : Protocol σ) : AutomaticallyGeneratedModel σ := 
  let specification := P.Specification 
  let agentsNumber := P.Agents.length 
  let agentsPositions := List.zip P.Agents $ List.range $ agentsNumber

  let initialAction := specification.getAtIndex! 0 EmptyProtocolAction
  let agentsInitialKnowledgeEmpty : List $ List $ Message σ := List.replicate agentsNumber [] 
  let initialAgentPosition := ((agentsPositions.filter (fun (ag, _) => ag == initialAction.Sender)).map (fun (_, pos) => pos)).getAtIndex! 0 0

  let agentsInitialKnowledge := ((agentsInitialKnowledgeEmpty.zip (List.range agentsNumber)).map (fun (ik, agentPos) => 
    if agentPos == initialAgentPosition then ik.append [initialAction.Message] else ik.append []))

  let agentsInitialKnowledgeKeys := (agentsInitialKnowledge.zip (List.range agentsNumber)).map (fun (ik, pos) => 
    let agentByPos := ((agentsPositions.filter (fun ((_ : Agent), y) => y == pos)).map (fun ((x : Agent), (_ : Nat)) => x)).getAtIndex! 0 ""
    let searchInSymmetricKeys := P.SymmetricKeys.filter (fun ((x : Agent), (y : Agent), (_ : Message σ)) => x == agentByPos || y == agentByPos)
    let key := if searchInSymmetricKeys.length > 0 then (searchInSymmetricKeys.getAtIndex! 0 (("", "", Message.empty) : Agent × Agent × Message σ)).snd.snd else Message.empty 
    let otherAgentsPublicKeys : List $ Message σ := (P.Agents.filter (fun ag => ag != agentByPos)).map (fun ag => pk(ag))
    if key != Message.empty then (ik.append [key, sk(agentByPos), pk(agentByPos) ]).append otherAgentsPublicKeys else (ik.append [sk(agentByPos), pk(agentByPos) ]).append otherAgentsPublicKeys
    )
  
  let initialState : State σ := agentsInitialKnowledgeKeys

  let result := BuildFromActions P 0 [initialState] (specification.length + 1)

  let states := result.fst 
  let pdlRelationSend := result.snd.fst 

  let firstOccuranceForEveryAgent := P.Agents.map (fun agent => 
    let firstState : Nat := (((pdlRelationSend.filter (fun (ag, _, _, _) => ag == agent)).map (fun (_, _, _, ls) => ls)).getAtIndex! 0 []).getAtIndex! 0 0 
    (agent, firstState)
  )

  let numberOfStates := states.length 

  let knowledge_relation := firstOccuranceForEveryAgent.map (fun (ag, initialAgentState) => 
    let allStates := List.range numberOfStates 
    let agentStates := (List.foldr (fun x y => x ++ y) [] $ (allStates.map (fun x => allStates.map (fun y => if x <= y then [x, y] else []))))
    let agentListFiltered := agentStates.filter (fun (list : List Nat) => list.getAtIndex! 0 0 >= initialAgentState) 
    (agentListFiltered.map (fun list => (ag, list))).filter (fun (_, list) => list != [])
  )

  let knowledge := List.foldr (fun x y => x ++ y) [] knowledge_relation 

  let belief_relation := firstOccuranceForEveryAgent.map (fun (ag, initialAgentState) => 
    let allStates := List.range numberOfStates 
    let agentStates := (List.foldr (fun x y => x ++ y) [] $ (allStates.map (fun x => allStates.map (fun y => if x < y then [x, y] else [])))) ++ [[allStates.getAtIndex! (allStates.length - 1) 0, allStates.getAtIndex! (allStates.length - 1) 0]]
    let agentListFiltered := agentStates.filter (fun (list : List Nat) => list.getAtIndex! 0 0 >= initialAgentState) 
    (agentListFiltered.map (fun list => (ag, list))).filter (fun (_, list) => list != []))

  let belief := List.foldr (fun x y => x ++ y) [] belief_relation 

  {
    Agents := P.Agents,
    States := states,
    R𝕂 := knowledge,
    R𝔹 := belief,
    RPDLSend := pdlRelationSend,
    RPDLRecv := result.snd.snd,
    RPDLGen := [],
  }

/-
  **OSS**
-/

section OSS
  instance OSS {σ : Nat} : Protocol σ := 
  {
    Agents := ["i", "r"]
    SymmetricKeys := []
    Specification := [
      { Sender := "i", Receiver := "r", Message := ⦃|#"i"# ‖ #"ni"#|⦄pk("r") }
    ]
  }

  def OSSModel {σ : Nat} : AutomaticallyGeneratedModel σ := BuildModel OSS

  #reduce OSSModel 

  #reduce OSSModel ⊧ 𝕏 "i", #"ni"#

  #reduce OSSModel ⊧ [recv "r"(⦃|#"i"# ‖ #"ni"#|⦄pk("r"))] (𝕏 "r", (⦃|#"i"# ‖ #"ni"#|⦄pk("r")))

  #reduce OSSModel ⊧ [recv "r"(⦃|#"i"# ‖ #"ni"#|⦄pk("r"))] ((𝕂 "i", 𝕏 "r", #"ni"#) ⋀ (𝕂 "r", 𝕏 "i", #"ni"#))

  

end OSS

section OSSE
  instance OSSE {σ : Nat} : Protocol σ := 
  {
    Agents := ["i", "r", "e"]
    SymmetricKeys := []
    Specification := [
      { Sender := "e", Receiver := "r", Message := ⦃|#"i"# ‖ #"ne"#|⦄pk("r") }
    ]
  }

  def OSSEModel {σ : Nat} : AutomaticallyGeneratedModel σ := BuildModel OSSE

  #reduce OSSEModel 

  #reduce OSSEModel ⊧ [recv "r"(⦃|#"i"# ‖ #"ni"#|⦄pk("r"))] ((𝕂 "i", 𝕏 "r", #"ni"#) ⋀ (𝕂 "r", 𝕏 "i", #"ni"#))

end OSSE

/-
  **Needham Schroeder**
-/

section NeedhamSchroeder
  instance NeedhamSchroeder {σ : Nat} : Protocol σ := 
  {
    Agents := ["i", "r"]
    SymmetricKeys := [] 
    Specification := [
      { Sender := "i", Receiver := "r", Message := ⦃|ag("i") ‖ #"ni"#|⦄pk("r") },
      { Sender := "r", Receiver := "r", Message := ⦃|#"ni"# ‖ #"nr"# |⦄pk("i") },
      { Sender := "i", Receiver := "r", Message := ⦃|#"nr"#|⦄pk("r") }
    ]
  }

  def NeedhamSchroederModel {σ : Nat} : AutomaticallyGeneratedModel σ := BuildModel NeedhamSchroeder

  #reduce NeedhamSchroederModel

  #reduce NeedhamSchroederModel ⊧ [recv "r"(⦃|ag("i") ‖ #"ni"#|⦄pk("r"))] ((𝕂 "r", 𝕏 "i", #"ni"#) ⋀ (𝕂 "i", 𝕏 "r", #"ni"#))
  -- true

  -- #reduce NeedhamSchroederModel ⊧ [recv "r"(⦃|ag("i") ‖ #"ni"#|⦄pk("r"))] ([recv "i"(⦃|#"ni"# ‖ #"nr"# |⦄pk("i"))] 𝕂 "i", 𝕏 "r", #"nr"#)
  -- true 

end NeedhamSchroeder

section NeedhamSchroederMitM
  instance NeedhamSchroederMitM {σ : Nat} : Protocol σ := 
  {
    Agents := ["i", "r", "e"]
    SymmetricKeys := [] 
    Specification := [
      { Sender := "i", Receiver := "e", Message := ⦃|ag("i") ‖ #"ni"#|⦄pk("e") },
      { Sender := "e", Receiver := "r", Message := ⦃|ag("i") ‖ #"ni"#|⦄pk("r") },
      { Sender := "r", Receiver := "e", Message := ⦃|#"ni"# ‖ #"nr"# |⦄pk("e") },
      { Sender := "e", Receiver := "i", Message := ⦃|#"ni"# ‖ #"nr"# |⦄pk("i") },
      { Sender := "i", Receiver := "e", Message := ⦃|#"nr"#|⦄pk("e") },
      { Sender := "e", Receiver := "r", Message := ⦃|#"nr"#|⦄pk("r") }
    ]
  }

  def NeedhamSchroederMitMModel {σ : Nat} : AutomaticallyGeneratedModel σ := BuildModel NeedhamSchroederMitM

  #reduce NeedhamSchroederMitMModel

  -- #reduce NeedhamSchroederMitMModel ⊧ [recv "r"(⦃|ag("i") ‖ #"ni"#|⦄pk("r"))] 𝕂 "r", 𝕏 "i", #"ni"#
  -- true 

  -- #reduce NeedhamSchroederMitMModel ⊧ 𝕂 "i", 𝕏 "r", #"ni"#
  -- false 
end NeedhamSchroederMitM
end hidden 