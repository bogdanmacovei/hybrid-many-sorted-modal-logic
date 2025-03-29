import Init.Data.List.Basic
import Init.Data.List.FinRange

section Set
  inductive Set (α : Type) where
  | nil : Set α
  | cons : α → Set α → Set α
  deriving Repr
  def Set.mem {α : Type} (a : α) : Set α → Prop
  | Set.nil => false
  | (Set.cons b l) => a = b ∨ Set.mem a l
  notation x " ∈₁ " xs => Set.mem x xs
  theorem Set.mem_cons_of_mem (α : Type) {a b : α} {l : Set α} (h : a ∈₁ l)
    : a ∈₁ (Set.cons b l) := by
      exact Or.inr h
  theorem Set.mem_cons_self {α : Type} (a : α) (l : Set α)
    : a ∈₁ Set.cons a l := Or.inl rfl
  theorem Set.mem_nil {α : Type} (a : α) : ¬ (Set.mem a Set.nil) := by
    intro h
    trivial
  notation "∅₁" => Set.nil
  notation x "::" xs => Set.cons x xs
  def Set.append {α : Type} : Set α → Set α → Set α := fun l₁ ys =>
    match l₁ with
  | Set.nil => ys
  | (Set.cons x xs) => Set.cons x (Set.append xs ys)
  notation xs "+++" ys => Set.append xs ys
end Set

inductive sort (σ : Nat) where 
  | atom : Fin σ → sort σ
deriving Repr

notation "#s" s => sort.atom (s : Fin 100)

inductive Nominal (σ : Nat) where 
| atom : Fin σ → Nominal σ
| nominal : Float → Nominal σ
deriving Repr

inductive ActionNN (σ : Nat)
| atom : Fin σ → ActionNN σ
| train : ActionNN σ
| update : ActionNN σ
| Stop : ActionNN σ
| seq : ActionNN σ → ActionNN σ → ActionNN σ
deriving Repr

notation "#a" a => ActionNN.atom (a : Fin 100)
notation α " ; " β => ActionNN.seq α β

notation "#n" x => Nominal.atom (x : Fin 100)
notation "#γ" r => ((Nominal.nominal r) : Nominal 100)

inductive FormNN (σ : Nat) : Type where
  | atom : Fin σ → FormNN σ
  | nomToForm : Nominal σ → FormNN σ
  | neg : FormNN σ → FormNN σ
  | oplus : FormNN σ → FormNN σ → FormNN σ
  | sigma : Set (FormNN σ) → FormNN σ
  | hybrid : Nominal σ → sort σ → FormNN σ → FormNN σ
  | nom : Nominal σ → FormNN σ → FormNN σ
  | diam : Nominal σ → FormNN σ → FormNN σ
  | program : ActionNN σ → FormNN σ → FormNN σ
  | program_memory : ActionNN σ → FormNN σ → FormNN σ → FormNN σ
  | list : List (FormNN σ) → FormNN σ
  | modalImplication : FormNN σ → FormNN σ → FormNN σ
  | negation : FormNN σ → FormNN σ
  | bot : FormNN σ
  | and : FormNN σ → FormNN σ → FormNN σ
deriving Repr

notation " #p " p => FormNN.atom (p : Fin 100)
notation " ¬L " p => FormNN.neg p
notation p " ⊕ " q => FormNN.oplus p q 
notation p " ⊙ " q => ¬L((¬L p) ⊕ (¬L q))
notation p " →L " q => (¬L p) ⊕ q
notation p " ⋁ " q => (p ⊙ (¬L q)) ⊕ q
notation p " ⋀ " q => (p ⊕ (¬L q)) ⊙ q
notation " ◇ " r " , " p => FormNN.diam r p
notation " @@ " j " , " s " : " φ => FormNN.hybrid j s φ
notation " @@ " x " , " φ => FormNN.nom x φ
notation " [[ " α " ]] " φ => FormNN.program α φ
notation φ " ⊃ " ψ => FormNN.modalImplication φ ψ
notation "~" φ => FormNN.negation φ
notation φ " & " ψ => FormNN.and φ ψ
notation "⊥" => FormNN.bot

notation " zL " => (FormNN.nomToForm $ #γ 0)

section Hidden 
 section LinearAlgebra

    open List

    def Vector (α : Type) (n : Nat) := Fin n → α
    def Matrix (α : Type) (m n : Nat) := Fin m → Vector α n

    def list2vector {α : Type} (l : List α) (n : Nat) (h : n = l.length) : Vector α n :=
      fun i : Fin n =>
      match i with
      | ⟨i, hi⟩ => l.get ⟨i, by {
        apply Nat.lt_of_lt_of_le hi
        exact Nat.le_of_eq (by exact h)
      }⟩

    def list2matrix {α : Type} (ll : List (List α)) (m n : Nat) (h : m = ll.length) : Matrix α m n :=
      fun i => list2vector (ll.get ⟨i.val, by {
        apply Nat.lt_of_lt_of_le i.isLt
        exact Nat.le_of_eq (by exact h)
      }⟩) n (by {
        -- Proof that each sublist has length n needs to be provided or assumed
        sorry
      })



    -- def index {α : Type} (v : Vector α n) (i : Nat) : Option α :=
    --   if h : i < n then
    --     some $ v ⟨i, h⟩
    --   else
    --     none

      -- it is left with sorry so that it is not necessary to write the hypothesis with i < n everytime
      def index {α : Type} (v : Vector α n) (i : Nat) : α := v ⟨i, by admit ⟩



    notation v " [ " i " ] " => index v i

    def vector2list {α : Type} {n : Nat} (v : Vector α n) : List α :=
      map (fun i => v [i]) (range n)

    instance {α : Type} [Repr α] {n : Nat} : Repr (Vector α n) where
      reprPrec v _ :=
        let elems := vector2list v
        "Vector " ++ repr elems

    def matrix2list {α : Type} {n m : Nat} (m : Matrix α n m) : List $ List α :=
      map (fun i => vector2list $ m [i]) (range n)

    instance {α : Type} [Repr α] {n m : Nat} : Repr (Matrix α n m) where
      reprPrec m _ :=
        let elems := matrix2list m
        "Matrix " ++ repr elems

    def elementwiseDiff { α : Type } [HSub α α α] [HAdd α α α] [OfNat α 0]
      (v₁ : Vector α n) (v₂ : Vector α n) : Vector α n := fun i => v₁ [i] - v₂ [i]

    notation v₁ " -V " v₂ => elementwiseDiff v₁ v₂

    def dot_product { α : Type } [HMul α α α] [HAdd α α α] [OfNat α 0]
      (v w : Vector α n) : α :=
      foldr (fun x y => x + y) 0 $
      map (fun (x, y) => x * y)
      (Array.zip
        (map (fun i => v [i]) (range n)).toArray
        (map (fun i => w [i]) (range n)).toArray).toList

    notation v " ⬝ " w => dot_product v w

    def indexes (matrix : Matrix α m n) (i j : Nat) (hi : i < m) (hj : j < n)
      := matrix ⟨ i, by assumption ⟩ ⟨ j, by assumption ⟩

    notation m " [ " i " , " j " ] " => indexes m i j (by simp) (by simp)

    def list_times_vector { α : Type } [HMul α α α] [HAdd α α α] [OfNat α 0] [Inhabited α] { n : Nat }
      (list : List α)
      (vector : Vector α n) : α :=
      foldr (fun x y => x + y) 0 $ map (fun i => list.get! i * vector [i]) (range n)

    def vector_times_list { α : Type } [HMul α α α] [HAdd α α α] [OfNat α 0] [Inhabited α] { n : Nat }
      (vector : Vector α n)
      (list : List α): α := list_times_vector list vector

    notation list " ×LV " vector => list_times_vector list vector
    notation vector " ×VL " list => vector_times_list vector list

    def transpose {α : Type} {m n : Nat} (mat : Matrix α m n) : Matrix α n m :=
      fun i j => mat j i

    notation "T( " matrix " )" => transpose matrix

    def matrix_product {α : Type} [HMul α α α] [HAdd α α α] [OfNat α 0]
      {m n p : Nat}
      (A : Matrix α m n)
      (B : Matrix α n p) : Matrix α m p :=
      fun i => fun j =>
        let row_i := A [i]
        let col_j := (fun k => B k j)
        let dot_prod := row_i ⬝ col_j
        dot_prod

    notation m₁ " ×M " m₂ => matrix_product m₁ m₂

    def mapVector {α β : Type} {n : Nat} (f : α → β) (v : Vector α n) : Vector β n :=
      fun i => f (v i)

    notation f " <$>V " v => mapVector f v

    def mapMatrix {α β : Type} {m n : Nat} (f : α → β)
      (mat : Matrix α m n) : Matrix β m n :=
      fun i j => f (mat i j)

    notation f " <$>M " matrix => mapMatrix f matrix

    def matrix_dot_vector {α : Type} [HMul α α α] [HAdd α α α] [OfNat α 0]
      (matrix : Matrix α m n)
      (vector : Vector α n)
      : Matrix α m 1 := fun i _ => matrix[i] ⬝ vector

    notation matrix " × " vector => matrix_dot_vector matrix vector

    section Example2
      def vector : Vector Float 3 := fun i => match i with
        | ⟨0, _⟩ => 0.4 | ⟨1, _⟩ => 0.5 | ⟨2, _⟩ => 0.6
      #eval vector ⬝ vector

      def vector₂ : Vector Float 3 := fun i => match i with
        | ⟨0, _⟩ => 0.2 | ⟨1, _⟩ => 0.52 | ⟨2, _⟩ => 0.78

      def matrix : Matrix Float 2 3 :=
        fun i => match i with
        | ⟨0, _⟩ => fun j => match j with
          | ⟨0, _⟩ => 0.1 | ⟨1, _⟩ => 0.2  | ⟨2, _⟩ => 0.3
        | ⟨1, _⟩ => fun j => match j with
          | ⟨0, _⟩ => 0.4  | ⟨1, _⟩ => 0.5 | ⟨2, _⟩ => 0.6

      #check matrix × vector
      #eval (matrix × vector) [0, 0]

      #check T(matrix)

      #eval ((fun x => x) <$>M (matrix ×M (T(matrix)))) [1,1]

      #eval (foldr (fun x y => x + y) 0 $ map (fun i => (vector [i] - vector₂ [i]) ^ 2) (range 3)) * 1 / 3

      #check [Vector Nat 2, Vector Nat 3]
      #eval List.get! [1,2,3] 1


      def random_list [HDiv Nat Nat $ IO Nat] (size : Nat) : IO (List Float) :=
        let rec loop (n : Nat) (acc : List Float) : IO (List Float) :=
          if n = 0 then
            return acc
          else do
            let r ← IO.rand 0 100
            loop (n - 1) (List.append [Nat.toFloat (r/100)] acc)
        loop size []

    end Example2

  end LinearAlgebra
end Hidden 


section hidden 
namespace SymbolicNN

abbrev Vector (n : Nat) := Fin n → Float
abbrev Matrix (m n : Nat) := Fin m → Fin n → Float

instance : Repr (Vector n) where
  reprPrec v _ := toString (repr (List.map v (List.finRange n))) |> toString

instance : Repr (Matrix m n) where
  reprPrec mtx _ :=
    let rows := List.finRange m |>.map (fun i =>
      List.finRange n |>.map (fun j => mtx i j))
    toString (repr rows) |> toString

structure NNState (n k : Nat) where
  id : Nat
  weights : Fin k → Matrix n n
  biases : Fin k → Vector n
  input : Vector n

instance [Repr (Vector n)] [Repr (Matrix n n)] : Repr (NNState n k) where
  reprPrec s _ :=
    "State " ++ repr s.id ++
    "\nWeights:\n" ++ toString (repr (List.map s.weights (List.finRange k))) ++
    "\nBiases:\n" ++ toString (repr (List.map s.biases (List.finRange k))) ++
    "\nInput: " ++ toString (toString (repr s.input))

inductive Action where
| train : Nat → Action
| update : Action
| stop : Action
  deriving Repr

structure Transition (n k : Nat) where
  fromState : NNState n k
  action : Action
  toState : NNState n k
  deriving Repr

def relu1 (x : Float) : Float :=
  min (max 0 x) 1

def trainStep {n k : Nat} (s : NNState n k) (layer : Nat) (h : layer < k) : NNState n k :=
  let idx := s.id + 1
  let z : Vector n := fun i =>
    let sum := List.finRange n |>.foldl (fun acc j =>
      acc + s.weights ⟨layer, by exact h⟩ i j * s.input j) 0.0
    relu1 sum
  let newWeights := fun l =>
    if l.1 = layer then
      fun i j =>
        let grad := s.input j 
        s.weights l i j - 0.01 * grad
    else
      s.weights l
  { id := idx, weights := newWeights, biases := s.biases, input := z }

def updateStep {n k : Nat} (s : NNState n k) : NNState n k :=
  let idx := s.id + 1
  let newBiases := fun l => fun i =>
    let sum := List.finRange n |>.foldl (fun acc j =>
      acc + s.weights l i j * s.input j) 0.0
    let act := relu1 sum
    s.biases l i - 0.01 * act
  { id := idx, weights := s.weights, biases := newBiases, input := s.input }

def stopStep {n k : Nat} (s : NNState n k) : NNState n k :=
  { s with id := s.id + 1 }

def step {n k : Nat} (s : NNState n k) (a : Action) : NNState n k :=
  match a with
  | Action.train l => trainStep s l (by admit)
  | Action.update => updateStep s
  | Action.stop => stopStep s

def generateModel {n k : Nat}
  (init : NNState n k)
  (actions : List Action) : List (Transition n k) :=
    let rec aux (s : NNState n k) (acts : List Action) (acc : List (Transition n k)) :=
      match acts with
      | [] => acc
      | a :: rest =>
        let newState := step s a
        let trans : Transition n k := { fromState := s, action := a, toState := newState }
        aux newState rest (acc ++ [trans])
    aux init actions []

def relu (x : Float) : Float :=
  min (max 0 x) 1 

def forwardLayer {n : Nat} (w : Matrix n n) (b : Vector n) (input : Vector n) : Vector n :=
  fun i =>
    let sum := (List.finRange n).foldl (fun acc j => acc + w i j * input j) 0
    relu (sum + b i)

def evaluate {n k : Nat} (s : NNState n k) : Vector n :=
  (List.finRange k).foldl (fun acc i => forwardLayer (s.weights i) (s.biases i) acc) s.input

def loss {n : Nat} (output target : Vector n) : Float :=
  (List.finRange n).foldl (fun acc i => acc + (output i - target i)^2) 0 / n.toFloat

def symbolicTrainLoop {n k : Nat} (init : NNState n k) (target : Vector n) (maxEpochs : Nat) (threshold : Float) : List (Transition n k) :=
  let rec loop (s : NNState n k) (epoch : Nat) (acc : List (Transition n k)) : List (Transition n k) :=
    if epoch ≥ maxEpochs then acc
    else
      let trainedTransitions := (List.finRange k).foldl (fun (accT, st) i =>
        let newSt := step st (Action.train i.1)
        (accT ++ [{ fromState := st, action := Action.train i.1, toState := newSt }], newSt)) ([], s)
      let trainedState := trainedTransitions.2
      let eval := evaluate trainedState
      let currentLoss := loss eval target
      if currentLoss ≤ threshold then
        let stopState := step trainedState Action.stop
        acc ++ trainedTransitions.1 ++ [{ fromState := trainedState, action := Action.stop, toState := stopState }]
      else
        let updateState := step trainedState Action.update
        let transitions := trainedTransitions.1 ++ [{ fromState := trainedState, action := Action.update, toState := updateState }]
        loop updateState (epoch + 1) (acc ++ transitions)
  --termination_by maxEpochs - epoch
  loop init 0 []

def w1 : Matrix 2 2 := fun i j => match (i.1, j.1) with
  | (0, 0) => 0.1 | (0, 1) => 0.2
  | (1, 0) => 0.13 | (1, 1) => 0.03
  | _ => 0.0

def w2 : Matrix 2 2 := fun i j => match (i.1, j.1) with
  | (0, 0) => 0.11 | (0, 1) => 0.1
  | (1, 0) => 0.0 | (1, 1) => 0.0
  | _ => 0.0

def W : Fin 2 → Matrix 2 2 := fun i => match i.1 with
  | 0 => w1
  | 1 => w2
  | _ => w1

def b : Fin 2 → Vector 2 := fun i => fun j => match (i.1, j.1) with
  | (0, 0) => 0.08 | (0, 1) => 0.0
  | (1, 0) => 0.18 | (1, 1) => 0.0
  | _ => 0.0

def input : Vector 2 := fun i => match i.1 with
  | 0 => 0.2 | 1 => 0.3 | _ => 0.0

def initState : NNState 2 2 := { id := 0, weights := W, biases := b, input := input }

def exampleActions : List Action :=
  let trainActions := List.finRange 2 |>.map (fun i => Action.train i.1)
  trainActions ++ [Action.update, Action.stop]

def printState {n k : Nat} (s : NNState n k) : String :=
  "State " ++ toString s.id ++
  "
Weights:
" ++ String.intercalate "
" (List.map (fun l => toString (repr (s.weights l))) (List.finRange k)) ++
  "
Biases:
" ++ String.intercalate "
" (List.map (fun l => toString (repr (s.biases l))) (List.finRange k)) ++
  "
Input: " ++ toString (repr s.input) ++ "
"


def printModel {n k : Nat} (m : List (Transition n k)) : String :=
  String.intercalate "
" (m.map (fun t =>
    "⟦" ++ printState t.fromState ++ "⟧ --[ " ++ toString (repr t.action) ++ " ]-->⟦" ++ printState t.toState ++ "⟧"))


def printModelCompact {n k : Nat} (m : List (Transition n k)) : String :=
  String.intercalate "\n" (m.map (fun t =>
    "State " ++ toString t.fromState.id ++
    " --[" ++ toString (repr t.action) ++ "]--> " ++
    "State " ++ toString t.toState.id))


def target : Vector 2 := fun i => match i.1 with | 0 => 0.01 | 1 => 0.0 | _ => 0.0

def exampleModel := symbolicTrainLoop initState target 10 0.0001

def transitionSummary {n k : Nat} (t : Transition n k) : String :=
  "State " ++ toString t.fromState.id ++
  " --[" ++ match t.action with
    | Action.train l => "train " ++ toString l
    | Action.update => "update"
    | Action.stop => "stop"
  ++ "]--> " ++ "State " ++ toString t.toState.id

def modelSummary {n k : Nat} (ts : List (Transition n k)) : List String :=
  ts.map transitionSummary

def actionToString : Action → String
  | Action.train l => "train " ++ toString l
  | Action.update => "update"
  | Action.stop => "stop"

def modelCompactSummary {n k : Nat} (ts : List (Transition n k)) : List String :=
  ts.map (fun t =>
    "State " ++ toString t.fromState.id ++
    " --[" ++ actionToString t.action ++ "]--> " ++
    "State " ++ toString t.toState.id)

set_option pp.explicit false
set_option pp.unicode.fun true
set_option pp.structureInstances true
set_option pp.proofs true
set_option pp.maxSteps 10

-- #reduce printModelCompact exampleModel

#eval! exampleModel.map (fun t => (t.fromState.id, repr t.action, t.toState.id))
#print modelCompactSummary exampleModel

#reduce modelSummary exampleModel

end SymbolicNN
end hidden 