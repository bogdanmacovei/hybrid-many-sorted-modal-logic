
def relu1 (x : Float) : Float :=
  min 1 (max 0 x)

def d_relu1 (x : Float) : Float :=
  if x > 0 ∧ x < 1 then 1 else 0

def loss (y_real y_pred : Float) : Float :=
  max 0 (y_real - y_pred)

def d_loss (y_real y_pred : Float) : Float :=
  if y_real - y_pred > 0 then -1 else 0

structure NeuralNetwork where
  weights1 : Array (Array Float)
  bias1    : Array Float
  weights2 : Array (Array Float)
  bias2    : Array Float
deriving Repr

def dot (x w : Array Float) : Float :=
  Array.foldl (· + ·) 0 (Array.zipWith (· * ·) x w)

def forward (nn : NeuralNetwork) (x : Array Float) : (Float × Array Float × Array Float) :=
  let a1 := #[relu1 (dot x nn.weights1[0]! + nn.bias1[0]!),
              relu1 (dot x nn.weights1[1]! + nn.bias1[1]!)]
  let y1 := dot a1 nn.weights2[0]! + nn.bias2[0]!
  let y2 := dot a1 nn.weights2[1]! + nn.bias2[1]!
  let y  := max y1 y2
  (y, a1, #[y1, y2])

def trainStep (nn : NeuralNetwork) (x : Array Float) (y_real : Float) (lr : Float) : NeuralNetwork :=
  let (y_pred, a1, ys) := forward nn x
  let err_grad := d_loss y_real y_pred
  let max_idx := if ys[0]! ≥ ys[1]! then 0 else 1
  let delta2 := #[if max_idx=0 then err_grad else 0,
                  if max_idx=1 then err_grad else 0]
  let grad_w2 := #[#[delta2[0]! * a1[0]!, delta2[0]! * a1[1]!],
                   #[delta2[1]! * a1[0]!, delta2[1]! * a1[1]!]]
  let grad_b2 := delta2
  let delta1 := #[d_relu1 a1[0]! * (nn.weights2[0]![0]! * delta2[0]! + nn.weights2[1]![0]! * delta2[1]!),
                  d_relu1 a1[1]! * (nn.weights2[0]![1]! * delta2[0]! + nn.weights2[1]![1]! * delta2[1]!)]
  let grad_w1 := #[#[delta1[0]! * x[0]!, delta1[0]! * x[1]!],
                   #[delta1[1]! * x[0]!, delta1[1]! * x[1]!]]
  let grad_b1 := delta1
  { weights1 := #[#[nn.weights1[0]![0]! - lr * grad_w1[0]![0]!, nn.weights1[0]![1]! - lr * grad_w1[0]![1]!],
                 #[nn.weights1[1]![0]! - lr * grad_w1[1]![0]!, nn.weights1[1]![1]! - lr * grad_w1[1]![1]!]],
    bias1    := #[nn.bias1[0]! - lr * grad_b1[0]!, nn.bias1[1]! - lr * grad_b1[1]!],
    weights2 := #[#[nn.weights2[0]![0]! - lr * grad_w2[0]![0]!, nn.weights2[0]![1]! - lr * grad_w2[0]![1]!],
                 #[nn.weights2[1]![0]! - lr * grad_w2[1]![0]!, nn.weights2[1]![1]! - lr * grad_w2[1]![1]!]],
    bias2    := #[nn.bias2[0]! - lr * grad_b2[0]!, nn.bias2[1]! - lr * grad_b2[1]!] }

def nn_init : NeuralNetwork :=
  { weights1 := #[#[0.4, 0.3], #[0.6, 0.1]],
    bias1    := #[0.1, 0.1],
    weights2 := #[#[0.9, 0.0], #[0.8, 1.0]],
    bias2    := #[0.15, 0.15] }

def x : Array Float := #[0.2, 0.3]
def y_real : Float := 0.8
def lr : Float := 0.1

def main : IO Unit := do
  let (initial_pred, _, _) := forward nn_init x
  IO.println s!"Initial prediction: {initial_pred}"
  let nn_trained := trainStep nn_init x y_real lr
  let (new_pred, _, _) := forward nn_trained x
  IO.println s!"Prediction after 1 epoch: {new_pred}"

#eval main