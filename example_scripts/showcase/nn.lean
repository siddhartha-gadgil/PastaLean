import PastaLean
import Libraries
import Std.Tactic.Do

open PastaLean
open Libraries
open Std.Do

set_option linter.all false
set_option mvcgen.warning false

set_option maxHeartbeats 0

noncomputable def sigmoid := fun (x : Real) ↦ (1.0 : Rat) /ₚ ((1.0 : Rat) +ₚ Libraries.math.pyMathExpR (-x))

attribute [simp] sigmoid

def sigmoid'rn := fun (x : Float) ↦ PastaLean.pyFloat (1.0 : Float) /ₚ ((1.0 : Float) +ₚ Libraries.math.pyMathExp (-x))

noncomputable def predict := fun (x : List Rat) ↦ fun (w1 : List (List Real)) ↦ fun (b1 : List Real) ↦
  fun (w2 : List (List Real)) ↦ fun (b2 : List Real) ↦
  -- Forward pass through a 2 -> 2 -> 1 network.
  let h0 := sigmoid (Libraries.numpy.pyNumpyDot x w1⦋(0 : Int)⦌ +ₚ b1⦋(0 : Int)⦌)
  let h1 := sigmoid (Libraries.numpy.pyNumpyDot x w1⦋(1 : Int)⦌ +ₚ b1⦋(1 : Int)⦌)
  let hidden := [h0, h1]
  sigmoid (Libraries.numpy.pyNumpyDot hidden w2⦋(0 : Int)⦌ +ₚ b2⦋(0 : Int)⦌)

attribute [simp] predict

def predict'rn := fun (x : List Float) ↦ fun (w1 : List (List Float)) ↦ fun (b1 : List Float) ↦
  fun (w2 : List (List Float)) ↦ fun (b2 : List Float) ↦
  -- Forward pass through a 2 -> 2 -> 1 network.
  let h0 := sigmoid'rn (Libraries.numpy.pyNumpyDot x w1⦋(0 : Int)⦌ +ₚ b1⦋(0 : Int)⦌)
  let h1 := sigmoid'rn (Libraries.numpy.pyNumpyDot x w1⦋(1 : Int)⦌ +ₚ b1⦋(1 : Int)⦌)
  let hidden := [h0, h1]
  sigmoid'rn (Libraries.numpy.pyNumpyDot hidden w2⦋(0 : Int)⦌ +ₚ b2⦋(0 : Int)⦌)

noncomputable def mean_squared_error := fun (xs : List (List Rat)) ↦ fun (ys : List Rat) ↦
  fun (w1 : List (List Real)) ↦ fun (b1 : List Real) ↦ fun (w2 : List (List Real)) ↦ fun (b2 : List Real) ↦
  Id.run
    (do
      let mut total := (0.0 : Real)
      for i in (PastaLean.pyRange (PastaLean.pyLen xs)) do
        let mut diff := predict xs⦋i⦌ w1 b1 w2 b2 -ₚ ys⦋i⦌
        total := total +ₚ diff *ₚ diff
      let __py_ret_1 := total /ₚ PastaLean.pyLen xs
      return __py_ret_1)

attribute [simp] mean_squared_error

def mean_squared_error'rn := fun (xs : List (List Float)) ↦ fun (ys : List Float) ↦ fun (w1 : List (List Float)) ↦
  fun (b1 : List Float) ↦ fun (w2 : List (List Float)) ↦ fun (b2 : List Float) ↦
  Id.run
    (do
      let mut total := (0.0 : Float)
      for i in (PastaLean.pyRange (PastaLean.pyLen xs)) do
        let mut diff := predict'rn xs⦋i⦌ w1 b1 w2 b2 -ₚ ys⦋i⦌
        total := total +ₚ diff *ₚ diff
      let __py_ret_1 := PastaLean.pyFloat total /ₚ PastaLean.pyLen xs
      return __py_ret_1)

noncomputable def main' :=
  ((do
      -- XOR is not linearly separable, so a single layer cannot solve it -- the
      -- hidden layer is what makes this learnable.
      let mut xs :=
        ([[(0.0 : Rat), (0.0 : Rat)], [(0.0 : Rat), (1.0 : Rat)], [(1.0 : Rat), (0.0 : Rat)],
            [(1.0 : Rat), (1.0 : Rat)]] :
          List (List Rat))
      let mut ys := ([(0.0 : Rat), (1.0 : Rat), (1.0 : Rat), (0.0 : Rat)] : List Rat)
      -- Fixed initial weights so the run is reproducible (no RNG needed).
      let mut w1 := ([[(0.5 : Real), -(0.4 : Real)], [(0.9 : Real), (1.0 : Real)]] : List (List Real))
      let mut b1 := ([(0.1 : Real), -(0.2 : Real)] : List Real)
      let mut w2 := ([[(0.7 : Real), -(0.8 : Real)]] : List (List Real))
      let mut b2 := ([(0.3 : Real)] : List Real)
      let mut lr := (0.5 : Rat)
      let mut epochs : Int := (4000 : Int)
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg "=== Training a neural net on XOR (NumPy + math) ==="]
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg s! "initial loss: {mean_squared_error xs ys w1 b1 w2 b2}"]
      for epoch in (PastaLean.pyRange epochs) do
        for i in (PastaLean.pyRange (PastaLean.pyLen xs)) do
          let mut x := xs⦋i⦌
          let mut y := ys⦋i⦌
          -- Forward pass, keeping the hidden activations for backprop.
          let mut h0 := sigmoid (Libraries.numpy.pyNumpyDot x w1⦋(0 : Int)⦌ +ₚ b1⦋(0 : Int)⦌)
          let mut h1 := sigmoid (Libraries.numpy.pyNumpyDot x w1⦋(1 : Int)⦌ +ₚ b1⦋(1 : Int)⦌)
          let mut hidden := ([h0, h1] : List Real)
          let mut out := sigmoid (Libraries.numpy.pyNumpyDot hidden w2⦋(0 : Int)⦌ +ₚ b2⦋(0 : Int)⦌)
          -- Backward pass: gradients of 1/2 the squared error.
          let mut d_out := (out -ₚ y) *ₚ out *ₚ ((1.0 : Real) -ₚ out)
          let mut d_h0 := d_out *ₚ w2⦋(0 : Int)⦌⦋(0 : Int)⦌ *ₚ h0 *ₚ ((1.0 : Real) -ₚ h0)
          let mut d_h1 := d_out *ₚ w2⦋(0 : Int)⦌⦋(1 : Int)⦌ *ₚ h1 *ₚ ((1.0 : Real) -ₚ h1)
          -- Gradient-descent step (rebuild each weight row in place).
          w2 :=
            PastaLean.pySetItem w2 (0 : Int)
              [w2⦋(0 : Int)⦌⦋(0 : Int)⦌ -ₚ lr *ₚ d_out *ₚ h0, w2⦋(0 : Int)⦌⦋(1 : Int)⦌ -ₚ lr *ₚ d_out *ₚ h1]
          b2 := ([b2⦋(0 : Int)⦌ -ₚ lr *ₚ d_out] : List Real)
          w1 :=
            PastaLean.pySetItem w1 (0 : Int)
              [w1⦋(0 : Int)⦌⦋(0 : Int)⦌ -ₚ lr *ₚ d_h0 *ₚ x⦋(0 : Int)⦌,
                w1⦋(0 : Int)⦌⦋(1 : Int)⦌ -ₚ lr *ₚ d_h0 *ₚ x⦋(1 : Int)⦌]
          w1 :=
            PastaLean.pySetItem w1 (1 : Int)
              [w1⦋(1 : Int)⦌⦋(0 : Int)⦌ -ₚ lr *ₚ d_h1 *ₚ x⦋(0 : Int)⦌,
                w1⦋(1 : Int)⦌⦋(1 : Int)⦌ -ₚ lr *ₚ d_h1 *ₚ x⦋(1 : Int)⦌]
          b1 := ([b1⦋(0 : Int)⦌ -ₚ lr *ₚ d_h0, b1⦋(1 : Int)⦌ -ₚ lr *ₚ d_h1] : List Real)
        if h_1 : (epoch +ₚ (1 : Int)) %ₚ (1000 : Int) = (0 : Int) then 
          let _ ←
            PastaLean.ProofMode.pyPrintProof
                [pyPrintArg s!"epoch {(epoch +ₚ (1 : Int))}: loss = {mean_squared_error xs ys w1 b1 w2 b2}"]
        else
          let _ := ()
      let _ ← PastaLean.ProofMode.pyPrintProof [pyPrintArg "learned predictions:"]
      for i in (PastaLean.pyRange (PastaLean.pyLen xs)) do
        let mut p := predict xs⦋i⦌ w1 b1 w2 b2
        let mut label : Int := if p > (0.5 : Real) then (1 : Int) else (0 : Int)
        let _ ←
          PastaLean.ProofMode.pyPrintProof
              [pyPrintArg s! "  {xs⦋i⦌} -> {p }  (class {label }, target {PastaLean.pyInt ys⦋i⦌})"]) :
    PastaLean.ProofMode.PyProofM _)

attribute [simp] main'

def main''rn :=
  ((do
      -- XOR is not linearly separable, so a single layer cannot solve it -- the
      -- hidden layer is what makes this learnable.
      let mut xs :=
        ([[(0.0 : Float), (0.0 : Float)], [(0.0 : Float), (1.0 : Float)], [(1.0 : Float), (0.0 : Float)],
            [(1.0 : Float), (1.0 : Float)]] :
          List (List Float))
      let mut ys := ([(0.0 : Float), (1.0 : Float), (1.0 : Float), (0.0 : Float)] : List Float)
      -- Fixed initial weights so the run is reproducible (no RNG needed).
      let mut w1 := ([[(0.5 : Float), -(0.4 : Float)], [(0.9 : Float), (1.0 : Float)]] : List (List Float))
      let mut b1 := ([(0.1 : Float), -(0.2 : Float)] : List Float)
      let mut w2 := ([[(0.7 : Float), -(0.8 : Float)]] : List (List Float))
      let mut b2 := ([(0.3 : Float)] : List Float)
      let mut lr := (0.5 : Float)
      let mut epochs : Int := (4000 : Int)
      let _ ← pyPrintIO [pyPrintArg "=== Training a neural net on XOR (NumPy + math) ==="]
      let _ ← pyPrintIO [pyPrintArg s! "initial loss: {mean_squared_error'rn xs ys w1 b1 w2 b2}"]
      for epoch in (PastaLean.pyRange epochs) do
        for i in (PastaLean.pyRange (PastaLean.pyLen xs)) do
          let mut x := xs⦋i⦌
          let mut y := ys⦋i⦌
          -- Forward pass, keeping the hidden activations for backprop.
          let mut h0 := sigmoid'rn (Libraries.numpy.pyNumpyDot x w1⦋(0 : Int)⦌ +ₚ b1⦋(0 : Int)⦌)
          let mut h1 := sigmoid'rn (Libraries.numpy.pyNumpyDot x w1⦋(1 : Int)⦌ +ₚ b1⦋(1 : Int)⦌)
          let mut hidden := ([h0, h1] : List Float)
          let mut out := sigmoid'rn (Libraries.numpy.pyNumpyDot hidden w2⦋(0 : Int)⦌ +ₚ b2⦋(0 : Int)⦌)
          -- Backward pass: gradients of 1/2 the squared error.
          let mut d_out := (out -ₚ y) *ₚ out *ₚ ((1.0 : Float) -ₚ out)
          let mut d_h0 := d_out *ₚ w2⦋(0 : Int)⦌⦋(0 : Int)⦌ *ₚ h0 *ₚ ((1.0 : Float) -ₚ h0)
          let mut d_h1 := d_out *ₚ w2⦋(0 : Int)⦌⦋(1 : Int)⦌ *ₚ h1 *ₚ ((1.0 : Float) -ₚ h1)
          -- Gradient-descent step (rebuild each weight row in place).
          w2 :=
            PastaLean.pySetItem w2 (0 : Int)
              [w2⦋(0 : Int)⦌⦋(0 : Int)⦌ -ₚ lr *ₚ d_out *ₚ h0, w2⦋(0 : Int)⦌⦋(1 : Int)⦌ -ₚ lr *ₚ d_out *ₚ h1]
          b2 := ([b2⦋(0 : Int)⦌ -ₚ lr *ₚ d_out] : List Float)
          w1 :=
            PastaLean.pySetItem w1 (0 : Int)
              [w1⦋(0 : Int)⦌⦋(0 : Int)⦌ -ₚ lr *ₚ d_h0 *ₚ x⦋(0 : Int)⦌,
                w1⦋(0 : Int)⦌⦋(1 : Int)⦌ -ₚ lr *ₚ d_h0 *ₚ x⦋(1 : Int)⦌]
          w1 :=
            PastaLean.pySetItem w1 (1 : Int)
              [w1⦋(1 : Int)⦌⦋(0 : Int)⦌ -ₚ lr *ₚ d_h1 *ₚ x⦋(0 : Int)⦌,
                w1⦋(1 : Int)⦌⦋(1 : Int)⦌ -ₚ lr *ₚ d_h1 *ₚ x⦋(1 : Int)⦌]
          b1 := ([b1⦋(0 : Int)⦌ -ₚ lr *ₚ d_h0, b1⦋(1 : Int)⦌ -ₚ lr *ₚ d_h1] : List Float)
        if h_1 : (epoch +ₚ (1 : Int)) %ₚ (1000 : Int) == (0 : Int) then 
          let _ ←
            pyPrintIO [pyPrintArg s!"epoch {(epoch +ₚ (1 : Int))}: loss = {mean_squared_error'rn xs ys w1 b1 w2 b2}"]
        else
          let _ := ()
      let _ ← pyPrintIO [pyPrintArg "learned predictions:"]
      for i in (PastaLean.pyRange (PastaLean.pyLen xs)) do
        let mut p := predict'rn xs⦋i⦌ w1 b1 w2 b2
        let mut label : Int := if p > (0.5 : Float) then (1 : Int) else (0 : Int)
        let _ ← pyPrintIO [pyPrintArg s! "  {xs⦋i⦌} -> {p }  (class {label }, target {PastaLean.pyInt ys⦋i⦌})"]) :
    IO _)

noncomputable def main : IO Unit := do
  let _ := main'
  pure ()

def main'rn : IO Unit := do
  let _ := main''rn
  pure ()