import Lean.Util.TestNormalForms

open Lean
open Lean.Elab.Command (CommandElab)
open Lean.Test.NormalForms

namespace Nat

attribute [simp] mod_one

end Nat

namespace Int

attribute [simp] emod_self

@[simp] theorem zero_bdiv : bdiv 0 n = 0 := by sorry

@[simp] theorem bdiv_one : bdiv m 1 = 0 := by sorry

end Int

inductive NumType where
| nat
| int
deriving BEq, Hashable, Inhabited, Repr

protected def NumType.render [Monad M] [MonadQuotation M] (v : NumType) : M Term := do
  match v with
  | nat => `(Nat)
  | int => `(Int)

inductive  DivMode where
| divNat
| edivInt
| fdivInt
| tdivInt
| bdivInt
deriving BEq, Repr

def DivMode.typeOf (m : DivMode) : NumType :=
  match m with
  | divNat => .nat
  | edivInt => .int
  | fdivInt => .int
  | tdivInt => .int
  | bdivInt => .int

inductive NumTerm where
  | var (d : VarDecl NumType)
  | lit (n : Nat) (tp : NumType)
  | natToInt (x : NumTerm)
  | intToNat (x : NumTerm)
  | add (x y : NumTerm) (tp : NumType)
  | sub (x y : NumTerm) (tp : NumType)
  | neg (x : NumTerm) (tp : NumType)
  | mul (x y : NumTerm) (tp : NumType)
  | div (x y : NumTerm) (m : DivMode)
  | mod (x y : NumTerm) (m : DivMode)
  deriving BEq, Inhabited, Repr

namespace NumTerm

open NumType

partial def map (f : NumTerm → NumTerm) (v : NumTerm) : NumTerm :=
  match v with
  | var _ | lit _ _ => v
  | natToInt x => natToInt (f x)
  | intToNat x => intToNat (f x)
  | add x y tp => add (f x) (f y) tp
  | sub x y tp => sub (f x) (f y) tp
  | neg x tp => neg (f x) tp
  | mul x y tp => mul (f x) (f y) tp
  | div x y op => div (f x) (f y) op
  | mod x y op => mod (f x) (f y) op

protected def typeOf (v : NumTerm) : NumType :=
  match v with
  | var d => d.type
  | lit _ tp => tp
  | natToInt _ => .int
  | intToNat _ => .nat
  | add _ _ tp => tp
  | sub _ _ tp => tp
  | neg _   tp => tp
  | mul _ _ tp => tp
  | div _ _ op => op.typeOf
  | mod _ _ op => op.typeOf

protected def render [Monad M] [MonadQuotation M] (v : NumTerm) : M Term := do
  match v with
  | var d => pure d.ident
  | lit n tp => `(($(Syntax.mkNumLit (toString n)) : $(←tp.render)))
  | natToInt x => `((($(←x.render) : Nat) : Int))
  | intToNat x => `((($(←x.render) : Int) : Nat))
  | add x y tp => `((($(←x.render) + $(←y.render)) : $(←tp.render)))
  | sub x y _ => `($(←x.render) - $(←y.render))
  | neg x _   => `(- $(←x.render))
  | mul x y _ => `($(←x.render) * $(←y.render))
  | div x y op =>
    match op with
    | .divNat  => `($(←x.render) / $(←y.render))
    | .edivInt => `($(←x.render) / $(←y.render))
    | .fdivInt => `(Int.fdiv $(←x.render) $(←y.render))
    | .tdivInt => `(Int.div  $(←x.render) $(←y.render))
    | .bdivInt => `(Int.bdiv $(←x.render) $(←y.render))
  | mod x y op =>
    match op with
    | .divNat  => `($(←x.render) % $(←y.render))
    | .edivInt => `($(←x.render) % $(←y.render))
    | .fdivInt => `(Int.fmod $(←x.render) $(←y.render))
    | .tdivInt => `(Int.mod  $(←x.render) $(←y.render))
    | .bdivInt => `(Int.bmod $(←x.render) $(←y.render))

instance : GenTerm NumTerm NumType where
  render := NumTerm.render
  mkVar := NumTerm.var

def intLit (i : Int) : NumTerm :=
  if i < 0 then
    neg (lit ((- i).toNat) .int) .int
  else
    lit i.toNat .int

partial def simp (v : NumTerm) : NumTerm :=
  let v := map simp v
  match v with
  | natToInt x =>
    (match x with
    | lit n _ => lit n .int
    | add x y _ => add (natToInt x) (natToInt y) .int
    | mul x y _ => mul (natToInt x) (natToInt y) .int
    | div x y _ => div (natToInt x) (natToInt y) .edivInt
    | mod x y _ => mod (natToInt x) (natToInt y) .edivInt
    | var _ | sub _ _ _ | neg _ _ | intToNat _ | natToInt _ => v)
  | add x y tp =>
    match x, y with
    | x, lit 0 _ => x
    | lit 0 _, y => y
    | lit i _, lit j _ => lit (i+j) tp
    | _, _ => v
  | sub x y tp =>
    match x, y, tp with
    | x, lit 0 _, _ => x
    | lit i _, lit j _, .nat => lit (i-j) tp
    | lit i _, lit j _, .int => intLit ((i : Int) - (j : Int))
    | lit 0 _, _, .nat => lit 0 .nat
    | lit 0 _, y, .int => simp (neg y .int)
    | x, y, _ =>
      if x == y then
        .lit 0 tp
      else
        v
  | neg x _ =>
    match x with
    | lit n _ => intLit (- (Int.ofNat n))
    | _ => v
  | mul x y tp =>
    match x, y with
    | _, lit 0 _ => y
    | lit 0 _, _ => x
    | _, lit 1 _ => x
    | lit 1 _, _ => y
    | lit i _, lit j _ => lit (i*j) tp
    | _, _ => v
  | div x y _op =>
    if let lit 0 _ := x then
      x
    else if let lit 0 _ := y then
      y
    else if let lit 1 _ := y then
      x
    else
      v
  | mod x y op =>
    if let lit 0 _ := x then
      x
    else if let lit 0 _ := y then
      x
    else if let lit 1 _ := y then
      lit 0 op.typeOf
    else if x == y then
      lit 0 op.typeOf
    else
      v
  | _ => v

partial def simpv (u : NumTerm) : NumTerm :=
  let v := simp u
  if v.typeOf == u.typeOf then
    v
  else
    panic! s!"{repr u} has changed types."

def litOp (n : Nat) (tp : NumType) := mkOp [] tp fun _ => lit n tp
def addOp (tp : NumType) := mkOp [tp, tp] tp fun a => add (a[0]!) (a[1]!) tp
def subOp (tp : NumType) := mkOp [tp, tp] tp fun a => sub (a[0]!) (a[1]!) tp
def negOp (tp : NumType) := mkOp [tp] tp fun a => neg (a[0]!) tp
def mulOp (tp : NumType) := mkOp [tp, tp] tp fun a => mul (a[0]!) (a[1]!) tp
def divOp (op : DivMode) (dtp := op.typeOf) := let tp := op.typeOf; mkOp [tp, dtp] tp fun a => div (a[0]!) (a[1]!) op
def modOp (op : DivMode) (dtp := op.typeOf) := let tp := op.typeOf; mkOp [tp, dtp] tp fun a => mod (a[0]!) (a[1]!) op

end NumTerm

open NumTerm

syntax:lead (name := intTestElab) "#intTest" : command

@[command_elab intTestElab]
def elabIntTest : CommandElab := fun _stx => do
  let types : List NumType := [.nat, .int]
  let ops := [
      litOp 0 .nat,
      litOp 1 .nat,
      litOp 0 .int,
      litOp 1 .int,
      addOp .nat, addOp .int,
      subOp .nat, subOp .int,
      negOp .int,
      mulOp .nat, mulOp .int,
      divOp .divNat, divOp .edivInt, divOp .fdivInt, divOp .tdivInt, divOp .bdivInt .nat,
      modOp .divNat, modOp .edivInt, modOp .fdivInt, modOp .tdivInt, divOp .bdivInt .nat,
  ]
  let vars : List (NumType × CoreM Command) := [
      (.nat, `(variable (n : Nat))),
      (.int, `(variable (i : Int)))
  ]
  let stats : GenStats := { maxTermSize := 7, maxDepth := 2, maxVarCount := 3 }
  testNormalForms types ops vars NumTerm.simpv stats

--set_option pp.coercions false
--set_option pp.explicit true
#intTest
