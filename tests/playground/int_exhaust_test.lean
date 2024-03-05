/-

namespace IntTest

inductive NumType where
| nat
| int
deriving BEq, Hashable

inductive NumVal where
| add (x y : NumVal) (tp : NumType)
| var (d : VarDecl NumType)
| natLit (n : Nat)
deriving Inhabited

namespace NumVal

open NumType

def addOp (tp : NumType) := mkOp [tp, tp] tp fun a => add (a[0]!) (a[1]!) tp

def natLitOp (n : Nat) := mkOp [] nat fun _ => natLit n

protected def typeOf (v : NumVal) : NumType :=
  match v with
  | add _ _ tp => tp
  | var d => d.type
  | natLit _ => .nat

instance : HasType NumVal NumType where
  typeOf := NumVal.typeOf

protected def render [Monad M] [MonadQuotation M] (v : NumVal) : M Term :=
  match v with
  | var d => do pure d.ident
  | add x y _ => do `($(←x.render) + $(←y.render))
  | natLit n => do `(($(Syntax.mkNumLit (toString n)) : Nat))

instance : Value NumVal where
  render := NumVal.render

partial def map (f : NumVal → NumVal) (v : NumVal) : NumVal :=
  match v with
  | add x y tp => add (f x) (f y) tp
  | var d => var d
  | natLit n => natLit n

partial def simp (v : NumVal) : NumVal :=
  let v := map simp v
  match v with
  | add x y _ =>
    match x, y with
--    | x, natLit 0 => x
--    | natLit 0, y => y
    | _, _ => v
  | _ => v

end NumVal

open NumVal

syntax:lead (name := intTestElab) "#intTest" : command

@[command_elab intTestElab]
def elabIntTest : CommandElab := fun stx => do
  let stats : GenStats := { maxTermSize := 7, maxDepth := 2, maxVarCount := 3 }
  let types := #[.nat, .int]
  let ops := [
      addOp .nat,
      natLitOp 0
  ]
  let varGen : List (NumType × CoreM Command) := [
      (.nat, `(variable (n : Nat))),
      (.int, `(variable (i : Int)))
  ]
  let tac : Syntax.Tactic ← `(tactic|try simp)
  runGen stx NumVal.simp varGen NumVal.var stats types ops tac

--set_option pp.all true
--#intTest

end IntTest
-/
