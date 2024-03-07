import Lean

section
open Lean Elab Meta Command

syntax:lead (name := metaliftElab) "#metalift" ident : command


def nameToIdent (nm : Name) : TermElabM Syntax.Term :=
  match nm with
  | .anonymous => `(Name.anonymous)
  | .str nm r => do `(Name.str $(←nameToIdent nm) $(Syntax.mkStrLit r))
  | .num nm r => do `(Name.num $(←nameToIdent nm) $(Syntax.mkNumLit (toString r)))

@[command_elab metaliftElab]
def elabGenTest : CommandElab := fun stx => do
  let `(command|#metalift $d) := stx | throwUnsupportedSyntax
  let typeName := d.getId
  let indVal ← getConstInfoInduct typeName
  let recName := typeName.str "rec"
  let _ ← getConstInfoRec recName
  let toExprIdent := mkIdent (typeName.str "toExpr")
  let args ←
    liftTermElabM do
      let mut args : TSyntaxArray `term := #[]
      for c in indVal.ctors do
        let ctp ← inferType (.const c [])
        let meta ← forallMetaTelescope ctp
        let ctorArgVars := meta.1

        let n := ctorArgVars.size
        log m!"Constructor {c} {n}"
        let mut val ← `(term|Lean.Expr.const $(←nameToIdent c) [])
        --let mut val ← `(term|sorry)
        let mut ctorArgs : Array Ident := .mkEmpty n
        for i in [0:n] do
          let argVar := ctorArgVars[i]!
          let argType ← inferType argVar
          let nmIdent := mkIdent s!"b{i}"
          ctorArgs := ctorArgs.push nmIdent
          let .const argTypeName [] := argType | throwError "Expected constant {argType}"
          let argVal ←
                if argTypeName == typeName then
                  `($toExprIdent $nmIdent)
                else if argTypeName == ``Nat then
                  `(Lean.ToExpr.toExpr $nmIdent)
                else
                  throwError "Unexpected constant {argType}"
          val := ←`(term|Lean.Expr.app $val $argVal)
        for i in [0:n] do
          let nmIdent := ctorArgs[n-1-i]!
          val := ←`(term| fun $nmIdent => $val)
        ctorArgs := ctorArgs.reverse

        args := args.push val
      pure args
  let typeIdent := mkIdent typeName
  let casesOnIdent := mkIdent (typeName.str "casesOn")
  elabCommand (←`(command|
    def $toExprIdent (t : $typeIdent) := @$casesOnIdent (fun _ => Lean.Expr) t $args*))

end

inductive Term where
| cns (x : Nat)
| add (x y : Term)


#print
#metalift Bool
#metalift Term

#print Term.toExpr
--set_option pp.all true
#eval Term.toExpr (.cns 0)
#print BoolVal.bar.match_1

partial def listOfExprAux (a : List Expr) (e : Expr) : MetaM (List Expr) := do
  let e ← whnf e
  match e with
  | .app (.app (.app (.const ``List.cons [_u]) _tp) h) e =>
    listOfExprAux (h :: a) e
  | .app (.const ``List.nil [_u]) _tp =>
    pure a.reverse
  | _ =>
    throwError s!"Could not parse {e}"

def listOfExpr (e : Expr) : MetaM (List Expr) := listOfExprAux [] e

structure Match where
  eq : Expr

instance : BEq Match where
  beq _ _ := false -- FIXME?

def matchDtConfig : WhnfCoreConfig := {}

def addMatchProp (d : DiscrTree Match) (p : Expr) : MetaM (DiscrTree Match) := do
  let pa ← withReducible (forallMetaTelescopeReducing p)
  let eq := pa.2.2
  let pat ←
    match eq with
    | .app (.app (.app (.const `Eq [_]) _) lhs) _ => pure lhs
    | _ =>
      throwError m!"Could not interpret {eq} as equation."
  let keys ←  DiscrTree.mkPath pat matchDtConfig
  let ma : Match := { eq }
  pure <| d.insertCore keys ma

def mkDiscrTree (rules : List Expr) : MetaM (DiscrTree Match):= do
  rules.foldlM (init := DiscrTree.empty) addMatchProp

/-run_meta do
  let l ← listOfExpr (.const ``Rules [])
  let t ← mkDiscrTree l
  throwError s!"Parsed {l.length}"
  pure ()

partial def simp_from_rules [h : ToExpr BoolVal] (rules : List Prop) (v : BoolVal) : MetaM BoolVal := do
  let t ← mkDiscrTree rules
  let e := toExpr v


  -- Discrimination tree
  -- Lift
  sorry

-/

namespace Quot

structure Context where
  mainModule : Name
  ref : Syntax
  currMacroScope : MacroScope


end Quot

def QuotM := ReaderT Quot.Context (StateM MacroScope)

namespace QuotM

instance : Monad QuotM := inferInstanceAs (Monad (ReaderT _ _))
local instance : MonadReader Quot.Context QuotM := inferInstanceAs (MonadReader _ (ReaderT _ _))
local instance : MonadState MacroScope QuotM := inferInstanceAs (MonadState _ (ReaderT _ _))

protected def withFreshMacroScope (m : QuotM α) : QuotM α := do
  let fresh ← modifyGet (fun s => (s, s + 1))
  ReaderT.adapt ({· with currMacroScope := fresh }) m

instance : MonadQuotation QuotM where
  getRef := return (← read).ref
  withRef ref := ReaderT.adapt ({ · with ref })
  getCurrMacroScope := return (← read).currMacroScope
  getMainModule := return (← read).mainModule
  withFreshMacroScope := QuotM.withFreshMacroScope

end QuotM

inductive App (α : Type) where
| mkApp (op : QuotM Term) (args : Array α)

export App (mkApp)

/-
def getConstInfoRec [Monad m] [MonadEnv m] [MonadError m] (constName : Name) : m RecursorVal := do
  match (← getConstInfo constName) with
  | ConstantInfo.recInfo v => pure v
  | _                      => throwError "'{mkConst constName}' is not a recursor"
-/

def Rules : List Prop := [
  ∀tp,     decide (trueVal tp)  = trueVal bool,
  ∀tp,     decide (falseVal tp) = falseVal bool,
  ∀tp x,   decide (not x tp) = decide x,
  ∀tp x y, decide (and x y tp) = (decide x &&& decide y),
  ∀tp x y, decide (or  x y tp) = (decide x ||| decide y),
  ∀x y,    decide (implies x y) = ~(decide x) ||| decide y,
  ∀x y,    decide (eq x y .iffProp) = eq (decide x) (decide y) .beqBool,
  ∀x op,   decide (eq x (trueVal  bool) op) = x,
  ∀x op,   decide (eq x (falseVal bool) op) = ~x,
  ∀x y,    decide (eq x y .eqBool)  = eq x y .beqBool,
  ∀x y,    decide (eq x y .eqProp)  = eq (decide x) (decide y) .beqBool,
  ∀x y,    decide (eq x y .iffProp) = eq (decide x) (decide y) .beqBool,
  ∀c t f,  decide (ite c t f .iteProp) = ite c (decide t) (decide f) .iteBool
  ]
