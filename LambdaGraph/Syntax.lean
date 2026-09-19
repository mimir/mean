module

import Lean

import LambdaGraph.Basic

declare_syntax_cat lambdag_op
syntax "+" : lambdag_op
syntax "-" : lambdag_op
syntax "*" : lambdag_op
syntax "=" : lambdag_op
syntax "≠" : lambdag_op
syntax "≤" : lambdag_op
syntax "<" : lambdag_op
syntax "∧" : lambdag_op
syntax "∨" : lambdag_op
syntax "↮" : lambdag_op

open Lean in
meta def expandOp : TSyntax `lambdag_op → MacroM Term
  | `(lambdag_op| +) => `(Expr.ofOp Op.add)
  | `(lambdag_op| -) => `(Expr.ofOp Op.sub)
  | `(lambdag_op| *) => `(Expr.ofOp Op.mul)
  | `(lambdag_op| =) => `(Expr.ofCmp Cmp.eq)
  | `(lambdag_op| ≠) => `(Expr.ofCmp Cmp.ne)
  | `(lambdag_op| ≤) => `(Expr.ofCmp Cmp.le)
  | `(lambdag_op| <) => `(Expr.ofCmp Cmp.lt)
  | `(lambdag_op| ∧) => `(Expr.ofLogic Logic.and)
  | `(lambdag_op| ∨) => `(Expr.ofLogic Logic.or)
  | `(lambdag_op| ↮) => `(Expr.ofLogic Logic.xor)
  | _ => Macro.throwUnsupported

declare_syntax_cat lambdag_expr (behavior := symbol)

syntax:max "var" "[" num "]" : lambdag_expr
syntax:max "[" num "]" : lambdag_expr
syntax "(" ")" : lambdag_expr
syntax "false" : lambdag_expr
syntax "true" : lambdag_expr
syntax:max num : lambdag_expr
syntax "-" num : lambdag_expr
syntax "[" lambdag_op "]" : lambdag_expr
syntax:arg lambdag_expr:arg ppSpace lambdag_expr:max : lambdag_expr
syntax "(" lambdag_expr ", " lambdag_expr ")" : lambdag_expr
syntax "if " lambdag_expr:min " then " lambdag_expr " else " lambdag_expr : lambdag_expr
syntax:max lambdag_expr:max ".0" : lambdag_expr
syntax:max lambdag_expr:max ".1" : lambdag_expr
syntax "(" lambdag_expr ")" : lambdag_expr

macro:65 e₁:lambdag_expr:65 " + " e₂:lambdag_expr:66 : lambdag_expr =>
  `(lambdag_expr| [+] ($e₁, $e₂))
macro:65 e₁:lambdag_expr:65 " - " e₂:lambdag_expr:66 : lambdag_expr =>
  `(lambdag_expr| [-] ($e₁, $e₂))
macro:70 e₁:lambdag_expr:70 " * " e₂:lambdag_expr:71 : lambdag_expr =>
  `(lambdag_expr| [*] ($e₁, $e₂))
macro:50 e₁:lambdag_expr:51 " = " e₂:lambdag_expr:51 : lambdag_expr =>
  `(lambdag_expr| [=] ($e₁, $e₂))
macro:50 e₁:lambdag_expr:51 " ≠ " e₂:lambdag_expr:51 : lambdag_expr =>
  `(lambdag_expr| [≠] ($e₁, $e₂))
macro:50 e₁:lambdag_expr:51 " ≤ " e₂:lambdag_expr:51 : lambdag_expr =>
  `(lambdag_expr| [≤] ($e₁, $e₂))
macro:50 e₁:lambdag_expr:51 " < " e₂:lambdag_expr:51 : lambdag_expr =>
  `(lambdag_expr| [<] ($e₁, $e₂))
macro:35 e₁:lambdag_expr:36 " ∧ " e₂:lambdag_expr:35 : lambdag_expr =>
  `(lambdag_expr| [∧] ($e₁, $e₂))
macro:30 e₁:lambdag_expr:31 " ∨ " e₂:lambdag_expr:30 : lambdag_expr =>
  `(lambdag_expr| [∨] ($e₁, $e₂))
macro:32 e₁:lambdag_expr:33 " ↮ " e₂:lambdag_expr:32 : lambdag_expr =>
  `(lambdag_expr| [↮] ($e₁, $e₂))

open Lean in
meta partial def expandExpr (stx : Syntax) : MacroM Term := do
  -- Only infix operators need to be expanded, so doing it once is enough.
  let stx := (← Macro.expandMacro? stx).getD stx
  match stx with
  | `(lambdag_expr| var[$n]) => `(Expr.var $n)
  | `(lambdag_expr| [$n:num]) => `(Expr.fn $n)
  | `(lambdag_expr| ()) => `(Expr.unit)
  | `(lambdag_expr| false) => `(Expr.ofBool false)
  | `(lambdag_expr| true) => `(Expr.ofBool true)
  | `(lambdag_expr| $n:num) => `(Expr.ofInt $n)
  | `(lambdag_expr| -$n:num) => `(Expr.ofInt (-$n))
  | `(lambdag_expr| [$o:lambdag_op]) => expandOp o
  | `(lambdag_expr| $f $e) => do
    `(Expr.app $(← expandExpr f) $(← expandExpr e))
  | `(lambdag_expr| ($e₁, $e₂)) => do
    `(Expr.pair $(← expandExpr e₁) $(← expandExpr e₂))
  | `(lambdag_expr| if $c then $et else $ef) => do
    `(Expr.cond $(← expandExpr c) $(← expandExpr et) $(← expandExpr ef))
  | `(lambdag_expr| $e.0) => do
    `(Expr.proj $(← expandExpr e) 0)
  | `(lambdag_expr| $e.1) => do
    `(Expr.proj $(← expandExpr e) 1)
  | `(lambdag_expr| ($e)) => expandExpr e
  | _ => Macro.throwUnsupported

macro "expr" "(" e:lambdag_expr ")" : term => expandExpr e

declare_syntax_cat lambdag_ty

syntax "⊥" : lambdag_ty
syntax "[" "]" : lambdag_ty
syntax "bool" : lambdag_ty
syntax "int" : lambdag_ty
syntax:25 lambdag_ty:26 " → " lambdag_ty:25 : lambdag_ty
syntax "[" lambdag_ty ", " lambdag_ty "]" : lambdag_ty

open Lean in
meta partial def expandTy : TSyntax `lambdag_ty → MacroM Term
  | `(lambdag_ty| ⊥) => `(Ty.bot)
  | `(lambdag_ty| []) => `(Ty.unit)
  | `(lambdag_ty| bool) => `(Ty.bool)
  | `(lambdag_ty| int) => `(Ty.int)
  | `(lambdag_ty| $t₁ → $t₂) => do
    `(Ty.fn $(← expandTy t₁) $(← expandTy t₂))
  | `(lambdag_ty| [$t₁, $t₂]) => do
    `(Ty.prod $(← expandTy t₁) $(← expandTy t₂))
  | _ => Macro.throwUnsupported

macro "ty" "(" t:lambdag_ty ")" : term => expandTy t

declare_syntax_cat lambdag_fn

syntax "λ " lambdag_ty:26 " → " lambdag_ty:25 ". " lambdag_expr : lambdag_fn

open Lean in
meta partial def expandFn : TSyntax `lambdag_fn → MacroM Term
  | `(lambdag_fn| λ $t₁ → $t₂. $e) => do
    `(($(← expandTy t₁), $(← expandTy t₂), $(← expandExpr e)))
  | _ => Macro.throwUnsupported

syntax "prog " ppLine withPosition((colEq lambdag_fn)*) : term

macro_rules
  | `(term| prog $fns*) => do
    let fns ← fns.mapM expandFn
    `(Program.ofList [$fns,*])
