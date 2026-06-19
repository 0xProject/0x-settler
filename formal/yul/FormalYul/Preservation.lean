import FormalYul.Runtime
import Init.Data.Fin.Bitwise
import Batteries.Data.RBMap.Lemmas
import Batteries.Data.UInt

namespace FormalYul

namespace Preservation

open EvmYul
open EvmYul.Yul
open EvmYul.Yul.Ast

attribute [simp] Finmap.lookup_insert Finmap.lookup_insert_of_ne

@[simp]
theorem functionDefinition_params_def
    (params rets : List EvmYul.Identifier) (body : List EvmYul.Yul.Ast.Stmt) :
    (EvmYul.Yul.Ast.FunctionDefinition.Def params rets body).params = params := rfl

@[simp]
theorem functionDefinition_rets_def
    (params rets : List EvmYul.Identifier) (body : List EvmYul.Yul.Ast.Stmt) :
    (EvmYul.Yul.Ast.FunctionDefinition.Def params rets body).rets = rets := rfl

@[simp]
theorem functionDefinition_body_def
    (params rets : List EvmYul.Identifier) (body : List EvmYul.Yul.Ast.Stmt) :
    (EvmYul.Yul.Ast.FunctionDefinition.Def params rets body).body = body := rfl

@[simp]
theorem lookup_insert_same
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (name : EvmYul.Identifier) (value : EvmYul.UInt256) :
    EvmYul.Yul.State.lookup! name
      ((EvmYul.Yul.State.Ok shared store).insert name value) = value := by
  simp [EvmYul.Yul.State.insert, EvmYul.Yul.State.lookup!, Finmap.lookup_insert]

@[simp]
theorem lookup_insert_ne
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (name other : EvmYul.Identifier) (value : EvmYul.UInt256) (h : other ≠ name) :
    EvmYul.Yul.State.lookup! other
      ((EvmYul.Yul.State.Ok shared store).insert name value) =
      (EvmYul.Yul.State.Ok shared store).lookup! other := by
  simp [EvmYul.Yul.State.insert, EvmYul.Yul.State.lookup!, Finmap.lookup_insert_of_ne,
    h]

@[simp]
theorem getElem_insert_same
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (name : EvmYul.Identifier) (value : EvmYul.UInt256) :
    ((EvmYul.Yul.State.Ok shared store).insert name value)[name]! = value := by
  simp [GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.store, EvmYul.Yul.State.insert,
    Finmap.lookup_insert, Finmap.mem_insert]

@[simp]
theorem getElem_insert_ne
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (name other : EvmYul.Identifier) (value : EvmYul.UInt256) (h : other ≠ name) :
    ((EvmYul.Yul.State.Ok shared store).insert name value)[other]! =
      (EvmYul.Yul.State.Ok shared store)[other]! := by
  simp [GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.store, EvmYul.Yul.State.insert,
    Finmap.lookup_insert_of_ne, h]

@[simp]
theorem getElem_ok_store_insert_same
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (name : EvmYul.Identifier) (value : EvmYul.UInt256) :
    (EvmYul.Yul.State.Ok shared (store.insert name value))[name]! = value := by
  simp [GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.store, Finmap.lookup_insert,
    Finmap.mem_insert]

@[simp]
theorem getElem_ok_store_insert_ne
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (name other : EvmYul.Identifier) (value : EvmYul.UInt256) (h : other ≠ name) :
    (EvmYul.Yul.State.Ok shared (store.insert name value))[other]! =
      (EvmYul.Yul.State.Ok shared store)[other]! := by
  simp [GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.store, Finmap.lookup_insert_of_ne,
    h]

@[simp]
theorem getElem_ok_finmap_insert_same
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (name : EvmYul.Identifier) (value : EvmYul.UInt256) :
    (EvmYul.Yul.State.Ok shared (Finmap.insert name value store))[name]! = value := by
  simp [GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.store]

@[simp]
theorem getElem_ok_finmap_insert_ne
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (name other : EvmYul.Identifier) (value : EvmYul.UInt256) (h : other ≠ name) :
    (EvmYul.Yul.State.Ok shared (Finmap.insert name value store))[other]! =
      (EvmYul.Yul.State.Ok shared store)[other]! := by
  simp [GetElem?.getElem!, decidableGetElem?,
    EvmYul.Yul.State.instGetElemIdentifierLiteralMemVarStoreStore,
    EvmYul.Yul.State.lookup!, EvmYul.Yul.State.store, h]

@[simp]
theorem multifill_single_ok
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (name : EvmYul.Identifier) (value : EvmYul.UInt256) :
    EvmYul.Yul.State.multifill [name] [value] (EvmYul.Yul.State.Ok shared store) =
      (EvmYul.Yul.State.Ok shared store).insert name value := by
  rfl

@[simp]
theorem multifill_nil_ok
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.State.multifill [] [] (EvmYul.Yul.State.Ok shared store) =
      EvmYul.Yul.State.Ok shared store := rfl

@[simp]
theorem setStore_ok
    (shared shared' : EvmYul.SharedState .Yul)
    (store store' : EvmYul.Yul.VarStore) :
    EvmYul.Yul.State.setStore (EvmYul.Yul.State.Ok shared store)
      (EvmYul.Yul.State.Ok shared' store') =
      EvmYul.Yul.State.Ok shared store' := rfl

@[simp]
theorem setMachineState_ok
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (mstate : EvmYul.MachineState) :
    EvmYul.Yul.State.setMachineState mstate (EvmYul.Yul.State.Ok shared store) =
      EvmYul.Yul.State.Ok { shared with toMachineState := mstate } store := rfl

@[simp]
theorem accountMapFor_find_contractOwner (contract : YulContract) :
    (accountMapFor contract).find? contractOwner = some (accountFor contract) := by
  unfold accountMapFor
  rw [Batteries.RBMap.find?_insert_of_eq]
  simp [contractOwner]

@[simp]
theorem sharedFor_account_lookup (contract : YulContract) (input : ByteArray) :
    (sharedFor contract input).accountMap.find?
        (sharedFor contract input).executionEnv.codeOwner =
      some (accountFor contract) := by
  simp [sharedFor, envFor]

@[simp]
theorem exec_block_nil
    (fuel : Nat) (code : Option EvmYul.Yul.Ast.YulContract) (s : EvmYul.Yul.State) :
    EvmYul.Yul.exec fuel.succ (EvmYul.Yul.Ast.Stmt.Block []) code s = .ok s := by
  rw [EvmYul.Yul.exec.eq_def]

@[simp]
theorem exec_block_cons
    (fuel : Nat) (stmt : EvmYul.Yul.Ast.Stmt) (stmts : List EvmYul.Yul.Ast.Stmt)
    (code : Option EvmYul.Yul.Ast.YulContract) (s : EvmYul.Yul.State) :
    EvmYul.Yul.exec fuel.succ (EvmYul.Yul.Ast.Stmt.Block (stmt :: stmts)) code s =
      match EvmYul.Yul.exec fuel stmt code s with
      | .error e => .error e
      | .ok s1 => EvmYul.Yul.exec fuel (EvmYul.Yul.Ast.Stmt.Block stmts) code s1 := by
  rw [EvmYul.Yul.exec.eq_def]
  simp only
  rfl

theorem returnOf_multifill_nil
    (r : Except EvmYul.Yul.Exception (EvmYul.Yul.State × List EvmYul.Literal)) :
    (match EvmYul.Yul.multifill' [] r with
      | Except.ok state => Except.ok (FormalYul.returnOf state)
      | Except.error (.YulHalt state _) => Except.ok (FormalYul.returnOf state)
      | Except.error .Revert => Except.error "revert"
      | Except.error err => Except.error (reprStr err)) =
    (match r with
      | Except.ok (state, _) => Except.ok (FormalYul.returnOf state)
      | Except.error (.YulHalt state _) => Except.ok (FormalYul.returnOf state)
      | Except.error .Revert => Except.error "revert"
      | Except.error err => Except.error (reprStr err)) := by
  cases r with
  | error e => cases e <;> rfl
  | ok p =>
      cases p with
      | mk state rets =>
          cases state <;> rfl

theorem returnOf_exec_block_nil
    (fuel : Nat) (code : Option EvmYul.Yul.Ast.YulContract)
    (r : Except EvmYul.Yul.Exception EvmYul.Yul.State) :
    (match (match r with
      | Except.error e => Except.error e
      | Except.ok state =>
          EvmYul.Yul.exec fuel.succ (EvmYul.Yul.Ast.Stmt.Block []) code state) with
      | Except.ok state => Except.ok (FormalYul.returnOf state)
      | Except.error (.YulHalt state _) => Except.ok (FormalYul.returnOf state)
      | Except.error .Revert => Except.error "revert"
      | Except.error err => Except.error (reprStr err)) =
    (match r with
      | Except.ok state => Except.ok (FormalYul.returnOf state)
      | Except.error (.YulHalt state _) => Except.ok (FormalYul.returnOf state)
      | Except.error .Revert => Except.error "revert"
      | Except.error err => Except.error (reprStr err)) := by
  cases r with
  | error e => cases e <;> rfl
  | ok state =>
      simp [EvmYul.Yul.exec.eq_def]

@[simp]
theorem exec_let_lit
    (fuel : Nat) (vars : List EvmYul.Identifier) (lit : EvmYul.Literal)
    (code : Option EvmYul.Yul.Ast.YulContract) (s : EvmYul.Yul.State) :
    EvmYul.Yul.exec fuel.succ
        (EvmYul.Yul.Ast.Stmt.Let vars (.some (EvmYul.Yul.Ast.Expr.Lit lit))) code s =
      .ok (s.insert vars.head! lit) := by
  rw [EvmYul.Yul.exec.eq_def]

@[simp]
theorem exec_let_var
    (fuel : Nat) (vars : List EvmYul.Identifier) (id : EvmYul.Identifier)
    (code : Option EvmYul.Yul.Ast.YulContract) (s : EvmYul.Yul.State) :
    EvmYul.Yul.exec fuel.succ
        (EvmYul.Yul.Ast.Stmt.Let vars (.some (EvmYul.Yul.Ast.Expr.Var id))) code s =
      .ok (s.insert vars.head! s[id]!) := by
  rw [EvmYul.Yul.exec.eq_def]

@[simp]
theorem exec_let_prim
    (fuel : Nat) (vars : List EvmYul.Identifier) (prim : EvmYul.Operation .Yul)
    (args : List EvmYul.Yul.Ast.Expr) (code : Option EvmYul.Yul.Ast.YulContract)
    (s : EvmYul.Yul.State) :
    EvmYul.Yul.exec fuel.succ
        (EvmYul.Yul.Ast.Stmt.Let vars (.some (EvmYul.Yul.Ast.Expr.Call (.inl prim) args)))
        code s =
      EvmYul.Yul.execPrimCall fuel prim vars
        (EvmYul.Yul.reverse' (EvmYul.Yul.evalArgs fuel args.reverse code s)) := by
  rw [EvmYul.Yul.exec.eq_def]

@[simp]
theorem exec_let_call
    (fuel : Nat) (vars : List EvmYul.Identifier) (fn : EvmYul.Yul.Ast.YulFunctionName)
    (args : List EvmYul.Yul.Ast.Expr) (code : Option EvmYul.Yul.Ast.YulContract)
    (s : EvmYul.Yul.State) :
    EvmYul.Yul.exec fuel.succ
        (EvmYul.Yul.Ast.Stmt.Let vars (.some (EvmYul.Yul.Ast.Expr.Call (.inr fn) args)))
        code s =
      EvmYul.Yul.execCall fuel fn vars code
        (EvmYul.Yul.reverse' (EvmYul.Yul.evalArgs fuel args.reverse code s)) := by
  rw [EvmYul.Yul.exec.eq_def]

@[simp]
theorem exec_if
    (fuel : Nat) (cond : EvmYul.Yul.Ast.Expr) (body : List EvmYul.Yul.Ast.Stmt)
    (code : Option EvmYul.Yul.Ast.YulContract) (s : EvmYul.Yul.State) :
    EvmYul.Yul.exec fuel.succ (EvmYul.Yul.Ast.Stmt.If cond body) code s =
      match EvmYul.Yul.eval fuel cond code s with
      | .error e => .error e
      | .ok (s, cond) =>
          if cond ≠ (⟨0⟩ : EvmYul.UInt256) then
            EvmYul.Yul.exec fuel (EvmYul.Yul.Ast.Stmt.Block body) code s
          else
            .ok s := by
  rw [EvmYul.Yul.exec.eq_def]
  simp only
  rfl

@[simp]
theorem exec_leave
    (fuel : Nat) (code : Option EvmYul.Yul.Ast.YulContract) (s : EvmYul.Yul.State) :
    EvmYul.Yul.exec fuel.succ EvmYul.Yul.Ast.Stmt.Leave code s =
      .ok (EvmYul.Yul.State.setLeave s) := by
  rw [EvmYul.Yul.exec.eq_def]

@[simp]
theorem exec_exprstmt_prim
    (fuel : Nat) (prim : EvmYul.Operation .Yul) (args : List EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract) (s : EvmYul.Yul.State) :
    EvmYul.Yul.exec fuel.succ
        (EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (.inl prim) args)) code s =
      EvmYul.Yul.execPrimCall fuel prim []
        (EvmYul.Yul.reverse' (EvmYul.Yul.evalArgs fuel args.reverse code s)) := by
  rw [EvmYul.Yul.exec.eq_def]

@[simp]
theorem exec_exprstmt_call
    (fuel : Nat) (fn : EvmYul.Yul.Ast.YulFunctionName)
    (args : List EvmYul.Yul.Ast.Expr) (code : Option EvmYul.Yul.Ast.YulContract)
    (s : EvmYul.Yul.State) :
    EvmYul.Yul.exec fuel.succ
        (EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (.inr fn) args)) code s =
      EvmYul.Yul.execCall fuel fn [] code
        (EvmYul.Yul.reverse' (EvmYul.Yul.evalArgs fuel args.reverse code s)) := by
  rw [EvmYul.Yul.exec.eq_def]

@[simp]
theorem exec_switch
    (fuel : Nat) (cond : EvmYul.Yul.Ast.Expr)
    (cases : List (EvmYul.Literal × List EvmYul.Yul.Ast.Stmt))
    (defaultStmts : List EvmYul.Yul.Ast.Stmt) (code : Option EvmYul.Yul.Ast.YulContract)
    (s : EvmYul.Yul.State) :
    EvmYul.Yul.exec fuel.succ (EvmYul.Yul.Ast.Stmt.Switch cond cases defaultStmts) code s =
      match EvmYul.Yul.eval fuel cond code s with
      | .error e => .error e
      | .ok (s1, cond) =>
          match EvmYul.Yul.selectSwitchCase cond cases with
          | .some stmts => EvmYul.Yul.exec fuel (EvmYul.Yul.Ast.Stmt.Block stmts) code s1
          | .none => EvmYul.Yul.exec fuel (EvmYul.Yul.Ast.Stmt.Block defaultStmts) code s1 := by
  rw [EvmYul.Yul.exec.eq_def]
  simp only
  rfl

@[simp]
theorem eval_lit
    (fuel : Nat) (lit : EvmYul.Literal) (code : Option EvmYul.Yul.Ast.YulContract)
    (s : EvmYul.Yul.State) :
    EvmYul.Yul.eval fuel.succ (EvmYul.Yul.Ast.Expr.Lit lit) code s = .ok (s, lit) := by
  rw [EvmYul.Yul.eval.eq_def]

@[simp]
theorem eval_var
    (fuel : Nat) (id : EvmYul.Identifier) (code : Option EvmYul.Yul.Ast.YulContract)
    (s : EvmYul.Yul.State) :
    EvmYul.Yul.eval fuel.succ (EvmYul.Yul.Ast.Expr.Var id) code s = .ok (s, s[id]!) := by
  rw [EvmYul.Yul.eval.eq_def]

@[simp]
theorem eval_prim
    (fuel : Nat) (prim : EvmYul.Operation .Yul) (args : List EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract) (s : EvmYul.Yul.State) :
    EvmYul.Yul.eval fuel.succ (EvmYul.Yul.Ast.Expr.Call (.inl prim) args) code s =
      EvmYul.Yul.evalPrimCall fuel prim
        (EvmYul.Yul.reverse' (EvmYul.Yul.evalArgs fuel args.reverse code s)) := by
  rw [EvmYul.Yul.eval.eq_def]

@[simp]
theorem eval_call
    (fuel : Nat) (fn : EvmYul.Yul.Ast.YulFunctionName) (args : List EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract) (s : EvmYul.Yul.State) :
    EvmYul.Yul.eval fuel.succ (EvmYul.Yul.Ast.Expr.Call (.inr fn) args) code s =
      EvmYul.Yul.evalCall fuel fn code
        (EvmYul.Yul.reverse' (EvmYul.Yul.evalArgs fuel args.reverse code s)) := by
  rw [EvmYul.Yul.eval.eq_def]

@[simp]
theorem evalArgs_nil
    (fuel : Nat) (code : Option EvmYul.Yul.Ast.YulContract) (s : EvmYul.Yul.State) :
    EvmYul.Yul.evalArgs fuel.succ [] code s = .ok (s, []) := by
  rw [EvmYul.Yul.evalArgs.eq_def]

@[simp]
theorem evalArgs_cons
    (fuel : Nat) (arg : EvmYul.Yul.Ast.Expr) (args : List EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract) (s : EvmYul.Yul.State) :
    EvmYul.Yul.evalArgs fuel.succ (arg :: args) code s =
      EvmYul.Yul.evalTail fuel args code (EvmYul.Yul.eval fuel arg code s) := by
  rw [EvmYul.Yul.evalArgs.eq_def]

@[simp]
theorem primCall_add (fuel : Nat) (s : EvmYul.Yul.State) (a b : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.ADD : Operation .Yul) [a, b] =
      .ok (s, [a + b]) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp only [List.mem_cons, Bool.not_eq_true, reduceCtorEq, false_or, List.not_mem_nil,
    EvmYul.step.eq_def, and_false, if_false]
  rfl

@[simp]
theorem primCall_sub (fuel : Nat) (s : EvmYul.Yul.State) (a b : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.SUB : Operation .Yul) [a, b] =
      .ok (s, [a - b]) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp only [List.mem_cons, Bool.not_eq_true, reduceCtorEq, false_or, List.not_mem_nil,
    EvmYul.step.eq_def, and_false, if_false]
  rfl

@[simp]
theorem primCall_mul (fuel : Nat) (s : EvmYul.Yul.State) (a b : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.MUL : Operation .Yul) [a, b] =
      .ok (s, [a * b]) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp only [List.mem_cons, Bool.not_eq_true, reduceCtorEq, false_or, List.not_mem_nil,
    EvmYul.step.eq_def, and_false, if_false]
  rfl

@[simp]
theorem primCall_div (fuel : Nat) (s : EvmYul.Yul.State) (a b : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.DIV : Operation .Yul) [a, b] =
      .ok (s, [a / b]) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp only [List.mem_cons, Bool.not_eq_true, reduceCtorEq, false_or, List.not_mem_nil,
    EvmYul.step.eq_def, and_false, if_false]
  rfl

@[simp]
theorem primCall_mod (fuel : Nat) (s : EvmYul.Yul.State) (a b : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.MOD : Operation .Yul) [a, b] =
      .ok (s, [UInt256.mod a b]) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp only [List.mem_cons, Bool.not_eq_true, reduceCtorEq, false_or, List.not_mem_nil,
    EvmYul.step.eq_def, and_false, if_false]
  rfl

@[simp]
theorem primCall_sdiv (fuel : Nat) (s : EvmYul.Yul.State) (a b : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.SDIV : Operation .Yul) [a, b] =
      .ok (s, [UInt256.sdiv a b]) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp only [List.mem_cons, Bool.not_eq_true, reduceCtorEq, false_or, List.not_mem_nil,
    EvmYul.step.eq_def, and_false, if_false]
  rfl

@[simp]
theorem primCall_mulmod
    (fuel : Nat) (s : EvmYul.Yul.State) (a b n : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.MULMOD : Operation .Yul) [a, b, n] =
      .ok (s, [UInt256.mulMod a b n]) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp only [List.mem_cons, Bool.not_eq_true, reduceCtorEq, false_or, List.not_mem_nil,
    EvmYul.step.eq_def, and_false, if_false]
  rfl

@[simp]
theorem primCall_lt (fuel : Nat) (s : EvmYul.Yul.State) (a b : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.LT : Operation .Yul) [a, b] =
      .ok (s, [UInt256.lt a b]) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp only [List.mem_cons, Bool.not_eq_true, reduceCtorEq, false_or, List.not_mem_nil,
    EvmYul.step.eq_def, and_false, if_false]
  rfl

@[simp]
theorem primCall_gt (fuel : Nat) (s : EvmYul.Yul.State) (a b : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.GT : Operation .Yul) [a, b] =
      .ok (s, [UInt256.gt a b]) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp only [List.mem_cons, Bool.not_eq_true, reduceCtorEq, false_or, List.not_mem_nil,
    EvmYul.step.eq_def, and_false, if_false]
  rfl

@[simp]
theorem primCall_slt (fuel : Nat) (s : EvmYul.Yul.State) (a b : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.SLT : Operation .Yul) [a, b] =
      .ok (s, [UInt256.slt a b]) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp only [List.mem_cons, Bool.not_eq_true, reduceCtorEq, false_or, List.not_mem_nil,
    EvmYul.step.eq_def, and_false, if_false]
  rfl

@[simp]
theorem primCall_sgt (fuel : Nat) (s : EvmYul.Yul.State) (a b : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.SGT : Operation .Yul) [a, b] =
      .ok (s, [UInt256.sgt a b]) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp only [List.mem_cons, Bool.not_eq_true, reduceCtorEq, false_or, List.not_mem_nil,
    EvmYul.step.eq_def, and_false, if_false]
  rfl

@[simp]
theorem primCall_eq (fuel : Nat) (s : EvmYul.Yul.State) (a b : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.EQ : Operation .Yul) [a, b] =
      .ok (s, [UInt256.eq a b]) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp only [List.mem_cons, Bool.not_eq_true, reduceCtorEq, false_or, List.not_mem_nil,
    EvmYul.step.eq_def, and_false, if_false]
  rfl

@[simp]
theorem primCall_iszero (fuel : Nat) (s : EvmYul.Yul.State) (a : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.ISZERO : Operation .Yul) [a] =
      .ok (s, [UInt256.isZero a]) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp only [List.mem_cons, Bool.not_eq_true, reduceCtorEq, false_or, List.not_mem_nil,
    EvmYul.step.eq_def, and_false, if_false]
  rfl

@[simp]
theorem primCall_and (fuel : Nat) (s : EvmYul.Yul.State) (a b : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.AND : Operation .Yul) [a, b] =
      .ok (s, [UInt256.land a b]) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp only [List.mem_cons, Bool.not_eq_true, reduceCtorEq, false_or, List.not_mem_nil,
    EvmYul.step.eq_def, and_false, if_false]
  rfl

@[simp]
theorem primCall_or (fuel : Nat) (s : EvmYul.Yul.State) (a b : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.OR : Operation .Yul) [a, b] =
      .ok (s, [UInt256.lor a b]) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp only [List.mem_cons, Bool.not_eq_true, reduceCtorEq, false_or, List.not_mem_nil,
    EvmYul.step.eq_def, and_false, if_false]
  rfl

@[simp]
theorem primCall_xor (fuel : Nat) (s : EvmYul.Yul.State) (a b : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.XOR : Operation .Yul) [a, b] =
      .ok (s, [UInt256.xor a b]) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp only [List.mem_cons, Bool.not_eq_true, reduceCtorEq, false_or, List.not_mem_nil,
    EvmYul.step.eq_def, and_false, if_false]
  rfl

@[simp]
theorem primCall_not (fuel : Nat) (s : EvmYul.Yul.State) (a : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.NOT : Operation .Yul) [a] =
      .ok (s, [UInt256.lnot a]) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp only [List.mem_cons, Bool.not_eq_true, reduceCtorEq, false_or, List.not_mem_nil,
    EvmYul.step.eq_def, and_false, if_false]
  rfl

@[simp]
theorem primCall_byte (fuel : Nat) (s : EvmYul.Yul.State) (a b : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.BYTE : Operation .Yul) [a, b] =
      .ok (s, [UInt256.byteAt a b]) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp only [List.mem_cons, Bool.not_eq_true, reduceCtorEq, false_or, List.not_mem_nil,
    EvmYul.step.eq_def, and_false, if_false]
  rfl

@[simp]
theorem primCall_shl (fuel : Nat) (s : EvmYul.Yul.State) (a b : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.SHL : Operation .Yul) [a, b] =
      .ok (s, [UInt256.shiftLeft b a]) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp only [List.mem_cons, Bool.not_eq_true, reduceCtorEq, false_or, List.not_mem_nil,
    EvmYul.step.eq_def, and_false, if_false]
  rfl

@[simp]
theorem primCall_shr (fuel : Nat) (s : EvmYul.Yul.State) (a b : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.SHR : Operation .Yul) [a, b] =
      .ok (s, [UInt256.shiftRight b a]) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp only [List.mem_cons, Bool.not_eq_true, reduceCtorEq, false_or, List.not_mem_nil,
    EvmYul.step.eq_def, and_false, if_false]
  rfl

@[simp]
theorem primCall_sar (fuel : Nat) (s : EvmYul.Yul.State) (a b : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.SAR : Operation .Yul) [a, b] =
      .ok (s, [UInt256.sar a b]) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp only [List.mem_cons, Bool.not_eq_true, reduceCtorEq, false_or, List.not_mem_nil,
    EvmYul.step.eq_def, and_false, if_false]
  rfl

@[simp]
theorem primCall_clz (fuel : Nat) (s : EvmYul.Yul.State) (a : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.CLZ : Operation .Yul) [a] =
      .ok (s, [UInt256.clz a]) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp only [List.mem_cons, Bool.not_eq_true, reduceCtorEq, false_or, List.not_mem_nil,
    EvmYul.step.eq_def, and_false, if_false]
  rfl

@[simp]
theorem primCall_callvalue (fuel : Nat) (s : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.CALLVALUE : Operation .Yul) [] =
      .ok (s, [s.executionEnv.weiValue]) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp only [List.mem_cons, Bool.not_eq_true, reduceCtorEq, false_or, List.not_mem_nil,
    EvmYul.step.eq_def, and_false, if_false]
  rfl

@[simp]
theorem primCall_calldatasize (fuel : Nat) (s : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.CALLDATASIZE : Operation .Yul) [] =
      .ok (s, [EvmYul.UInt256.ofNat s.executionEnv.calldata.size]) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp only [List.mem_cons, Bool.not_eq_true, reduceCtorEq, false_or, List.not_mem_nil,
    EvmYul.step.eq_def, and_false, if_false]
  rfl

@[simp]
theorem primCall_calldataload
    (fuel : Nat) (s : EvmYul.Yul.State) (a : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.CALLDATALOAD : Operation .Yul) [a] =
      .ok (s, [EvmYul.State.calldataload s.toState a]) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp [EvmYul.step.eq_def, EvmYul.dispatchUnaryStateOp]
  unfold EvmYul.Yul.unaryStateOp
  cases s <;> rfl

@[simp]
theorem primCall_mstore
    (fuel : Nat) (s : EvmYul.Yul.State) (a b : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.MSTORE : Operation .Yul) [a, b] =
      .ok (s.setMachineState (s.toMachineState.mstore a b), []) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp [EvmYul.step.eq_def, EvmYul.dispatchBinaryMachineStateOp]
  unfold EvmYul.Yul.binaryMachineStateOp
  rfl

@[simp]
theorem primCall_mload (fuel : Nat) (s : EvmYul.Yul.State) (a : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.MLOAD : Operation .Yul) [a] =
      .ok (s.setMachineState (s.toMachineState.mload a).2, [(s.toMachineState.mload a).1]) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp [EvmYul.step.eq_def, EvmYul.Yul.State.toSharedState, EvmYul.Yul.State.toMachineState,
    EvmYul.Yul.State.setMachineState]
  cases s <;> rfl

@[simp]
theorem primCall_return
    (fuel : Nat) (s : EvmYul.Yul.State) (a b : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) s (Operation.RETURN : Operation .Yul) [a, b] =
      .error (EvmYul.Yul.Exception.YulHalt
        (s.setMachineState (s.toMachineState.evmReturn a b)) (EvmYul.UInt256.ofNat 1)) := by
  rw [EvmYul.Yul.primCall.eq_def]
  simp [EvmYul.step.eq_def, EvmYul.dispatchBinaryMachineStateOp]
  unfold EvmYul.Yul.binaryMachineStateOp
  rfl

@[simp]
theorem wordNat_word (x : Nat) : wordNat (word x) = u256 x := by
  unfold wordNat word EvmYul.UInt256.toNat EvmYul.UInt256.ofNat u256 WORD_MOD EvmYul.UInt256.size
  change
    (Fin.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639936
        x).val =
      x % 115792089237316195423570985008687907853269984665640564039457584007913129639936
  rw [Fin.val_ofNat]

@[simp]
theorem wordNat_ofNat (x : Nat) : wordNat (EvmYul.UInt256.ofNat x) = u256 x := by
  simpa [word] using wordNat_word x

@[simp]
theorem word_toNat (x : Nat) : (word x).toNat = u256 x :=
  wordNat_word x

theorem eq_of_wordNat_eq {a b : EvmYul.UInt256} (h : wordNat a = wordNat b) : a = b := by
  cases a with
  | mk av =>
  cases b with
  | mk bv =>
  simp [wordNat, EvmYul.UInt256.toNat] at h
  cases av
  cases bv
  simp at h
  subst h
  rfl

@[simp]
theorem u256_u256 (x : Nat) : u256 (u256 x) = u256 x := by
  unfold u256 WORD_MOD
  rw [Nat.mod_mod]

theorem u256_eq_self_of_lt {x : Nat} (h : x < WORD_MOD) : u256 x = x := by
  unfold u256
  exact Nat.mod_eq_of_lt h

@[simp] theorem u256_zero : u256 0 = 0 := by norm_num [u256, WORD_MOD]
@[simp] theorem u256_one : u256 1 = 1 := by norm_num [u256, WORD_MOD]
@[simp] theorem u256_two : u256 2 = 2 := by norm_num [u256, WORD_MOD]
@[simp] theorem u256_three : u256 3 = 3 := by norm_num [u256, WORD_MOD]
@[simp] theorem u256_four : u256 4 = 4 := by norm_num [u256, WORD_MOD]
@[simp] theorem u256_eight : u256 8 = 8 := by norm_num [u256, WORD_MOD]
@[simp] theorem u256_sixteen : u256 16 = 16 := by norm_num [u256, WORD_MOD]
@[simp] theorem u256_thirty_one : u256 31 = 31 := by norm_num [u256, WORD_MOD]
@[simp] theorem u256_thirty_two : u256 32 = 32 := by norm_num [u256, WORD_MOD]
@[simp] theorem u256_sixty_four : u256 64 = 64 := by norm_num [u256, WORD_MOD]
@[simp] theorem u256_one_twenty_eight : u256 128 = 128 := by norm_num [u256, WORD_MOD]
@[simp] theorem u256_one_sixty : u256 160 = 160 := by norm_num [u256, WORD_MOD]
@[simp] theorem u256_two_twenty_four : u256 224 = 224 := by norm_num [u256, WORD_MOD]
@[simp] theorem u256_two_fifty_five : u256 255 = 255 := by norm_num [u256, WORD_MOD]
@[simp] theorem u256_two_fifty_six : u256 256 = 256 := by norm_num [u256, WORD_MOD]

@[simp]
theorem byteArray_empty_append (b : ByteArray) : ByteArray.empty ++ b = b := by
  apply ByteArray.ext
  rw [← Array.toList_inj]
  simp [ByteArray.empty]

@[simp]
theorem encodeWord_data_toList (x : Nat) :
    (encodeWord x).data.toList =
      (List.range 32).map (fun i => byteAt (u256 x) (31 - i)) := by
  simp [encodeWord, ByteArray.push, ByteArray.empty, ByteArray.emptyWithCapacity,
    List.range, List.range.loop, List.range']
  rfl

private theorem div_pow_succ_256 (n i : Nat) :
    n / 256 ^ (i + 1) = (n / 256) / 256 ^ i := by
  rw [Nat.pow_succ]
  rw [Nat.div_div_eq_div_mul]
  ring_nf

private theorem mod_pow_succ_decomp_256 (n k : Nat) :
    n % 256 + 256 * ((n / 256) % 256 ^ k) = n % 256 ^ (k + 1) := by
  symm
  calc
    n % 256 ^ (k + 1)
        = (256 * (n / 256) + n % 256) % (256 * 256 ^ k) := by
          rw [show 256 ^ (k + 1) = 256 * 256 ^ k by
            rw [Nat.pow_succ]
            ring]
          exact congrArg (fun m => m % (256 * 256 ^ k)) (Nat.div_add_mod n 256).symm
    _ = (n % 256 + 256 * (n / 256)) % (256 * 256 ^ k) := by
          rw [Nat.add_comm]
    _ = (n % 256 + (256 * (n / 256)) % (256 * 256 ^ k)) %
          (256 * 256 ^ k) := by
          rw [Nat.add_mod]
          have hr : n % 256 % (256 * 256 ^ k) = n % 256 := by
            apply Nat.mod_eq_of_lt
            have h : n % 256 < 256 := Nat.mod_lt _ (by norm_num)
            have hpos : 0 < 256 ^ k := pow_pos (by norm_num : 0 < 256) k
            nlinarith
          rw [hr]
    _ = (n % 256 + 256 * ((n / 256) % 256 ^ k)) %
          (256 * 256 ^ k) := by
          rw [Nat.mul_mod_mul_left]
    _ = n % 256 + 256 * ((n / 256) % 256 ^ k) := by
          apply Nat.mod_eq_of_lt
          have h1 : n % 256 < 256 := Nat.mod_lt _ (by norm_num)
          have hpos : 0 < 256 ^ k := pow_pos (by norm_num : 0 < 256) k
          have h2 : (n / 256) % 256 ^ k < 256 ^ k := Nat.mod_lt _ hpos
          nlinarith

private theorem fromBytes_digits_256 (n k : Nat) :
    EvmYul.fromBytes'
        ((List.range k).map fun i => UInt8.ofNat ((n / 256 ^ i) % 256)) =
      n % 256 ^ k := by
  induction k generalizing n with
  | zero =>
      simp [EvmYul.fromBytes']
      omega
  | succ k ih =>
      rw [List.range_succ_eq_map]
      simp [EvmYul.fromBytes', UInt8.size]
      rw [show
          (List.map ((fun i => UInt8.ofNat (n / 256 ^ i % 256)) ∘ Nat.succ)
            (List.range k)) =
          (List.map (fun i => UInt8.ofNat ((n / 256) / 256 ^ i % 256))
            (List.range k)) by
        apply List.map_congr_left
        intro i _hi
        simp only [Function.comp_apply]
        rw [div_pow_succ_256]]
      rw [ih (n / 256)]
      exact mod_pow_succ_decomp_256 n k

@[simp]
theorem fromBytes_encodeWord (x : Nat) :
    EvmYul.fromBytes' ((encodeWord x).data.toList.reverse) = u256 x := by
  rw [encodeWord_data_toList]
  rw [show
      (List.map (fun i => byteAt (u256 x) (31 - i)) (List.range 32)).reverse =
        List.map (fun i => UInt8.ofNat ((u256 x / 256 ^ i) % 256)) (List.range 32) by
    simp [List.range, List.range.loop, List.range', byteAt]]
  rw [fromBytes_digits_256 (u256 x) 32]
  norm_num [u256, WORD_MOD]

@[simp]
theorem uInt256OfByteArray_encodeWord (x : Nat) :
    EvmYul.uInt256OfByteArray (encodeWord x) = word x := by
  apply eq_of_wordNat_eq
  unfold EvmYul.uInt256OfByteArray
  rw [wordNat_ofNat, fromBytes_encodeWord, wordNat_word]
  simp

theorem fromBytesBigEndian_snoc (xs : List UInt8) (b : UInt8) :
    EvmYul.fromBytesBigEndian (xs ++ [b]) =
      EvmYul.fromBytesBigEndian xs * 256 + b.toNat := by
  simp only [EvmYul.fromBytesBigEndian, Function.comp_apply]
  rw [List.reverse_append]
  simp [EvmYul.fromBytes']
  ring

theorem fromBytesBigEndian_append (xs ys : List UInt8) :
    EvmYul.fromBytesBigEndian (xs ++ ys) =
      EvmYul.fromBytesBigEndian xs * 256 ^ ys.length +
        EvmYul.fromBytesBigEndian ys := by
  induction ys using List.reverseRecOn with
  | nil =>
      simp [EvmYul.fromBytesBigEndian, EvmYul.fromBytes']
  | append_singleton ys b ih =>
      rw [← List.append_assoc, fromBytesBigEndian_snoc, ih, fromBytesBigEndian_snoc]
      simp [Nat.pow_succ]
      ring

theorem fromBytesBigEndian_lt_pow_length (xs : List UInt8) :
    EvmYul.fromBytesBigEndian xs < 256 ^ xs.length := by
  induction xs using List.reverseRecOn with
  | nil =>
      simp [EvmYul.fromBytesBigEndian, EvmYul.fromBytes']
  | append_singleton xs b ih =>
      rw [fromBytesBigEndian_snoc]
      simp [Nat.pow_succ]
      have hb : b.toNat < 256 := by
        simpa using UInt8.toNat_lt b
      have hpos : 0 < 256 ^ xs.length := pow_pos (by norm_num) xs.length
      nlinarith

theorem foldl_bytes_eq_fromBytesBigEndian (xs : List UInt8) :
    xs.foldl (fun acc b => acc * 256 + b.toNat) 0 =
      EvmYul.fromBytesBigEndian xs := by
  induction xs using List.reverseRecOn with
  | nil =>
      simp [EvmYul.fromBytesBigEndian, EvmYul.fromBytes']
  | append_singleton xs b ih =>
      rw [List.foldl_concat]
      rw [ih]
      simp only [EvmYul.fromBytesBigEndian, Function.comp_apply]
      rw [List.reverse_append]
      simp [EvmYul.fromBytes']
      ring

theorem range_map_getD_eq_self (xs : List UInt8) :
    (List.range xs.length).map (fun i => xs[i]?.getD 0) = xs := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map]
  by_cases hi : i < xs.length
  · have hrange : (List.range xs.length)[i]? = some i := List.getElem?_range hi
    rw [hrange]
    simp [List.getElem?_eq_getElem hi]
  · have hrangeNone : (List.range xs.length)[i]? = none := by
      apply List.getElem?_eq_none
      simpa using Nat.le_of_not_gt hi
    have hxsNone : xs[i]? = none := List.getElem?_eq_none (Nat.le_of_not_gt hi)
    rw [hrangeNone, hxsNone]
    simp

@[simp]
theorem decodeWord_toByteArray (v : EvmYul.UInt256) :
    FormalYul.decodeWord v.toByteArray = v.toNat := by
  unfold FormalYul.decodeWord
  simp [Id.run, EvmYul.UInt256.toByteArray_data_toList, List.range_eq_range']
  let xs :=
    List.replicate (32 - (EvmYul.toBytesBigEndian v.toNat).length) 0 ++
      EvmYul.toBytesBigEndian v.toNat
  have hlen : xs.length = 32 := by
    have h := EvmYul.toBytesBigEndian_UInt256_len_le v
    simp [xs, Nat.sub_add_cancel h]
  change List.foldl
    (fun b a => b * 256 + (xs[a]?.getD 0).toNat) 0 (List.range 32) = v.toNat
  rw [← (List.foldl_map (f := fun i => xs[i]?.getD 0)
    (g := fun acc b => acc * 256 + b.toNat) (l := List.range 32) (init := 0))]
  have hmap : (List.range 32).map (fun i => xs[i]?.getD 0) = xs := by
    rw [← hlen]
    exact range_map_getD_eq_self xs
  rw [hmap, foldl_bytes_eq_fromBytesBigEndian]
  simp [xs]

theorem readWithPadding_write_same_of_size
    (source dest : ByteArray) (destAddr : Nat) (hsize : source.size = 32) :
    (source.write 0 dest destAddr 32).readWithPadding destAddr 32 = source := by
  let pre := List.take destAddr
    (dest.data.toList ++ List.replicate (destAddr - dest.data.size) 0)
  let suffix := List.drop (destAddr + 32) dest.data.toList
  have hsrcLen : source.data.toList.length = 32 := by
    change source.data.size = 32 at hsize
    simpa [Array.length_toList] using hsize
  have hdataSize : source.data.size = 32 := by
    simpa [ByteArray.size] using hsize
  have hpreLen : pre.length = destAddr := by
    simp [pre, List.length_take]
    omega
  have hwrite :
      (source.write 0 dest destAddr 32).data.toList =
        pre ++ source.data.toList ++ suffix := by
    simp [ByteArray.write, pre, suffix, hsrcLen]
  have hwriteSizeSub :
      (source.write 0 dest destAddr 32).size - destAddr = 32 + suffix.length := by
    change (source.write 0 dest destAddr 32).data.size - destAddr = 32 + suffix.length
    rw [← Array.length_toList, hwrite]
    simp [hpreLen, hsrcLen]
  have hnotEnd : ¬ (source.write 0 dest destAddr 32).size ≤ destAddr := by
    omega
  have hmin :
      min 32 ((source.write 0 dest destAddr 32).size - destAddr) = 32 := by
    omega
  apply ByteArray.ext
  rw [← Array.toList_inj]
  simp [ByteArray.readWithPadding, ByteArray.readWithoutPadding, hwrite, hpreLen, hsrcLen,
    hnotEnd, hmin]
  change (ffi.ByteArray.zeroes (OfNat.ofNat 32 - OfNat.ofNat source.data.size)).data = #[]
  rw [hdataSize]
  have hz : (OfNat.ofNat 32 - OfNat.ofNat 32 : USize) = 0 := by
    apply USize.ext
    simp
  rw [hz]
  rfl

theorem evmReturn_mstore_word_H_return
    (mstate : EvmYul.MachineState) (pos value : EvmYul.UInt256) :
    ((mstate.mstore pos value).evmReturn pos (FormalYul.word 32)).H_return =
      value.toByteArray := by
  simp [EvmYul.MachineState.evmReturn, EvmYul.MachineState.mstore,
    EvmYul.MachineState.writeWord, EvmYul.writeBytes, FormalYul.word]
  exact readWithPadding_write_same_of_size value.toByteArray mstate.memory pos.toNat
    (by simp)

theorem resultWord_evmReturn_mstore_word
    (mstate : EvmYul.MachineState) (pos value : EvmYul.UInt256) :
    FormalYul.resultWord
      { returndata := ((mstate.mstore pos value).evmReturn pos (FormalYul.word 32)).H_return } =
      .ok value.toNat := by
  rw [evmReturn_mstore_word_H_return]
  simp [FormalYul.resultWord]

@[simp]
theorem readBytes_selector_single_arg (a b c d x : Nat) :
    ByteArray.readBytes (bytes [a, b, c, d] ++ encodeWord x) 4 32 =
      encodeWord x := by
  apply ByteArray.ext
  rw [← Array.toList_inj]
  simp [ByteArray.readBytes, bytes, ByteArray.push, ByteArray.empty,
    ByteArray.emptyWithCapacity, ByteArray.size, ffi.ByteArray.zeroes,
    List.range, List.range.loop, List.range']

@[simp]
theorem calldataload_single_arg
    (contract : YulContract) (a b c d x : Nat) :
    EvmYul.State.calldataload
      (sharedFor contract (bytes [a, b, c, d] ++ encodeWords [x])).toState
      (word 4) = word x := by
  simp [EvmYul.State.calldataload, sharedFor, envFor, encodeWords]

@[simp]
theorem calldataload_single_arg_state
    (contract : YulContract) (a b c d x : Nat) (store : EvmYul.Yul.VarStore) :
    EvmYul.State.calldataload
      (EvmYul.Yul.State.Ok
        (sharedFor contract (bytes [a, b, c, d] ++ encodeWords [x])) store).toState
      (word 4) = word x := by
  simpa [EvmYul.Yul.State.toState] using
    calldataload_single_arg contract a b c d x

@[simp]
theorem uint256_isZero_eq_self (v : EvmYul.UInt256) :
    EvmYul.UInt256.isZero (EvmYul.UInt256.eq v v) = EvmYul.UInt256.ofNat 0 := by
  unfold EvmYul.UInt256.isZero EvmYul.UInt256.eq EvmYul.UInt256.fromBool
  simp [EvmYul.UInt256.eq0]
  decide

@[simp]
theorem uint256_add_zero (v : EvmYul.UInt256) :
    v + EvmYul.UInt256.ofNat 0 = v := by
  change EvmYul.UInt256.add v (EvmYul.UInt256.ofNat 0) = v
  apply eq_of_wordNat_eq
  cases v with
  | mk val =>
      cases val with
      | mk val isLt =>
          simp [wordNat, EvmYul.UInt256.toNat, EvmYul.UInt256.add,
            EvmYul.UInt256.ofNat, EvmYul.UInt256.size, Fin.val_add]
          simpa [EvmYul.UInt256.size] using isLt

@[simp]
theorem u256_evmAdd (a b : Nat) : u256 (evmAdd a b) = evmAdd a b := by
  simp [evmAdd]

@[simp]
theorem u256_evmSub (a b : Nat) : u256 (evmSub a b) = evmSub a b := by
  simp [evmSub]

@[simp]
theorem u256_evmMul (a b : Nat) : u256 (evmMul a b) = evmMul a b := by
  simp [evmMul]

@[simp]
theorem u256_evmDiv (a b : Nat) : u256 (evmDiv a b) = evmDiv a b := by
  unfold evmDiv
  by_cases h : u256 b = 0
  · rw [if_pos h]
    simp [u256, WORD_MOD]
  · rw [if_neg h]
    apply u256_eq_self_of_lt
    apply lt_of_le_of_lt (Nat.div_le_self _ _)
    unfold u256 WORD_MOD
    exact Nat.mod_lt _ (by norm_num)

@[simp]
theorem u256_evmMod (a b : Nat) : u256 (evmMod a b) = evmMod a b := by
  unfold evmMod
  by_cases h : u256 b = 0
  · rw [if_pos h]
    simp [u256, WORD_MOD]
  · rw [if_neg h]
    apply u256_eq_self_of_lt
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.pos_of_ne_zero h))
      (Nat.le_of_lt (by
        unfold u256 WORD_MOD
        exact Nat.mod_lt _ (by norm_num)))

@[simp]
theorem u256_evmNot (a : Nat) : u256 (evmNot a) = evmNot a := by
  unfold evmNot
  apply u256_eq_self_of_lt
  unfold u256 WORD_MOD
  have h := Nat.mod_lt a (by norm_num :
    0 < 115792089237316195423570985008687907853269984665640564039457584007913129639936)
  omega

@[simp]
theorem u256_evmAnd (a b : Nat) : u256 (evmAnd a b) = evmAnd a b := by
  unfold evmAnd
  apply u256_eq_self_of_lt
  apply Nat.lt_of_le_of_lt Nat.and_le_left
  unfold u256 WORD_MOD
  exact Nat.mod_lt _ (by norm_num)

@[simp]
theorem u256_evmOr (a b : Nat) : u256 (evmOr a b) = evmOr a b := by
  unfold evmOr
  apply u256_eq_self_of_lt
  rw [show WORD_MOD = 2 ^ 256 by rfl]
  apply Nat.or_lt_two_pow
  · unfold u256 WORD_MOD
    exact Nat.mod_lt _ (by norm_num)
  · unfold u256 WORD_MOD
    exact Nat.mod_lt _ (by norm_num)

@[simp]
theorem u256_evmMulmod (a b n : Nat) : u256 (evmMulmod a b n) = evmMulmod a b n := by
  unfold evmMulmod
  by_cases h : u256 n = 0
  · rw [if_pos h]
    simp [u256, WORD_MOD]
  · rw [if_neg h]
    apply u256_eq_self_of_lt
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.pos_of_ne_zero h))
      (Nat.le_of_lt (by
        unfold u256 WORD_MOD
        exact Nat.mod_lt _ (by norm_num)))

@[simp]
theorem u256_evmShl (shift value : Nat) : u256 (evmShl shift value) = evmShl shift value := by
  unfold evmShl
  by_cases h : u256 shift < 256
  · rw [if_pos h]
    simp
  · rw [if_neg h]
    simp [u256, WORD_MOD]

@[simp]
theorem u256_evmShr (shift value : Nat) : u256 (evmShr shift value) = evmShr shift value := by
  unfold evmShr
  by_cases h : u256 shift < 256
  · rw [if_pos h]
    apply u256_eq_self_of_lt
    apply lt_of_le_of_lt (Nat.div_le_self _ _)
    unfold u256 WORD_MOD
    exact Nat.mod_lt _ (by norm_num)
  · rw [if_neg h]
    simp [u256, WORD_MOD]

@[simp]
theorem u256_evmClz (value : Nat) : u256 (evmClz value) = evmClz value := by
  unfold evmClz
  by_cases h : u256 value = 0
  · rw [if_pos h]
    apply u256_eq_self_of_lt
    norm_num [WORD_MOD]
  · rw [if_neg h]
    apply u256_eq_self_of_lt
    have hs : 255 - Nat.log2 (u256 value) ≤ 255 := Nat.sub_le _ _
    unfold WORD_MOD
    omega

@[simp]
theorem u256_evmLt (a b : Nat) : u256 (evmLt a b) = evmLt a b := by
  unfold evmLt
  by_cases h : u256 a < u256 b
  · rw [if_pos h]
    apply u256_eq_self_of_lt
    norm_num [WORD_MOD]
  · rw [if_neg h]
    simp [u256, WORD_MOD]

@[simp]
theorem u256_evmGt (a b : Nat) : u256 (evmGt a b) = evmGt a b := by
  unfold evmGt
  by_cases h : u256 a > u256 b
  · rw [if_pos h]
    apply u256_eq_self_of_lt
    norm_num [WORD_MOD]
  · rw [if_neg h]
    simp [u256, WORD_MOD]

@[simp]
theorem u256_evmEq (a b : Nat) : u256 (evmEq a b) = evmEq a b := by
  unfold evmEq
  by_cases h : u256 a = u256 b
  · rw [if_pos h]
    apply u256_eq_self_of_lt
    norm_num [WORD_MOD]
  · rw [if_neg h]
    simp [u256, WORD_MOD]

@[simp]
theorem u256_evmIszero (a : Nat) : u256 (evmIszero a) = evmIszero a := by
  unfold evmIszero
  by_cases h : u256 a = 0
  · rw [if_pos h]
    apply u256_eq_self_of_lt
    norm_num [WORD_MOD]
  · rw [if_neg h]
    simp [u256, WORD_MOD]

@[simp]
theorem evmAdd_u256_left (a b : Nat) : evmAdd (u256 a) b = evmAdd a b := by
  simp [evmAdd, u256]

@[simp]
theorem evmAdd_u256_right (a b : Nat) : evmAdd a (u256 b) = evmAdd a b := by
  simp [evmAdd, u256]

@[simp]
theorem evmSub_u256_left (a b : Nat) : evmSub (u256 a) b = evmSub a b := by
  simp [evmSub, u256]

@[simp]
theorem evmSub_u256_right (a b : Nat) : evmSub a (u256 b) = evmSub a b := by
  simp [evmSub, u256]

@[simp]
theorem evmMul_u256_left (a b : Nat) : evmMul (u256 a) b = evmMul a b := by
  simp [evmMul, u256]

@[simp]
theorem evmMul_u256_right (a b : Nat) : evmMul a (u256 b) = evmMul a b := by
  simp [evmMul, u256]

@[simp]
theorem evmDiv_u256_left (a b : Nat) : evmDiv (u256 a) b = evmDiv a b := by
  simp [evmDiv, u256]

@[simp]
theorem evmDiv_u256_right (a b : Nat) : evmDiv a (u256 b) = evmDiv a b := by
  simp [evmDiv, u256]

@[simp]
theorem evmMod_u256_left (a b : Nat) : evmMod (u256 a) b = evmMod a b := by
  simp [evmMod, u256]

@[simp]
theorem evmMod_u256_right (a b : Nat) : evmMod a (u256 b) = evmMod a b := by
  simp [evmMod, u256]

@[simp]
theorem evmShl_u256_left (a b : Nat) : evmShl (u256 a) b = evmShl a b := by
  simp [evmShl, u256]

@[simp]
theorem evmShl_u256_right (a b : Nat) : evmShl a (u256 b) = evmShl a b := by
  simp [evmShl, u256]

@[simp]
theorem evmShr_u256_left (a b : Nat) : evmShr (u256 a) b = evmShr a b := by
  simp [evmShr, u256]

@[simp]
theorem evmShr_u256_right (a b : Nat) : evmShr a (u256 b) = evmShr a b := by
  simp [evmShr, u256]

@[simp]
theorem evmClz_u256 (a : Nat) : evmClz (u256 a) = evmClz a := by
  simp [evmClz, u256]

@[simp]
theorem evmLt_u256_left (a b : Nat) : evmLt (u256 a) b = evmLt a b := by
  simp [evmLt, u256]

@[simp]
theorem evmLt_u256_right (a b : Nat) : evmLt a (u256 b) = evmLt a b := by
  simp [evmLt, u256]

@[simp]
theorem evmGt_u256_left (a b : Nat) : evmGt (u256 a) b = evmGt a b := by
  simp [evmGt, u256]

@[simp]
theorem evmGt_u256_right (a b : Nat) : evmGt a (u256 b) = evmGt a b := by
  simp [evmGt, u256]

@[simp]
theorem evmEq_u256_left (a b : Nat) : evmEq (u256 a) b = evmEq a b := by
  simp [evmEq, u256]

@[simp]
theorem evmEq_u256_right (a b : Nat) : evmEq a (u256 b) = evmEq a b := by
  simp [evmEq, u256]

@[simp]
theorem evmIszero_u256 (a : Nat) : evmIszero (u256 a) = evmIszero a := by
  simp [evmIszero, u256]

@[simp]
theorem evmAnd_u256_left (a b : Nat) : evmAnd (u256 a) b = evmAnd a b := by
  simp [evmAnd, u256]

@[simp]
theorem evmAnd_u256_right (a b : Nat) : evmAnd a (u256 b) = evmAnd a b := by
  simp [evmAnd, u256]

@[simp]
theorem evmOr_u256_left (a b : Nat) : evmOr (u256 a) b = evmOr a b := by
  simp [evmOr, u256]

@[simp]
theorem evmOr_u256_right (a b : Nat) : evmOr a (u256 b) = evmOr a b := by
  simp [evmOr, u256]

@[simp]
theorem evmNot_u256 (a : Nat) : evmNot (u256 a) = evmNot a := by
  simp [evmNot, u256]

@[simp]
theorem evmMulmod_u256_left (a b n : Nat) :
    evmMulmod (u256 a) b n = evmMulmod a b n := by
  simp [evmMulmod, u256]

@[simp]
theorem evmMulmod_u256_middle (a b n : Nat) :
    evmMulmod a (u256 b) n = evmMulmod a b n := by
  simp [evmMulmod, u256]

@[simp]
theorem evmMulmod_u256_right (a b n : Nat) :
    evmMulmod a b (u256 n) = evmMulmod a b n := by
  simp [evmMulmod, u256]

@[simp]
theorem wordNat_add (a b : EvmYul.UInt256) :
    wordNat (a + b) = evmAdd (wordNat a) (wordNat b) := by
  change wordNat (EvmYul.UInt256.add a b) = evmAdd (wordNat a) (wordNat b)
  unfold wordNat evmAdd u256 WORD_MOD EvmYul.UInt256.add EvmYul.UInt256.toNat
    EvmYul.UInt256.size
  simp [Fin.val_add]

@[simp]
theorem wordNat_mul (a b : EvmYul.UInt256) :
    wordNat (a * b) = evmMul (wordNat a) (wordNat b) := by
  change wordNat (EvmYul.UInt256.mul a b) = evmMul (wordNat a) (wordNat b)
  unfold wordNat evmMul u256 WORD_MOD EvmYul.UInt256.mul EvmYul.UInt256.toNat
    EvmYul.UInt256.size
  simp [Fin.val_mul]

@[simp]
theorem wordNat_sub (a b : EvmYul.UInt256) :
    wordNat (a - b) = evmSub (wordNat a) (wordNat b) := by
  change wordNat (EvmYul.UInt256.sub a b) = evmSub (wordNat a) (wordNat b)
  cases a with
  | mk av =>
  cases b with
  | mk bv =>
  cases av with
  | mk av hav =>
  cases bv with
  | mk bv hbv =>
  have hav' :
      av < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    simpa [EvmYul.UInt256.size] using hav
  have hbv' :
      bv < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    simpa [EvmYul.UInt256.size] using hbv
  change
    wordNat (EvmYul.UInt256.mk (Fin.sub (Fin.mk av hav) (Fin.mk bv hbv))) =
      evmSub (wordNat { val := ⟨av, hav⟩ }) (wordNat { val := ⟨bv, hbv⟩ })
  simp [wordNat, evmSub, u256, WORD_MOD, EvmYul.UInt256.toNat,
    EvmYul.UInt256.size, Fin.sub, Nat.mod_eq_of_lt hav', Nat.mod_eq_of_lt hbv']
  omega

@[simp]
theorem wordNat_div (a b : EvmYul.UInt256) :
    wordNat (a / b) = evmDiv (wordNat a) (wordNat b) := by
  change wordNat (EvmYul.UInt256.div a b) = evmDiv (wordNat a) (wordNat b)
  cases a with
  | mk av =>
  cases b with
  | mk bv =>
  cases av with
  | mk av hav =>
  cases bv with
  | mk bv hbv =>
  have hav' :
      av < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    simpa [EvmYul.UInt256.size] using hav
  have hbv' :
      bv < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    simpa [EvmYul.UInt256.size] using hbv
  by_cases hb : bv = 0
  · subst hb
    simp [wordNat, evmDiv, u256, WORD_MOD, EvmYul.UInt256.div,
      EvmYul.UInt256.toNat, EvmYul.UInt256.size]
  · simp [wordNat, evmDiv, u256, WORD_MOD, EvmYul.UInt256.div,
      EvmYul.UInt256.toNat, EvmYul.UInt256.size, Nat.mod_eq_of_lt hav',
      Nat.mod_eq_of_lt hbv', hb]

@[simp]
theorem wordNat_mod (a b : EvmYul.UInt256) :
    wordNat (a % b) = evmMod (wordNat a) (wordNat b) := by
  change wordNat (EvmYul.UInt256.mod a b) = evmMod (wordNat a) (wordNat b)
  cases a with
  | mk av =>
  cases b with
  | mk bv =>
  cases av with
  | mk av hav =>
  cases bv with
  | mk bv hbv =>
  have hav' :
      av < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    simpa [EvmYul.UInt256.size] using hav
  have hbv' :
      bv < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    simpa [EvmYul.UInt256.size] using hbv
  by_cases hb : bv = 0
  · subst hb
    simp [wordNat, evmMod, u256, WORD_MOD, EvmYul.UInt256.mod,
      EvmYul.UInt256.toNat, EvmYul.UInt256.size]
  · simp [wordNat, evmMod, u256, WORD_MOD, EvmYul.UInt256.mod,
      EvmYul.UInt256.toNat, EvmYul.UInt256.size, Nat.mod_eq_of_lt hav',
      Nat.mod_eq_of_lt hbv', hb]

@[simp]
theorem wordNat_uint256_mod (a b : EvmYul.UInt256) :
    wordNat (EvmYul.UInt256.mod a b) = evmMod (wordNat a) (wordNat b) := by
  change wordNat (a % b) = evmMod (wordNat a) (wordNat b)
  exact wordNat_mod a b

@[simp]
theorem wordNat_mulMod (a b n : EvmYul.UInt256) :
    wordNat (EvmYul.UInt256.mulMod a b n) =
      evmMulmod (wordNat a) (wordNat b) (wordNat n) := by
  cases a with
  | mk av =>
  cases b with
  | mk bv =>
  cases n with
  | mk nv =>
  cases av with
  | mk av hav =>
  cases bv with
  | mk bv hbv =>
  cases nv with
  | mk nv hnv =>
  have hav' : av < EvmYul.UInt256.size := by
    simpa [EvmYul.UInt256.size] using hav
  have hbv' : bv < EvmYul.UInt256.size := by
    simpa [EvmYul.UInt256.size] using hbv
  have hnv' : nv < EvmYul.UInt256.size := by
    simpa [EvmYul.UInt256.size] using hnv
  have havmod :
      av % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        av := by
    simpa [EvmYul.UInt256.size] using Nat.mod_eq_of_lt hav'
  have hbvmod :
      bv % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        bv := by
    simpa [EvmYul.UInt256.size] using Nat.mod_eq_of_lt hbv'
  have hnvmod :
      nv % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        nv := by
    simpa [EvmYul.UInt256.size] using Nat.mod_eq_of_lt hnv'
  by_cases hn : nv = 0
  · subst nv
    simp [wordNat, evmMulmod, u256, WORD_MOD, EvmYul.UInt256.mulMod,
      EvmYul.UInt256.eq0, EvmYul.UInt256.toNat, EvmYul.UInt256.ofNat,
      EvmYul.UInt256.size, havmod, hbvmod]
  · have hprodmod :
        (av * bv % nv) %
            115792089237316195423570985008687907853269984665640564039457584007913129639936 =
          av * bv % nv := by
      apply Nat.mod_eq_of_lt
      exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.pos_of_ne_zero hn)) (Nat.le_of_lt hnv')
    unfold EvmYul.UInt256.mulMod evmMulmod wordNat EvmYul.UInt256.toNat u256 WORD_MOD
      EvmYul.UInt256.eq0
    simp [EvmYul.UInt256.ofNat, EvmYul.UInt256.size, hn]
    rw [havmod, hbvmod, hnvmod]
    rw [if_neg hn]
    exact hprodmod

@[simp]
theorem wordNat_and (a b : EvmYul.UInt256) :
    wordNat (EvmYul.UInt256.land a b) = evmAnd (wordNat a) (wordNat b) := by
  cases a with
  | mk av =>
  cases b with
  | mk bv =>
  cases av with
  | mk av hav =>
  cases bv with
  | mk bv hbv =>
  have hav' : av < EvmYul.UInt256.size := by
    simpa [EvmYul.UInt256.size] using hav
  have hbv' : bv < EvmYul.UInt256.size := by
    simpa [EvmYul.UInt256.size] using hbv
  have handlt : Nat.land av bv < EvmYul.UInt256.size :=
    Nat.lt_of_le_of_lt Nat.and_le_left hav'
  have hlandmod :
      Nat.land av bv %
          115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        Nat.land av bv := by
    simpa [EvmYul.UInt256.size] using Nat.mod_eq_of_lt handlt
  have havmod :
      av % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        av := by
    simpa [EvmYul.UInt256.size] using Nat.mod_eq_of_lt hav'
  have hbvmod :
      bv % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        bv := by
    simpa [EvmYul.UInt256.size] using Nat.mod_eq_of_lt hbv'
  simp [wordNat, evmAnd, u256, WORD_MOD, EvmYul.UInt256.land, Fin.land,
    EvmYul.UInt256.toNat, EvmYul.UInt256.size, hlandmod, havmod, hbvmod]
  rfl

@[simp]
theorem wordNat_or (a b : EvmYul.UInt256) :
    wordNat (EvmYul.UInt256.lor a b) = evmOr (wordNat a) (wordNat b) := by
  cases a with
  | mk av =>
  cases b with
  | mk bv =>
  cases av with
  | mk av hav =>
  cases bv with
  | mk bv hbv =>
  have hav' : av < EvmYul.UInt256.size := by
    simpa [EvmYul.UInt256.size] using hav
  have hbv' : bv < EvmYul.UInt256.size := by
    simpa [EvmYul.UInt256.size] using hbv
  have horlt : Nat.lor av bv < EvmYul.UInt256.size := by
    rw [show EvmYul.UInt256.size = 2 ^ 256 by rfl]
    apply Nat.or_lt_two_pow
    · simpa [EvmYul.UInt256.size] using hav
    · simpa [EvmYul.UInt256.size] using hbv
  have hormod :
      Nat.lor av bv %
          115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        Nat.lor av bv := by
    simpa [EvmYul.UInt256.size] using Nat.mod_eq_of_lt horlt
  have havmod :
      av % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        av := by
    simpa [EvmYul.UInt256.size] using Nat.mod_eq_of_lt hav'
  have hbvmod :
      bv % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        bv := by
    simpa [EvmYul.UInt256.size] using Nat.mod_eq_of_lt hbv'
  simp [wordNat, evmOr, u256, WORD_MOD, EvmYul.UInt256.lor, Fin.lor,
    EvmYul.UInt256.toNat, EvmYul.UInt256.size, hormod, havmod, hbvmod]
  rfl

@[simp]
theorem wordNat_not (a : EvmYul.UInt256) :
    wordNat (EvmYul.UInt256.lnot a) = evmNot (wordNat a) := by
  rw [EvmYul.UInt256.lnot, wordNat_sub]
  cases a with
  | mk av =>
  cases av with
  | mk av hav =>
  have hav' :
      av < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    simpa [EvmYul.UInt256.size] using hav
  have havmod :
      av % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        av := by
    exact Nat.mod_eq_of_lt hav'
  simp [wordNat, evmSub, evmNot, u256, WORD_MOD, EvmYul.UInt256.ofNat,
    EvmYul.UInt256.toNat, EvmYul.UInt256.size, havmod, Nat.add_sub_cancel_left]
  rw [show
      231584178474632390847141970017375815706539969331281128078915168015826259279871 - av =
        115792089237316195423570985008687907853269984665640564039457584007913129639936 +
          (115792089237316195423570985008687907853269984665640564039457584007913129639935 - av) by
    omega]
  rw [Nat.add_mod, Nat.mod_self, zero_add]
  rw [show
      (115792089237316195423570985008687907853269984665640564039457584007913129639935 - av) %
          115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        115792089237316195423570985008687907853269984665640564039457584007913129639935 - av by
    apply Nat.mod_eq_of_lt
    omega]
  rw [show
      (115792089237316195423570985008687907853269984665640564039457584007913129639935 - av) %
          115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        115792089237316195423570985008687907853269984665640564039457584007913129639935 - av by
    apply Nat.mod_eq_of_lt
    omega]

@[simp]
theorem wordNat_lt (a b : EvmYul.UInt256) :
    wordNat (EvmYul.UInt256.lt a b) = evmLt (wordNat a) (wordNat b) := by
  cases a with
  | mk av =>
  cases b with
  | mk bv =>
  cases av with
  | mk av hav =>
  cases bv with
  | mk bv hbv =>
  have hav' :
      av < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    simpa [EvmYul.UInt256.size] using hav
  have hbv' :
      bv < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    simpa [EvmYul.UInt256.size] using hbv
  by_cases h : av < bv
  · have hfin : ({ val := ⟨av, hav⟩ } : EvmYul.UInt256) < { val := ⟨bv, hbv⟩ } := h
    rw [show EvmYul.UInt256.lt { val := ⟨av, hav⟩ } { val := ⟨bv, hbv⟩ } =
        EvmYul.UInt256.ofNat 1 by
      simp [EvmYul.UInt256.lt, EvmYul.UInt256.fromBool, hfin]]
    rw [wordNat_ofNat]
    simp [evmLt, u256, WORD_MOD, wordNat, EvmYul.UInt256.toNat,
      Nat.mod_eq_of_lt hav', Nat.mod_eq_of_lt hbv', h]
  · have hfin : ¬ (({ val := ⟨av, hav⟩ } : EvmYul.UInt256) < { val := ⟨bv, hbv⟩ }) := h
    rw [show EvmYul.UInt256.lt { val := ⟨av, hav⟩ } { val := ⟨bv, hbv⟩ } =
        EvmYul.UInt256.ofNat 0 by
      simp [EvmYul.UInt256.lt, EvmYul.UInt256.fromBool, hfin]]
    rw [wordNat_ofNat]
    simp [evmLt, u256, WORD_MOD, wordNat, EvmYul.UInt256.toNat,
      Nat.mod_eq_of_lt hav', Nat.mod_eq_of_lt hbv', h]

@[simp]
theorem wordNat_gt (a b : EvmYul.UInt256) :
    wordNat (EvmYul.UInt256.gt a b) = evmGt (wordNat a) (wordNat b) := by
  cases a with
  | mk av =>
  cases b with
  | mk bv =>
  cases av with
  | mk av hav =>
  cases bv with
  | mk bv hbv =>
  have hav' :
      av < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    simpa [EvmYul.UInt256.size] using hav
  have hbv' :
      bv < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    simpa [EvmYul.UInt256.size] using hbv
  by_cases h : bv < av
  · have hfin : ({ val := ⟨bv, hbv⟩ } : EvmYul.UInt256) < { val := ⟨av, hav⟩ } := h
    rw [show EvmYul.UInt256.gt { val := ⟨av, hav⟩ } { val := ⟨bv, hbv⟩ } =
        EvmYul.UInt256.ofNat 1 by
      simp [EvmYul.UInt256.gt, EvmYul.UInt256.fromBool, hfin]]
    rw [wordNat_ofNat]
    simp [evmGt, u256, WORD_MOD, wordNat, EvmYul.UInt256.toNat,
      Nat.mod_eq_of_lt hav', Nat.mod_eq_of_lt hbv', h]
  · have hfin : ¬ (({ val := ⟨bv, hbv⟩ } : EvmYul.UInt256) < { val := ⟨av, hav⟩ }) := h
    rw [show EvmYul.UInt256.gt { val := ⟨av, hav⟩ } { val := ⟨bv, hbv⟩ } =
        EvmYul.UInt256.ofNat 0 by
      simp [EvmYul.UInt256.gt, EvmYul.UInt256.fromBool, hfin]]
    rw [wordNat_ofNat]
    simp [evmGt, u256, WORD_MOD, wordNat, EvmYul.UInt256.toNat,
      Nat.mod_eq_of_lt hav', Nat.mod_eq_of_lt hbv', h]

@[simp]
theorem wordNat_eq (a b : EvmYul.UInt256) :
    wordNat (EvmYul.UInt256.eq a b) = evmEq (wordNat a) (wordNat b) := by
  cases a with
  | mk av =>
  cases b with
  | mk bv =>
  cases av with
  | mk av hav =>
  cases bv with
  | mk bv hbv =>
  have hav' :
      av < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    simpa [EvmYul.UInt256.size] using hav
  have hbv' :
      bv < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    simpa [EvmYul.UInt256.size] using hbv
  by_cases h : av = bv
  · subst av
    have hobj : ({ val := ⟨bv, hav⟩ } : EvmYul.UInt256) = { val := ⟨bv, hbv⟩ } := by
      rfl
    rw [show EvmYul.UInt256.eq { val := ⟨bv, hav⟩ } { val := ⟨bv, hbv⟩ } =
        EvmYul.UInt256.ofNat 1 by
      simp [EvmYul.UInt256.eq, EvmYul.UInt256.fromBool, hobj]]
    rw [wordNat_ofNat]
    simp [evmEq, u256, WORD_MOD, wordNat, EvmYul.UInt256.toNat,
      Nat.mod_eq_of_lt hbv']
  · have hobj : ¬ ({ val := ⟨av, hav⟩ } : EvmYul.UInt256) = { val := ⟨bv, hbv⟩ } := by
      intro heq
      apply h
      exact congrArg (fun u : EvmYul.UInt256 => u.toNat) heq
    rw [show EvmYul.UInt256.eq { val := ⟨av, hav⟩ } { val := ⟨bv, hbv⟩ } =
        EvmYul.UInt256.ofNat 0 by
      simp [EvmYul.UInt256.eq, EvmYul.UInt256.fromBool, hobj]]
    rw [wordNat_ofNat]
    simp [evmEq, u256, WORD_MOD, wordNat, EvmYul.UInt256.toNat,
      Nat.mod_eq_of_lt hav', Nat.mod_eq_of_lt hbv', h]

@[simp]
theorem wordNat_iszero (a : EvmYul.UInt256) :
    wordNat (EvmYul.UInt256.isZero a) = evmIszero (wordNat a) := by
  cases a with
  | mk av =>
  cases av with
  | mk av hav =>
  have hav' :
      av < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    simpa [EvmYul.UInt256.size] using hav
  by_cases h : av = 0
  · subst av
    have hzero : EvmYul.UInt256.eq0 ({ val := ⟨0, hav⟩ } : EvmYul.UInt256) = true := by
      simp [EvmYul.UInt256.eq0]
    rw [show EvmYul.UInt256.isZero { val := ⟨0, hav⟩ } = EvmYul.UInt256.ofNat 1 by
      unfold EvmYul.UInt256.isZero EvmYul.UInt256.fromBool
      rw [hzero]
      rfl]
    rw [wordNat_ofNat]
    simp [evmIszero, u256, WORD_MOD, wordNat, EvmYul.UInt256.toNat]
  · have hzero : EvmYul.UInt256.eq0 ({ val := ⟨av, hav⟩ } : EvmYul.UInt256) = false := by
      simp [EvmYul.UInt256.eq0, EvmYul.UInt256.toNat, h]
    rw [show EvmYul.UInt256.isZero { val := ⟨av, hav⟩ } = EvmYul.UInt256.ofNat 0 by
      unfold EvmYul.UInt256.isZero EvmYul.UInt256.fromBool
      rw [hzero]
      rfl]
    rw [wordNat_ofNat]
    simp [evmIszero, u256, WORD_MOD, wordNat, EvmYul.UInt256.toNat,
      Nat.mod_eq_of_lt hav', h]

@[simp]
theorem wordNat_shiftLeft (shift value : EvmYul.UInt256) :
    wordNat (EvmYul.UInt256.shiftLeft value shift) =
      evmShl (wordNat shift) (wordNat value) := by
  cases shift with
  | mk sh =>
  cases value with
  | mk v =>
  cases sh with
  | mk sh hsh =>
  cases v with
  | mk v hv =>
  have hsh' :
      sh < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    simpa [EvmYul.UInt256.size] using hsh
  have hv' :
      v < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    simpa [EvmYul.UInt256.size] using hv
  have h256mod : 256 % EvmYul.UInt256.size = 256 := by
    norm_num [EvmYul.UInt256.size]
  by_cases hlt : sh < 256
  · have hnle : ¬ 256 ≤ (⟨sh, hsh⟩ : Fin EvmYul.UInt256.size) := by
      simp [Fin.le_def, h256mod, hlt]
    simp [wordNat, evmShl, u256, WORD_MOD, EvmYul.UInt256.shiftLeft,
      EvmYul.UInt256.toNat, EvmYul.UInt256.size, Nat.mod_eq_of_lt hsh',
      Nat.mod_eq_of_lt hv', hlt, hnle, Nat.shiftLeft_eq]
  · have hge : 256 ≤ sh := Nat.le_of_not_gt hlt
    have hle : 256 ≤ (⟨sh, hsh⟩ : Fin EvmYul.UInt256.size) := by
      simp [Fin.le_def, h256mod, hge]
    simp [wordNat, evmShl, u256, WORD_MOD, EvmYul.UInt256.shiftLeft,
      EvmYul.UInt256.toNat, EvmYul.UInt256.size, Nat.mod_eq_of_lt hsh',
      Nat.mod_eq_of_lt hv', hge, hle]

@[simp]
theorem wordNat_shiftRight (shift value : EvmYul.UInt256) :
    wordNat (EvmYul.UInt256.shiftRight value shift) =
      evmShr (wordNat shift) (wordNat value) := by
  cases shift with
  | mk sh =>
  cases value with
  | mk v =>
  cases sh with
  | mk sh hsh =>
  cases v with
  | mk v hv =>
  have hsh' :
      sh < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    simpa [EvmYul.UInt256.size] using hsh
  have hv' :
      v < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    simpa [EvmYul.UInt256.size] using hv
  have h256mod : 256 % EvmYul.UInt256.size = 256 := by
    norm_num [EvmYul.UInt256.size]
  by_cases hlt : sh < 256
  · have hnle : ¬ 256 ≤ (⟨sh, hsh⟩ : Fin EvmYul.UInt256.size) := by
      simp [Fin.le_def, h256mod, hlt]
    simp [wordNat, evmShr, u256, WORD_MOD, EvmYul.UInt256.shiftRight,
      EvmYul.UInt256.toNat, EvmYul.UInt256.size, Nat.mod_eq_of_lt hsh',
      Nat.mod_eq_of_lt hv', hlt, hnle, Nat.shiftRight_eq_div_pow]
  · have hge : 256 ≤ sh := Nat.le_of_not_gt hlt
    have hle : 256 ≤ (⟨sh, hsh⟩ : Fin EvmYul.UInt256.size) := by
      simp [Fin.le_def, h256mod, hge]
    simp [wordNat, evmShr, u256, WORD_MOD, EvmYul.UInt256.shiftRight,
      EvmYul.UInt256.toNat, EvmYul.UInt256.size, Nat.mod_eq_of_lt hsh',
      Nat.mod_eq_of_lt hv', hge, hle]

@[simp]
theorem wordNat_clz (a : EvmYul.UInt256) :
    wordNat (EvmYul.UInt256.clz a) = evmClz (wordNat a) := by
  cases a with
  | mk av =>
  cases av with
  | mk av hav =>
  have hav' :
      av < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    simpa [EvmYul.UInt256.size] using hav
  by_cases hz : av = 0
  · subst av
    rw [show EvmYul.UInt256.clz { val := ⟨0, hav⟩ } = EvmYul.UInt256.ofNat 256 by
      simp [EvmYul.UInt256.clz, EvmYul.UInt256.toNat]]
    rw [wordNat_ofNat]
    simp [evmClz, u256, WORD_MOD, wordNat, EvmYul.UInt256.toNat]
  · have hsmall :
        255 - Nat.log2 av <
          115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
      have hs : 255 - Nat.log2 av ≤ 255 := Nat.sub_le _ _
      omega
    rw [show EvmYul.UInt256.clz { val := ⟨av, hav⟩ } =
        EvmYul.UInt256.ofNat (255 - Nat.log2 av) by
      simp [EvmYul.UInt256.clz, EvmYul.UInt256.toNat, hz]]
    rw [wordNat_ofNat]
    simp [evmClz, u256, WORD_MOD, wordNat, EvmYul.UInt256.toNat,
      Nat.mod_eq_of_lt hav', Nat.mod_eq_of_lt hsmall, hz]

@[simp]
theorem okWord_eq (x : Nat) : okWord x = .ok (u256 x) := rfl

@[simp]
theorem calldata_eq (selector : ByteArray) (args : List Nat) :
    calldata selector args = selector ++ encodeWords args := rfl

@[simp]
theorem callWord_eq_call_resultWord
    (contract : YulContract) (selector : ByteArray) (args : List Nat) (fuel : Nat) :
    callWord contract selector args fuel = (do
      let result ← call contract selector args fuel
      resultWord result) := rfl

@[simp]
theorem callPair_eq_call_resultWords
    (contract : YulContract) (selector : ByteArray) (args : List Nat) (fuel : Nat) :
    callPair contract selector args fuel = (do
      let words ← callWords contract selector args 2 fuel
      pairFromWords words) := rfl

@[simp]
theorem callTriple_eq_call_resultWords
    (contract : YulContract) (selector : ByteArray) (args : List Nat) (fuel : Nat) :
    callTriple contract selector args fuel = (do
      let words ← callWords contract selector args 3 fuel
      tripleFromWords words) := rfl

end Preservation

end FormalYul
