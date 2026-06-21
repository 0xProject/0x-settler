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
theorem toMachineState_ok
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.State.toMachineState (EvmYul.Yul.State.Ok shared store) =
      shared.toMachineState := rfl

@[simp]
theorem setMachineState_ok
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (mstate : EvmYul.MachineState) :
    EvmYul.Yul.State.setMachineState mstate (EvmYul.Yul.State.Ok shared store) =
      EvmYul.Yul.State.Ok { shared with toMachineState := mstate } store := rfl

@[simp]
theorem toMachineState_setMachineState_ok
    (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (mstate : EvmYul.MachineState) :
    EvmYul.Yul.State.toMachineState
      (EvmYul.Yul.State.setMachineState mstate (EvmYul.Yul.State.Ok shared store)) =
      mstate := rfl

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

def ExecReturn
    (fuel : Nat) (stmt : EvmYul.Yul.Ast.Stmt)
    (code : Option EvmYul.Yul.Ast.YulContract) (start : EvmYul.Yul.State)
    (result : CallResult) : Prop :=
  ∃ state value,
    EvmYul.Yul.exec fuel stmt code start =
      .error (EvmYul.Yul.Exception.YulHalt state value) ∧
    returnOf state = result

theorem execReturn_block_cons_of_head
    {fuel : Nat} {stmt : EvmYul.Yul.Ast.Stmt} {rest : List EvmYul.Yul.Ast.Stmt}
    {code : Option EvmYul.Yul.Ast.YulContract} {start : EvmYul.Yul.State}
    {result : CallResult}
    (hstmt : ExecReturn fuel stmt code start result) :
    ExecReturn (Nat.succ fuel) (EvmYul.Yul.Ast.Stmt.Block (stmt :: rest)) code
      start result := by
  rcases hstmt with ⟨state, value, hstmtExec, hret⟩
  refine ⟨state, value, ?_, hret⟩
  rw [EvmYul.Yul.exec.eq_def]
  simp only
  rw [hstmtExec]

theorem execReturn_block_cons_of_first_ok
    {fuel : Nat} {first : EvmYul.Yul.Ast.Stmt} {rest : List EvmYul.Yul.Ast.Stmt}
    {code : Option EvmYul.Yul.Ast.YulContract} {start mid : EvmYul.Yul.State}
    {result : CallResult}
    (hfirst : EvmYul.Yul.exec fuel first code start = .ok mid)
    (hrest : ExecReturn fuel (EvmYul.Yul.Ast.Stmt.Block rest) code mid result) :
    ExecReturn (Nat.succ fuel) (EvmYul.Yul.Ast.Stmt.Block (first :: rest)) code
      start result := by
  rcases hrest with ⟨state, value, hrestExec, hret⟩
  refine ⟨state, value, ?_, hret⟩
  rw [EvmYul.Yul.exec.eq_def]
  simp only
  rw [hfirst]
  exact hrestExec

theorem execReturn_block_cons_cons_of_first_ok_second
    {fuel : Nat} {first second : EvmYul.Yul.Ast.Stmt} {rest : List EvmYul.Yul.Ast.Stmt}
    {code : Option EvmYul.Yul.Ast.YulContract} {start mid : EvmYul.Yul.State}
    {result : CallResult}
    (hfirst : EvmYul.Yul.exec (Nat.succ fuel) first code start = .ok mid)
    (hsecond : ExecReturn fuel second code mid result) :
    ExecReturn (Nat.succ (Nat.succ fuel))
      (EvmYul.Yul.Ast.Stmt.Block (first :: second :: rest)) code start result := by
  rcases hsecond with ⟨state, value, hsecondExec, hret⟩
  refine ⟨state, value, ?_, hret⟩
  rw [EvmYul.Yul.exec.eq_def]
  simp only
  rw [hfirst]
  simp only
  rw [EvmYul.Yul.exec.eq_def]
  simp only
  rw [hsecondExec]

theorem execReturn_exprstmt_call_nil_of_call_halt
    {fuel : Nat} {fn : EvmYul.Yul.Ast.YulFunctionName}
    {code : Option EvmYul.Yul.Ast.YulContract} {start : EvmYul.Yul.State}
    {result : CallResult}
    (hcall :
      ∃ state value,
        EvmYul.Yul.call fuel [] (.some fn) code start =
          .error (EvmYul.Yul.Exception.YulHalt state value) ∧
        returnOf state = result) :
    ExecReturn (Nat.succ (Nat.succ fuel))
      (EvmYul.Yul.Ast.Stmt.ExprStmtCall
        (EvmYul.Yul.Ast.Expr.Call (.inr fn) [])) code start result := by
  rcases hcall with ⟨state, value, hcallExec, hret⟩
  refine ⟨state, value, ?_, hret⟩
  rw [EvmYul.Yul.exec.eq_def]
  simp only [EvmYul.Yul.execCall.eq_def, EvmYul.Yul.evalArgs.eq_def,
    List.reverse_nil, EvmYul.Yul.reverse']
  rw [hcallExec]
  rfl

theorem execReturn_block_single_call_nil_of_call_halt
    {fuel : Nat} {fn : EvmYul.Yul.Ast.YulFunctionName}
    {code : Option EvmYul.Yul.Ast.YulContract} {start : EvmYul.Yul.State}
    {result : CallResult}
    (hcall :
      ∃ state value,
        EvmYul.Yul.call fuel [] (.some fn) code start =
          .error (EvmYul.Yul.Exception.YulHalt state value) ∧
        returnOf state = result) :
    ExecReturn (Nat.succ (Nat.succ (Nat.succ fuel)))
      (EvmYul.Yul.Ast.Stmt.Block
        [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (.inr fn) [])]) code start result := by
  exact execReturn_block_cons_of_head
    (stmt := EvmYul.Yul.Ast.Stmt.ExprStmtCall
      (EvmYul.Yul.Ast.Expr.Call (.inr fn) []))
    (rest := []) (execReturn_exprstmt_call_nil_of_call_halt hcall)

theorem execReturn_if_true_of_eval
    {fuel : Nat} {cond : EvmYul.Yul.Ast.Expr} {body : List EvmYul.Yul.Ast.Stmt}
    {code : Option EvmYul.Yul.Ast.YulContract} {start mid : EvmYul.Yul.State}
    {condValue : EvmYul.UInt256} {result : CallResult}
    (heval : EvmYul.Yul.eval fuel cond code start = .ok (mid, condValue))
    (hcond : condValue ≠ (⟨0⟩ : EvmYul.UInt256))
    (hbody : ExecReturn fuel (EvmYul.Yul.Ast.Stmt.Block body) code mid result) :
    ExecReturn (Nat.succ fuel) (EvmYul.Yul.Ast.Stmt.If cond body) code start result := by
  rcases hbody with ⟨state, value, hbodyExec, hret⟩
  refine ⟨state, value, ?_, hret⟩
  rw [EvmYul.Yul.exec.eq_def]
  simp only
  rw [heval]
  simp only
  rw [if_pos hcond]
  exact hbodyExec

theorem execReturn_if_true_block_cons_cons_of_eval_first_ok_second
    {fuel : Nat} {cond : EvmYul.Yul.Ast.Expr}
    {first second : EvmYul.Yul.Ast.Stmt} {rest : List EvmYul.Yul.Ast.Stmt}
    {code : Option EvmYul.Yul.Ast.YulContract}
    {start branchStart afterFirst : EvmYul.Yul.State}
    {condValue : EvmYul.UInt256} {result : CallResult}
    (heval :
      EvmYul.Yul.eval (Nat.succ (Nat.succ fuel)) cond code start =
        .ok (branchStart, condValue))
    (hcond : condValue ≠ (⟨0⟩ : EvmYul.UInt256))
    (hfirst : EvmYul.Yul.exec (Nat.succ fuel) first code branchStart = .ok afterFirst)
    (hsecond : ExecReturn fuel second code afterFirst result) :
    ExecReturn (Nat.succ (Nat.succ (Nat.succ fuel)))
      (EvmYul.Yul.Ast.Stmt.If cond (first :: second :: rest)) code start result := by
  apply execReturn_if_true_of_eval
  · exact heval
  · exact hcond
  · exact execReturn_block_cons_cons_of_first_ok_second
      (first := first) (second := second) (rest := rest)
      (hfirst := hfirst) (hsecond := hsecond)

theorem execReturn_switch_of_eval_selected
    {fuel : Nat} {cond : EvmYul.Yul.Ast.Expr}
    {cases : List (EvmYul.Literal × List EvmYul.Yul.Ast.Stmt)}
    {defaultStmts selected : List EvmYul.Yul.Ast.Stmt}
    {code : Option EvmYul.Yul.Ast.YulContract} {start mid : EvmYul.Yul.State}
    {selector : EvmYul.Literal} {result : CallResult}
    (heval : EvmYul.Yul.eval fuel cond code start = .ok (mid, selector))
    (hselect : EvmYul.Yul.selectSwitchCase selector cases = .some selected)
    (hselected : ExecReturn fuel (EvmYul.Yul.Ast.Stmt.Block selected) code mid result) :
    ExecReturn (Nat.succ fuel)
      (EvmYul.Yul.Ast.Stmt.Switch cond cases defaultStmts) code start result := by
  rcases hselected with ⟨state, value, hselectedExec, hret⟩
  refine ⟨state, value, ?_, hret⟩
  rw [EvmYul.Yul.exec.eq_def]
  simp only
  rw [heval]
  simp only
  rw [hselect]
  exact hselectedExec

theorem execReturn_switch_selected_call_nil_of_eval
    {fuel : Nat} {fn : EvmYul.Yul.Ast.YulFunctionName}
    {cond : EvmYul.Yul.Ast.Expr}
    {cases : List (EvmYul.Literal × List EvmYul.Yul.Ast.Stmt)}
    {defaultStmts : List EvmYul.Yul.Ast.Stmt}
    {code : Option EvmYul.Yul.Ast.YulContract} {start mid : EvmYul.Yul.State}
    {selector : EvmYul.Literal} {result : CallResult}
    (heval :
      EvmYul.Yul.eval (Nat.succ (Nat.succ (Nat.succ fuel))) cond code start =
        .ok (mid, selector))
    (hselect :
      EvmYul.Yul.selectSwitchCase selector cases =
        .some [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (.inr fn) [])])
    (hcall :
      ∃ state value,
        EvmYul.Yul.call fuel [] (.some fn) code mid =
          .error (EvmYul.Yul.Exception.YulHalt state value) ∧
        returnOf state = result) :
    ExecReturn (Nat.succ (Nat.succ (Nat.succ (Nat.succ fuel))))
      (EvmYul.Yul.Ast.Stmt.Switch cond cases defaultStmts) code start result := by
  apply execReturn_switch_of_eval_selected
  · exact heval
  · exact hselect
  · exact execReturn_block_single_call_nil_of_call_halt hcall

theorem execReturn_block_if_switch_selected_call_nil
    {fuel : Nat}
    {first fallback letStmt : EvmYul.Yul.Ast.Stmt}
    {ifCond switchCond : EvmYul.Yul.Ast.Expr}
    {cases : List (EvmYul.Literal × List EvmYul.Yul.Ast.Stmt)}
    {defaultStmts : List EvmYul.Yul.Ast.Stmt}
    {fn : EvmYul.Yul.Ast.YulFunctionName}
    {code : Option EvmYul.Yul.Ast.YulContract}
    {start afterFirst branchStart afterLet switchStart : EvmYul.Yul.State}
    {condValue selector : EvmYul.Literal}
    {result : CallResult}
    (hfirst :
      EvmYul.Yul.exec
        (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ
          (Nat.succ fuel))))))))
        first code start = .ok afterFirst)
    (hcond :
      EvmYul.Yul.eval
        (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ fuel))))))
        ifCond code afterFirst = .ok (branchStart, condValue))
    (hcondNe : condValue ≠ (⟨0⟩ : EvmYul.UInt256))
    (hlet :
      EvmYul.Yul.exec
        (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ fuel)))))
        letStmt code branchStart = .ok afterLet)
    (hswitchEval :
      EvmYul.Yul.eval (Nat.succ (Nat.succ (Nat.succ fuel)))
        switchCond code afterLet = .ok (switchStart, selector))
    (hselect :
      EvmYul.Yul.selectSwitchCase selector cases =
        .some [EvmYul.Yul.Ast.Stmt.ExprStmtCall
          (EvmYul.Yul.Ast.Expr.Call (.inr fn) [])])
    (hcall :
      ∃ state value,
        EvmYul.Yul.call fuel [] (.some fn) code switchStart =
          .error (EvmYul.Yul.Exception.YulHalt state value) ∧
        returnOf state = result) :
    ExecReturn
      (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ
        (Nat.succ (Nat.succ fuel)))))))))
      (EvmYul.Yul.Ast.Stmt.Block
        [first,
          EvmYul.Yul.Ast.Stmt.If ifCond
            [letStmt,
              EvmYul.Yul.Ast.Stmt.Switch switchCond cases defaultStmts],
          fallback])
      code start result := by
  apply execReturn_block_cons_of_first_ok
  · exact hfirst
  · apply execReturn_block_cons_of_head
    apply execReturn_if_true_block_cons_cons_of_eval_first_ok_second
    · exact hcond
    · exact hcondNe
    · exact hlet
    · apply execReturn_switch_selected_call_nil_of_eval
      · exact hswitchEval
      · exact hselect
      · exact hcall

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
theorem exec_let_none
    (fuel : Nat) (vars : List EvmYul.Identifier)
    (code : Option EvmYul.Yul.Ast.YulContract) (s : EvmYul.Yul.State) :
    EvmYul.Yul.exec fuel.succ (EvmYul.Yul.Ast.Stmt.Let vars none) code s =
      .ok (List.foldr (fun var s => s.insert var (⟨0⟩ : EvmYul.UInt256)) s vars) := by
  rw [EvmYul.Yul.exec.eq_def]

@[simp]
theorem exec_let_none_add
    (fuel extra : Nat) (vars : List EvmYul.Identifier)
    (code : Option EvmYul.Yul.Ast.YulContract) (s : EvmYul.Yul.State) :
    EvmYul.Yul.exec (fuel + (extra + 1)) (EvmYul.Yul.Ast.Stmt.Let vars none) code s =
      .ok (List.foldr (fun var s => s.insert var (⟨0⟩ : EvmYul.UInt256)) s vars) := by
  rw [show fuel + (extra + 1) = (fuel + extra).succ by omega]
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
theorem primCall_add_add
    (fuel extra : Nat) (s : EvmYul.Yul.State) (a b : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + (extra + 1)) s (Operation.ADD : Operation .Yul) [a, b] =
      .ok (s, [a + b]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    primCall_add (fuel := fuel + extra) (s := s) (a := a) (b := b)

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
theorem primCall_mload_add
    (fuel extra : Nat) (s : EvmYul.Yul.State) (a : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + (extra + 1)) s (Operation.MLOAD : Operation .Yul) [a] =
      .ok (s.setMachineState (s.toMachineState.mload a).2, [(s.toMachineState.mload a).1]) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    primCall_mload (fuel := fuel + extra) (s := s) (a := a)

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

theorem decodeWord_zero_eq_fromBytesBigEndian_of_size (data : ByteArray)
    (hsize : data.size = 32) :
    FormalYul.decodeWord data 0 = EvmYul.fromBytesBigEndian data.data.toList := by
  unfold FormalYul.decodeWord
  simp [Id.run]
  rw [← List.range_eq_range']
  simp only [← Array.getElem?_toList]
  rw [← (List.foldl_map (f := fun i => data.data.toList[i]?.getD 0)
    (g := fun acc b => acc * 256 + b.toNat) (l := List.range 32) (init := 0))]
  have hmap : (List.range 32).map (fun i => data.data.toList[i]?.getD 0) =
      data.data.toList := by
    have hlen : data.data.toList.length = 32 := by
      simpa [ByteArray.size, Array.length_toList] using hsize
    rw [← hlen]
    exact range_map_getD_eq_self data.data.toList
  rw [hmap, foldl_bytes_eq_fromBytesBigEndian]

theorem decodeWord_append_left_of_size (a b : ByteArray) (ha : a.size = 32) :
    FormalYul.decodeWord (a ++ b) 0 = FormalYul.decodeWord a 0 := by
  unfold FormalYul.decodeWord
  simp [Id.run]
  rw [← List.range_eq_range']
  simp only [← Array.getElem?_toList]
  rw [← (List.foldl_map (f := fun i => (a.data.toList ++ b.data.toList)[i]?.getD 0)
    (g := fun acc b => acc * 256 + b.toNat) (l := List.range 32) (init := 0))]
  rw [← (List.foldl_map (f := fun i => a.data.toList[i]?.getD 0)
    (g := fun acc b => acc * 256 + b.toNat) (l := List.range 32) (init := 0))]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hlen : a.data.toList.length = 32 := by
    simpa [ByteArray.size, Array.length_toList] using ha
  have hi' : i < a.data.toList.length := by
    have hi32 := List.mem_range.mp hi
    omega
  rw [List.getElem?_append_left hi']

theorem decodeWord_append_right_of_size (a b : ByteArray) (ha : a.size = 32) :
    FormalYul.decodeWord (a ++ b) 32 = FormalYul.decodeWord b 0 := by
  unfold FormalYul.decodeWord
  simp [Id.run]
  rw [← List.range_eq_range']
  simp only [← Array.getElem?_toList]
  congr 1
  funext acc i
  have hlen : a.data.toList.length = 32 := by
    simpa [ByteArray.size, Array.length_toList] using ha
  have hge : a.data.toList.length ≤ 32 + i := by omega
  rw [List.getElem?_append_right hge]
  have hidx : 32 + i - a.data.toList.length = i := by omega
  rw [hidx]

theorem decodeWord_append_right_at_size (a b : ByteArray) (offset : Nat)
    (ha : a.size = offset) :
    FormalYul.decodeWord (a ++ b) offset = FormalYul.decodeWord b 0 := by
  unfold FormalYul.decodeWord
  simp [Id.run]
  rw [← List.range_eq_range']
  simp only [← Array.getElem?_toList]
  congr 1
  funext acc i
  have hlen : a.data.toList.length = offset := by
    simpa [ByteArray.size, Array.length_toList] using ha
  have hge : a.data.toList.length ≤ offset + i := by omega
  rw [List.getElem?_append_right hge]
  have hidx : offset + i - a.data.toList.length = i := by omega
  rw [hidx]

theorem byteArray_append_assoc (a b c : ByteArray) :
    (a ++ b) ++ c = a ++ (b ++ c) := by
  apply ByteArray.ext
  rw [← Array.toList_inj]
  simp [ByteArray.data_append]

theorem encodeWord_size (x : Nat) : (FormalYul.encodeWord x).size = 32 := by
  change (FormalYul.encodeWord x).data.size = 32
  rw [← Array.length_toList]
  simp [FormalYul.Preservation.encodeWord_data_toList]

@[simp]
theorem decodeWord_encodeWord (x : Nat) :
    FormalYul.decodeWord (FormalYul.encodeWord x) 0 = FormalYul.u256 x := by
  rw [decodeWord_zero_eq_fromBytesBigEndian_of_size]
  · change EvmYul.fromBytes' (encodeWord x).data.toList.reverse = u256 x
    rw [fromBytes_encodeWord]
  · exact encodeWord_size x

theorem resultWords_two_encodeWords (a b : Nat) :
    FormalYul.resultWords { returndata := FormalYul.encodeWords [a, b] } 2 =
      .ok [FormalYul.u256 a, FormalYul.u256 b] := by
  simp [FormalYul.resultWords, FormalYul.decodeWords, FormalYul.encodeWords,
    byteArray_empty_append, ByteArray.size_append, encodeWord_size,
    List.range, List.range.loop]
  rw [decodeWord_append_left_of_size (FormalYul.encodeWord a) (FormalYul.encodeWord b)
      (encodeWord_size a)]
  rw [decodeWord_append_right_of_size (FormalYul.encodeWord a) (FormalYul.encodeWord b)
      (encodeWord_size a)]
  simp

def abiWordResult (a : Nat) : FormalYul.CallResult :=
  { returndata := (FormalYul.word a).toByteArray }

def abiPairResult (a b : Nat) : FormalYul.CallResult :=
  { returndata := (FormalYul.word a).toByteArray ++ (FormalYul.word b).toByteArray }

def abiTripleResult (a b c : Nat) : FormalYul.CallResult :=
  { returndata :=
      (FormalYul.word a).toByteArray ++ (FormalYul.word b).toByteArray ++
        (FormalYul.word c).toByteArray }

theorem resultWords_two_word_toByteArray (a b : Nat) :
    FormalYul.resultWords (abiPairResult a b) 2 =
      .ok [FormalYul.u256 a, FormalYul.u256 b] := by
  unfold abiPairResult
  simp [FormalYul.resultWords, FormalYul.decodeWords,
    ByteArray.size_append, EvmYul.UInt256.toByteArray_size,
    List.range, List.range.loop]
  rw [decodeWord_append_left_of_size (FormalYul.word a).toByteArray (FormalYul.word b).toByteArray
      (EvmYul.UInt256.toByteArray_size (FormalYul.word a))]
  rw [decodeWord_append_right_of_size (FormalYul.word a).toByteArray (FormalYul.word b).toByteArray
      (EvmYul.UInt256.toByteArray_size (FormalYul.word a))]
  simp [FormalYul.word, decodeWord_toByteArray]
  constructor
  · exact wordNat_ofNat a
  · exact wordNat_ofNat b

theorem resultWords_three_word_toByteArray (a b c : Nat) :
    FormalYul.resultWords (abiTripleResult a b c) 3 =
      .ok [FormalYul.u256 a, FormalYul.u256 b, FormalYul.u256 c] := by
  unfold abiTripleResult
  simp [FormalYul.resultWords, FormalYul.decodeWords,
    ByteArray.size_append, EvmYul.UInt256.toByteArray_size,
    List.range, List.range.loop]
  constructor
  · rw [byteArray_append_assoc]
    rw [decodeWord_append_left_of_size (FormalYul.word a).toByteArray
        ((FormalYul.word b).toByteArray ++ (FormalYul.word c).toByteArray)
        (EvmYul.UInt256.toByteArray_size (FormalYul.word a))]
    simp [FormalYul.word, decodeWord_toByteArray]
    exact wordNat_ofNat a
  · constructor
    · rw [byteArray_append_assoc]
      rw [decodeWord_append_right_of_size (FormalYul.word a).toByteArray
          ((FormalYul.word b).toByteArray ++ (FormalYul.word c).toByteArray)
          (EvmYul.UInt256.toByteArray_size (FormalYul.word a))]
      rw [decodeWord_append_left_of_size (FormalYul.word b).toByteArray
          (FormalYul.word c).toByteArray
          (EvmYul.UInt256.toByteArray_size (FormalYul.word b))]
      simp [FormalYul.word, decodeWord_toByteArray]
      exact wordNat_ofNat b
    · rw [decodeWord_append_right_at_size
        ((FormalYul.word a).toByteArray ++ (FormalYul.word b).toByteArray)
        (FormalYul.word c).toByteArray 64 (by
          simp [ByteArray.size_append, EvmYul.UInt256.toByteArray_size])]
      simp [FormalYul.word, decodeWord_toByteArray]
      exact wordNat_ofNat c

theorem resultWord_word_toByteArray (a : Nat) :
    FormalYul.resultWord (abiWordResult a) = .ok (FormalYul.u256 a) := by
  unfold abiWordResult
  simp [FormalYul.resultWord, FormalYul.word, decodeWord_toByteArray,
    EvmYul.UInt256.toByteArray_size]
  exact wordNat_ofNat a

theorem bind_ok_resultWords (result : FormalYul.CallResult) (count : Nat) :
    (do
      let result' ← (Except.ok result : Except String FormalYul.CallResult)
      FormalYul.resultWords result' count) =
      FormalYul.resultWords result count := rfl

theorem bind_ok_pairFromWords (words : List Nat) :
    (do
      let words' ← (Except.ok words : Except String (List Nat))
      FormalYul.pairFromWords words') =
      FormalYul.pairFromWords words := rfl

theorem bind_ok_tripleFromWords (words : List Nat) :
    (do
      let words' ← (Except.ok words : Except String (List Nat))
      FormalYul.tripleFromWords words') =
      FormalYul.tripleFromWords words := rfl

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

theorem readWithPadding_two_word_writes_data_of_size
    (a b dest : ByteArray) (destAddr : Nat)
    (ha : a.size = 32) (hb : b.size = 32) (hdest : dest.size = destAddr) :
    ((b.write 0 (a.write 0 dest destAddr 32) (destAddr + 32) 32).readWithPadding
        destAddr 64).data.toList =
      a.data.toList ++ b.data.toList := by
  simp [ByteArray.size] at ha hb hdest
  have ha_take : List.take 32 a.data.toList = a.data.toList := by
    exact List.take_of_length_le (by simp [Array.length_toList, ha])
  have hb_take : List.take 32 b.data.toList = b.data.toList := by
    exact List.take_of_length_le (by simp [Array.length_toList, hb])
  have hsub0 : destAddr - (destAddr + 32 + 32) = 0 := by omega
  have hsub64 : destAddr + 32 + 32 - destAddr = 64 := by omega
  simp [ByteArray.write, ByteArray.readWithPadding, ByteArray.readWithoutPadding,
    ByteArray.size, ha, hb, hdest, ha_take, hb_take, hsub0, hsub64,
    List.take_append, List.drop_append, ffi.ByteArray.zeroes]

theorem readWithPadding_two_word_writes_of_size
    (a b dest : ByteArray) (destAddr : Nat)
    (ha : a.size = 32) (hb : b.size = 32) (hdest : dest.size = destAddr) :
    (b.write 0 (a.write 0 dest destAddr 32) (destAddr + 32) 32).readWithPadding
        destAddr 64 =
      a ++ b := by
  apply ByteArray.ext
  rw [← Array.toList_inj]
  simp [ByteArray.data_append]
  exact readWithPadding_two_word_writes_data_of_size a b dest destAddr ha hb hdest

theorem write32_size_of_size_le_addr
    (source dest : ByteArray) (destAddr : Nat)
    (hsource : source.size = 32) (hdest : dest.size ≤ destAddr) :
    (source.write 0 dest destAddr 32).size = destAddr + 32 := by
  simp [ByteArray.write, ByteArray.size] at hsource hdest ⊢
  omega

theorem write32_size_of_addr_add_le_size
    (source dest : ByteArray) (destAddr : Nat)
    (hsource : source.size = 32) (hdest : destAddr + 32 ≤ dest.size) :
    (source.write 0 dest destAddr 32).size = dest.size := by
  simp [ByteArray.write, ByteArray.size] at hsource hdest ⊢
  omega

theorem readWithPadding_64_32_write0_preserve_of_size_192
    (source dest : ByteArray) (hsource : source.size = 32) (hdest : dest.size = 192) :
    (source.write 0 dest 0 32).readWithPadding 64 32 =
      dest.readWithPadding 64 32 := by
  apply ByteArray.ext
  rw [← Array.toList_inj]
  simp [ByteArray.write, ByteArray.readWithPadding, ByteArray.readWithoutPadding,
    ByteArray.size] at hsource hdest ⊢
  have hif1 :
      ¬ (min 32 source.data.size +
            (32 - min 32 source.data.size + (dest.data.size - 32)) ≤ 64) := by
    omega
  have hif2 : ¬ dest.data.size ≤ 64 := by
    omega
  rw [if_neg hif1, if_neg hif2]
  have hmin1 :
      min 32
          (min 32 source.data.size +
              (32 - min 32 source.data.size + (dest.data.size - 32)) - 64) =
        32 := by
    omega
  have hmin2 : min 32 (dest.data.size - 64) = 32 := by
    omega
  rw [hmin1, hmin2]
  have hread :
      List.take 32
          (List.drop 64
            (List.take 32 source.data.toList ++
              (List.replicate (32 - min 32 source.data.size) 0 ++
                List.drop 32 dest.data.toList))) =
        List.take 32 (List.drop 64 dest.data.toList) := by
    simp [hsource, List.drop_append, List.take_append]
  rw [hread]

theorem readWithPadding_64_32_write32_preserve_of_size_192
    (source dest : ByteArray) (hsource : source.size = 32) (hdest : dest.size = 192) :
    (source.write 0 dest 32 32).readWithPadding 64 32 =
      dest.readWithPadding 64 32 := by
  apply ByteArray.ext
  rw [← Array.toList_inj]
  simp [ByteArray.write, ByteArray.readWithPadding, ByteArray.readWithoutPadding,
    ByteArray.size] at hsource hdest ⊢
  have hif1 :
      ¬ (min 32 (dest.data.size + (32 - dest.data.size)) +
            (min 32 source.data.size +
              (32 - min 32 source.data.size + (dest.data.size - 64))) ≤ 64) := by
    omega
  have hif2 : ¬ dest.data.size ≤ 64 := by
    omega
  rw [if_neg hif1, if_neg hif2]
  have hmin1 :
      min 32
          (min 32 (dest.data.size + (32 - dest.data.size)) +
              (min 32 source.data.size +
                (32 - min 32 source.data.size + (dest.data.size - 64))) - 64) =
        32 := by
    omega
  have hmin2 : min 32 (dest.data.size - 64) = 32 := by
    omega
  rw [hmin1, hmin2]
  have hread :
      List.take 32
          (List.drop 64
            (List.take 32 (dest.data.toList ++ List.replicate (32 - dest.data.size) 0) ++
              (List.take 32 source.data.toList ++
                (List.replicate (32 - min 32 source.data.size) 0 ++
                  List.drop 64 dest.data.toList)))) =
        List.take 32 (List.drop 64 dest.data.toList) := by
    simp [hsource, hdest, List.drop_append, List.take_append]
  rw [hread]

theorem readWithPadding_64_32_write128_preserve_of_size_96
    (source dest : ByteArray) (hsource : source.size = 32) (hdest : dest.size = 96) :
    (source.write 0 dest 128 32).readWithPadding 64 32 =
      dest.readWithPadding 64 32 := by
  apply ByteArray.ext
  rw [← Array.toList_inj]
  simp [ByteArray.write, ByteArray.readWithPadding, ByteArray.readWithoutPadding,
    ByteArray.size] at hsource hdest ⊢
  have hif1 :
      ¬ (min 128 (dest.data.size + (128 - dest.data.size)) +
            (min 32 source.data.size +
              (32 - min 32 source.data.size + (dest.data.size - 160))) ≤ 64) := by
    omega
  have hif2 : ¬ dest.data.size ≤ 64 := by
    omega
  rw [if_neg hif1, if_neg hif2]
  have hmin1 :
      min 32
          (min 128 (dest.data.size + (128 - dest.data.size)) +
              (min 32 source.data.size +
                (32 - min 32 source.data.size + (dest.data.size - 160))) - 64) =
        32 := by
    omega
  have hmin2 : min 32 (dest.data.size - 64) = 32 := by
    omega
  rw [hmin1, hmin2]
  have hread :
      List.take 32
          (List.drop 64
            (List.take 128 (dest.data.toList ++ List.replicate (128 - dest.data.size) 0) ++
              (List.take 32 source.data.toList ++
                (List.replicate (32 - min 32 source.data.size) 0 ++
                  List.drop 160 dest.data.toList)))) =
        List.take 32 (List.drop 64 dest.data.toList) := by
    simp [hsource, hdest, List.drop_append, List.take_append]
    rw [List.drop_take]
    have hlen : (List.drop 64 dest.data.toList).length = 32 := by
      simp [Array.length_toList, hdest]
    rw [List.take_of_length_le
      (show (List.drop 64 dest.data.toList).length ≤ 128 - 64 by omega)]
    rw [List.take_of_length_le
      (show (List.drop 64 dest.data.toList).length ≤ 32 by omega)]
  rw [hread]

theorem readWithPadding_64_32_write160_preserve_of_size_160
    (source dest : ByteArray) (hsource : source.size = 32) (hdest : dest.size = 160) :
    (source.write 0 dest 160 32).readWithPadding 64 32 =
      dest.readWithPadding 64 32 := by
  apply ByteArray.ext
  rw [← Array.toList_inj]
  simp [ByteArray.write, ByteArray.readWithPadding, ByteArray.readWithoutPadding,
    ByteArray.size] at hsource hdest ⊢
  have hif1 :
      ¬ (min 160 (dest.data.size + (160 - dest.data.size)) +
            (min 32 source.data.size +
              (32 - min 32 source.data.size + (dest.data.size - 192))) ≤ 64) := by
    omega
  have hif2 : ¬ dest.data.size ≤ 64 := by
    omega
  rw [if_neg hif1, if_neg hif2]
  have hmin1 :
      min 32
          (min 160 (dest.data.size + (160 - dest.data.size)) +
              (min 32 source.data.size +
                (32 - min 32 source.data.size + (dest.data.size - 192))) - 64) =
        32 := by
    omega
  have hmin2 : min 32 (dest.data.size - 64) = 32 := by
    omega
  rw [hmin1, hmin2]
  have hread :
      List.take 32
          (List.drop 64
            (List.take 160 (dest.data.toList ++ List.replicate (160 - dest.data.size) 0) ++
              (List.take 32 source.data.toList ++
                (List.replicate (32 - min 32 source.data.size) 0 ++
                  List.drop 192 dest.data.toList)))) =
        List.take 32 (List.drop 64 dest.data.toList) := by
    simp [hsource, hdest, List.drop_append, List.take_append]
    rw [List.drop_take, List.take_take]
    rfl
  rw [hread]

theorem evmReturn_mstore_word_H_return
    (mstate : EvmYul.MachineState) (pos value : EvmYul.UInt256) :
    ((mstate.mstore pos value).evmReturn pos (FormalYul.word 32)).H_return =
      value.toByteArray := by
  simp [EvmYul.MachineState.evmReturn, EvmYul.MachineState.mstore,
    EvmYul.MachineState.writeWord, EvmYul.writeBytes, FormalYul.word]
  exact readWithPadding_write_same_of_size value.toByteArray mstate.memory pos.toNat
    (by simp)

theorem evmReturn_mstore_two_words_H_return_of_size
    (mstate : EvmYul.MachineState) (pos value0 value1 : EvmYul.UInt256)
    (hmem : mstate.memory.size = pos.toNat)
    (hpos : (pos + FormalYul.word 32).toNat = pos.toNat + 32) :
    (((mstate.mstore pos value0).mstore (pos + FormalYul.word 32) value1).evmReturn
        pos (FormalYul.word 64)).H_return =
      value0.toByteArray ++ value1.toByteArray := by
  unfold EvmYul.MachineState.evmReturn EvmYul.MachineState.mstore
    EvmYul.MachineState.writeWord EvmYul.writeBytes
  simp only [FormalYul.word]
  change (value1.toByteArray.write 0 (value0.toByteArray.write 0 mstate.memory pos.toNat 32)
      (pos + EvmYul.UInt256.ofNat 32).toNat 32).readWithPadding pos.toNat 64 =
    value0.toByteArray ++ value1.toByteArray
  have hpos' : (pos + EvmYul.UInt256.ofNat 32).toNat = pos.toNat + 32 := by
    simpa [FormalYul.word] using hpos
  rw [hpos']
  exact readWithPadding_two_word_writes_of_size value0.toByteArray value1.toByteArray
    mstate.memory pos.toNat (by simp) (by simp) hmem

theorem read_two_word_write_first_data
    (a b dest : ByteArray) (ha : a.size = 32) :
    ((b.write 0 (a.write 0 dest 0 32) 32 32).readWithPadding 0 32).data.toList =
      a.data.toList := by
  simp [ByteArray.size] at ha
  simp [ByteArray.write, ByteArray.readWithPadding, ByteArray.readWithoutPadding,
    ByteArray.size, ha, ffi.ByteArray.zeroes]

theorem read_two_word_write_second_data
    (a b dest : ByteArray) (ha : a.size = 32) (hb : b.size = 32) :
    ((b.write 0 (a.write 0 dest 0 32) 32 32).readWithPadding 32 32).data.toList =
      b.data.toList := by
  simp [ByteArray.size] at ha hb
  simp [ByteArray.write, ByteArray.readWithPadding, ByteArray.readWithoutPadding,
    ByteArray.size, ha, hb, ffi.ByteArray.zeroes]

theorem write32_size_ge (source dest : ByteArray) (destAddr : Nat) :
    destAddr + 32 ≤ (source.write 0 dest destAddr 32).size := by
  simp [ByteArray.write, ByteArray.size]
  omega

theorem two_word_write_size_ge_64
    (a b dest : ByteArray) :
    64 ≤ (b.write 0 (a.write 0 dest 0 32) 32 32).size := by
  have h := write32_size_ge b (a.write 0 dest 0 32) 32
  simpa using h

theorem mload_two_word_write_first (m : EvmYul.MachineState) (xHi xLo : EvmYul.UInt256)
    (hactive : m.activeWords = word 3) :
    (((m.mstore (word 0) xHi).mstore (word 32) xLo).mload (word 0)).1 =
      xHi := by
  unfold EvmYul.MachineState.mload EvmYul.MachineState.lookupMemory
  have hsize :
      64 ≤ (xLo.toByteArray.write 0 (xHi.toByteArray.write 0 m.memory 0 32) 32 32).size :=
    two_word_write_size_ge_64 xHi.toByteArray xLo.toByteArray m.memory
  have hsize' :
      64 ≤ (xLo.toByteArray.write 0
        (xHi.toByteArray.write 0 m.memory (EvmYul.UInt256.ofNat 0).toNat 32)
        (EvmYul.UInt256.ofNat 32).toNat 32).size := by
    simpa using hsize
  have hzero : (EvmYul.UInt256.ofNat 0).toNat = 0 := rfl
  have hcond :
      ¬ ((xLo.toByteArray.write 0
                (xHi.toByteArray.write 0 m.memory (EvmYul.UInt256.ofNat 0).toNat 32)
                (EvmYul.UInt256.ofNat 32).toNat 32).size ≤
            (EvmYul.UInt256.ofNat 0).toNat ∨
          EvmYul.UInt256.ofNat
                (max
                  (EvmYul.UInt256.ofNat
                    (max (EvmYul.UInt256.ofNat 3).toNat
                      (((EvmYul.UInt256.ofNat 0).toNat + 32 + 31) / 32))).toNat
                  (((EvmYul.UInt256.ofNat 32).toNat + 32 + 31) / 32)) *
              { val := 32 } ≤
            EvmYul.UInt256.ofNat 0) := by
    intro h
    cases h with
    | inl hmem =>
        have hgt :
            (EvmYul.UInt256.ofNat 0).toNat <
              (xLo.toByteArray.write 0
                (xHi.toByteArray.write 0 m.memory (EvmYul.UInt256.ofNat 0).toNat 32)
                (EvmYul.UInt256.ofNat 32).toNat 32).size := by
          rw [hzero]
          omega
        exact (not_le_of_gt hgt) hmem
    | inr hactiveMem =>
        norm_num [EvmYul.MachineState.M, EvmYul.UInt256.ofNat, EvmYul.UInt256.mul,
          EvmYul.UInt256.toNat, EvmYul.UInt256.size] at hactiveMem
        exact
          (by decide :
            ¬ ((({ val := 3 } : EvmYul.UInt256) * ({ val := 32 } : EvmYul.UInt256)) ≤
              ({ val := (0 : Fin EvmYul.UInt256.size) } : EvmYul.UInt256))) hactiveMem
  simp [word, EvmYul.MachineState.mstore, EvmYul.MachineState.writeWord,
    hactive, EvmYul.writeBytes, EvmYul.fromByteArrayBigEndian, EvmYul.MachineState.M,
    hcond]
  apply eq_of_wordNat_eq
  simp
  have hread :
      ((xLo.toByteArray.write 0
            (xHi.toByteArray.write 0 m.memory (EvmYul.UInt256.ofNat 0).toNat 32)
            (EvmYul.UInt256.ofNat 32).toNat 32).readWithPadding
          (EvmYul.UInt256.ofNat 0).toNat 32).data.toList =
        xHi.toByteArray.data.toList := by
    simpa using
      read_two_word_write_first_data xHi.toByteArray xLo.toByteArray m.memory
        (EvmYul.UInt256.toByteArray_size xHi)
  rw [hread]
  change u256 (EvmYul.fromByteArrayBigEndian xHi.toByteArray) = wordNat xHi
  simp [u256, WORD_MOD, wordNat]
  exact xHi.val.isLt

theorem mload_two_word_write_second (m : EvmYul.MachineState) (xHi xLo : EvmYul.UInt256)
    (hactive : m.activeWords = word 3) :
    (((m.mstore (word 0) xHi).mstore (word 32) xLo).mload (word 32)).1 =
      xLo := by
  unfold EvmYul.MachineState.mload EvmYul.MachineState.lookupMemory
  have hsize :
      64 ≤ (xLo.toByteArray.write 0 (xHi.toByteArray.write 0 m.memory 0 32) 32 32).size :=
    two_word_write_size_ge_64 xHi.toByteArray xLo.toByteArray m.memory
  have hsize' :
      64 ≤ (xLo.toByteArray.write 0
        (xHi.toByteArray.write 0 m.memory (EvmYul.UInt256.ofNat 0).toNat 32)
        (EvmYul.UInt256.ofNat 32).toNat 32).size := by
    simpa using hsize
  have h32 : (EvmYul.UInt256.ofNat 32).toNat = 32 := rfl
  have hcond :
      ¬ ((xLo.toByteArray.write 0
                (xHi.toByteArray.write 0 m.memory (EvmYul.UInt256.ofNat 0).toNat 32)
                (EvmYul.UInt256.ofNat 32).toNat 32).size ≤
            (EvmYul.UInt256.ofNat 32).toNat ∨
          EvmYul.UInt256.ofNat
                (max
                  (EvmYul.UInt256.ofNat
                    (max (EvmYul.UInt256.ofNat 3).toNat
                      (((EvmYul.UInt256.ofNat 0).toNat + 32 + 31) / 32))).toNat
                  (((EvmYul.UInt256.ofNat 32).toNat + 32 + 31) / 32)) *
              { val := 32 } ≤
            EvmYul.UInt256.ofNat 32) := by
    intro h
    cases h with
    | inl hmem =>
        have hgt :
            (EvmYul.UInt256.ofNat 32).toNat <
              (xLo.toByteArray.write 0
                (xHi.toByteArray.write 0 m.memory (EvmYul.UInt256.ofNat 0).toNat 32)
                (EvmYul.UInt256.ofNat 32).toNat 32).size := by
          rw [h32]
          omega
        exact (not_le_of_gt hgt) hmem
    | inr hactiveMem =>
        norm_num [EvmYul.MachineState.M, EvmYul.UInt256.ofNat, EvmYul.UInt256.mul,
          EvmYul.UInt256.toNat, EvmYul.UInt256.size] at hactiveMem
        exact
          (by decide :
            ¬ ((({ val := 3 } : EvmYul.UInt256) * ({ val := 32 } : EvmYul.UInt256)) ≤
              ({ val := (32 : Fin EvmYul.UInt256.size) } : EvmYul.UInt256))) hactiveMem
  simp [word, EvmYul.MachineState.mstore, EvmYul.MachineState.writeWord,
    hactive, EvmYul.writeBytes, EvmYul.fromByteArrayBigEndian, EvmYul.MachineState.M,
    hcond]
  apply eq_of_wordNat_eq
  simp
  have hread :
      ((xLo.toByteArray.write 0
            (xHi.toByteArray.write 0 m.memory (EvmYul.UInt256.ofNat 0).toNat 32)
            (EvmYul.UInt256.ofNat 32).toNat 32).readWithPadding
          (EvmYul.UInt256.ofNat 32).toNat 32).data.toList =
        xLo.toByteArray.data.toList := by
    simpa using
      read_two_word_write_second_data xHi.toByteArray xLo.toByteArray m.memory
        (EvmYul.UInt256.toByteArray_size xHi) (EvmYul.UInt256.toByteArray_size xLo)
  rw [hread]
  change u256 (EvmYul.fromByteArrayBigEndian xLo.toByteArray) = wordNat xLo
  simp [u256, WORD_MOD, wordNat]
  exact xLo.val.isLt

theorem mstore_two_word_active_3 (m : EvmYul.MachineState) (xHi xLo : EvmYul.UInt256)
    (hactive : m.activeWords = word 3) :
    ((m.mstore (word 0) xHi).mstore (word 32) xLo).activeWords =
      word 3 := by
  cases m
  simp [EvmYul.MachineState.mstore, EvmYul.MachineState.writeWord, EvmYul.writeBytes,
    EvmYul.MachineState.M, word, hactive]
  decide

theorem mstore_two_word_active_6 (m : EvmYul.MachineState) (xHi xLo : EvmYul.UInt256)
    (hactive : m.activeWords = word 6) :
    ((m.mstore (word 0) xHi).mstore (word 32) xLo).activeWords =
      word 6 := by
  cases m
  simp [EvmYul.MachineState.mstore, EvmYul.MachineState.writeWord, EvmYul.writeBytes,
    EvmYul.MachineState.M, word, hactive]
  decide

theorem mload_two_word_write_first_state (m : EvmYul.MachineState)
    (xHi xLo : EvmYul.UInt256) (hactive : m.activeWords = word 3) :
    (((m.mstore (word 0) xHi).mstore (word 32) xLo).mload (word 0)).2 =
      ((m.mstore (word 0) xHi).mstore (word 32) xLo) := by
  cases m
  simp [EvmYul.MachineState.mload, EvmYul.MachineState.mstore,
    EvmYul.MachineState.writeWord, EvmYul.writeBytes, EvmYul.MachineState.M,
    word, hactive]
  decide

theorem mload_two_word_write_second_state (m : EvmYul.MachineState)
    (xHi xLo : EvmYul.UInt256) (hactive : m.activeWords = word 3) :
    (((m.mstore (word 0) xHi).mstore (word 32) xLo).mload (word 32)).2 =
      ((m.mstore (word 0) xHi).mstore (word 32) xLo) := by
  cases m
  simp [EvmYul.MachineState.mload, EvmYul.MachineState.mstore,
    EvmYul.MachineState.writeWord, EvmYul.writeBytes, EvmYul.MachineState.M,
    word, hactive]
  decide

theorem mload64_state_active_6
    (m : EvmYul.MachineState) (hactive : m.activeWords = word 6) :
    (m.mload (word 64)).2 = m := by
  cases m
  simp [EvmYul.MachineState.mload, EvmYul.MachineState.M, word] at hactive ⊢
  rw [hactive]
  decide

theorem resultWord_evmReturn_mstore_word
    (mstate : EvmYul.MachineState) (pos value : EvmYul.UInt256) :
    FormalYul.resultWord
      { returndata := ((mstate.mstore pos value).evmReturn pos (FormalYul.word 32)).H_return } =
      .ok value.toNat := by
  rw [evmReturn_mstore_word_H_return]
  simp [FormalYul.resultWord]

@[simp]
theorem sharedFor_mload_freePtr_after_mstore
    (contract : YulContract) (input : ByteArray) :
    (({ (sharedFor contract input) with
      toMachineState :=
        (sharedFor contract input).toMachineState.mstore (word 64) (word 128) }).mload
          (word 64)).1 =
      word 128 := by
  apply eq_of_wordNat_eq
  simp [sharedFor, envFor, wordNat, word,
    EvmYul.UInt256.toNat, EvmYul.UInt256.ofNat, EvmYul.UInt256.size,
    Inhabited.default, EvmYul.MachineState.mload, EvmYul.MachineState.lookupMemory,
    EvmYul.MachineState.mstore, EvmYul.MachineState.writeWord, EvmYul.writeBytes,
    ByteArray.write, ByteArray.readWithPadding, ByteArray.readWithoutPadding,
    ByteArray.size, EvmYul.MachineState.M, EvmYul.UInt256.toByteArray]
  have hle :
      ¬ (({ val := (3 : Fin EvmYul.UInt256.size) } : EvmYul.UInt256) *
          { val := (32 : Fin EvmYul.UInt256.size) } ≤
          ({ val := (64 : Fin EvmYul.UInt256.size) } : EvmYul.UInt256)) := by
    decide
  simp [hle, EvmYul.fromByteArrayBigEndian, EvmYul.fromBytesBigEndian,
    EvmYul.fromBytes', ffi.ByteArray.zeroes]
  norm_num [UInt8.size, EvmYul.UInt256.size]

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
theorem readBytes_selector_two_args_first (a b c d x y : Nat) :
    ByteArray.readBytes (bytes [a, b, c, d] ++ encodeWords [x, y]) 4 32 =
      encodeWord x := by
  apply ByteArray.ext
  rw [← Array.toList_inj]
  simp [ByteArray.readBytes, bytes, encodeWords, ByteArray.push, ByteArray.empty,
    ByteArray.emptyWithCapacity, ByteArray.size, ffi.ByteArray.zeroes,
    List.range, List.range.loop, List.range']

@[simp]
theorem readBytes_selector_two_args_second (a b c d x y : Nat) :
    ByteArray.readBytes (bytes [a, b, c, d] ++ encodeWords [x, y]) 36 32 =
      encodeWord y := by
  apply ByteArray.ext
  rw [← Array.toList_inj]
  simp [ByteArray.readBytes, bytes, encodeWords, ByteArray.push, ByteArray.empty,
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
theorem calldataload_single_arg_of_calldata
    (a b c d x : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hdata : shared.executionEnv.calldata = bytes [a, b, c, d] ++ encodeWords [x]) :
    EvmYul.State.calldataload
      (EvmYul.Yul.State.Ok shared store).toState (word 4) =
      word x := by
  simp [EvmYul.State.calldataload, EvmYul.Yul.State.toState, hdata, encodeWords]

@[simp]
theorem calldataload_two_args_first
    (contract : YulContract) (a b c d x y : Nat) :
    EvmYul.State.calldataload
      (sharedFor contract (bytes [a, b, c, d] ++ encodeWords [x, y])).toState
      (word 4) = word x := by
  simp only [EvmYul.State.calldataload, sharedFor, envFor]
  change EvmYul.uInt256OfByteArray
      (ByteArray.readBytes (bytes [a, b, c, d] ++ encodeWords [x, y]) 4 32) =
    word x
  rw [readBytes_selector_two_args_first]
  exact uInt256OfByteArray_encodeWord x

@[simp]
theorem calldataload_two_args_second
    (contract : YulContract) (a b c d x y : Nat) :
    EvmYul.State.calldataload
      (sharedFor contract (bytes [a, b, c, d] ++ encodeWords [x, y])).toState
      (word 36) = word y := by
  simp only [EvmYul.State.calldataload, sharedFor, envFor]
  change EvmYul.uInt256OfByteArray
      (ByteArray.readBytes (bytes [a, b, c, d] ++ encodeWords [x, y]) 36 32) =
    word y
  rw [readBytes_selector_two_args_second]
  exact uInt256OfByteArray_encodeWord y

@[simp]
theorem calldataload_two_args_first_state
    (contract : YulContract) (a b c d x y : Nat) (store : EvmYul.Yul.VarStore) :
    EvmYul.State.calldataload
      (EvmYul.Yul.State.Ok
        (sharedFor contract (bytes [a, b, c, d] ++ encodeWords [x, y])) store).toState
      (word 4) = word x := by
  simpa [EvmYul.Yul.State.toState] using
    calldataload_two_args_first contract a b c d x y

@[simp]
theorem calldataload_two_args_second_state
    (contract : YulContract) (a b c d x y : Nat) (store : EvmYul.Yul.VarStore) :
    EvmYul.State.calldataload
      (EvmYul.Yul.State.Ok
        (sharedFor contract (bytes [a, b, c, d] ++ encodeWords [x, y])) store).toState
      (word 36) = word y := by
  simpa [EvmYul.Yul.State.toState] using
    calldataload_two_args_second contract a b c d x y

@[simp]
theorem calldataload_two_args_first_of_calldata
    (a b c d x y : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hdata : shared.executionEnv.calldata = bytes [a, b, c, d] ++ encodeWords [x, y]) :
    EvmYul.State.calldataload
      (EvmYul.Yul.State.Ok shared store).toState (word 4) =
      word x := by
  simp only [EvmYul.State.calldataload, EvmYul.Yul.State.toState, hdata]
  change EvmYul.uInt256OfByteArray
      (ByteArray.readBytes (bytes [a, b, c, d] ++ encodeWords [x, y]) 4 32) =
    word x
  rw [readBytes_selector_two_args_first]
  exact uInt256OfByteArray_encodeWord x

@[simp]
theorem calldataload_two_args_second_of_calldata
    (a b c d x y : Nat) (shared : EvmYul.SharedState .Yul) (store : EvmYul.Yul.VarStore)
    (hdata : shared.executionEnv.calldata = bytes [a, b, c, d] ++ encodeWords [x, y]) :
    EvmYul.State.calldataload
      (EvmYul.Yul.State.Ok shared store).toState (word 36) =
      word y := by
  simp only [EvmYul.State.calldataload, EvmYul.Yul.State.toState, hdata]
  change EvmYul.uInt256OfByteArray
      (ByteArray.readBytes (bytes [a, b, c, d] ++ encodeWords [x, y]) 36 32) =
    word y
  rw [readBytes_selector_two_args_second]
  exact uInt256OfByteArray_encodeWord y

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

def DispatcherReturn
    (contract : YulContract) (input : ByteArray) (execFuel : Nat)
    (result : CallResult) : Prop :=
  ExecReturn execFuel contract.dispatcher (.some contract) (stateFor contract input) result

theorem dispatcherReturn_of_execReturn
    {contract : YulContract} {dispatcher : EvmYul.Yul.Ast.Stmt}
    {input : ByteArray} {execFuel : Nat} {result : CallResult}
    (hdispatcher : contract.dispatcher = dispatcher)
    (h : ExecReturn execFuel dispatcher (.some contract) (stateFor contract input) result) :
    DispatcherReturn contract input execFuel result := by
  unfold DispatcherReturn
  simpa [hdispatcher] using h

theorem dispatcherReturn_of_exec_halt
    {contract : YulContract} {dispatcher : EvmYul.Yul.Ast.Stmt}
    {input : ByteArray} {execFuel : Nat} {result : CallResult}
    (hdispatcher : contract.dispatcher = dispatcher)
    (h :
      ∃ state value,
        EvmYul.Yul.exec execFuel dispatcher (.some contract)
          (stateFor contract input) =
          .error (EvmYul.Yul.Exception.YulHalt state value) ∧
        returnOf state = result) :
    DispatcherReturn contract input execFuel result := by
  rcases h with ⟨state, value, hdisp, hret⟩
  exact ⟨state, value, by simpa [hdispatcher] using hdisp, hret⟩

theorem runContract_ok_of_dispatcherReturn
    {contract : YulContract} {input : ByteArray} {execFuel : Nat} {result : CallResult}
    (h : DispatcherReturn contract input execFuel result) :
    runContract contract input (Nat.succ (Nat.succ execFuel)) = .ok result := by
  unfold runContract
  rw [EvmYul.Yul.callDispatcher.eq_def]
  simp only [stateFor, EvmYul.Yul.State.initcall, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.executionEnv, sharedFor, envFor, accountMapFor, accountFor,
    EvmYul.Yul.State.multifill, EvmYul.Yul.State.setStore, List.zip_nil_left, List.foldr_nil,
    functionDefinition_params_def, functionDefinition_rets_def, functionDefinition_body_def]
  rw [EvmYul.Yul.exec.eq_def]
  simp only
  rcases h with ⟨state, value, hdisp, hret⟩
  have hdisp' :
      EvmYul.Yul.exec execFuel contract.dispatcher (.some contract)
        (EvmYul.Yul.State.Ok
          { (Inhabited.default : EvmYul.SharedState .Yul) with
            accountMap := accountMapFor contract
            executionEnv := envFor contract input
            gasAvailable := .ofNat 1000000000 }
          (Inhabited.default : EvmYul.Yul.VarStore)) =
        .error (EvmYul.Yul.Exception.YulHalt state value) := by
    simpa [stateFor, sharedFor] using hdisp
  have hdisp'' :
      EvmYul.Yul.exec execFuel contract.dispatcher (.some contract)
        (EvmYul.Yul.State.Ok
          { accountMap := accountMapFor contract,
            σ₀ := (Inhabited.default : EvmYul.SharedState .Yul).σ₀,
            totalGasUsedInBlock := (Inhabited.default : EvmYul.SharedState .Yul).totalGasUsedInBlock,
            transactionReceipts := (Inhabited.default : EvmYul.SharedState .Yul).transactionReceipts,
            substate := (Inhabited.default : EvmYul.SharedState .Yul).substate,
            executionEnv := envFor contract input,
            blocks := (Inhabited.default : EvmYul.SharedState .Yul).blocks,
            genesisBlockHeader := (Inhabited.default : EvmYul.SharedState .Yul).genesisBlockHeader,
            createdAccounts := (Inhabited.default : EvmYul.SharedState .Yul).createdAccounts,
            gasAvailable := EvmYul.UInt256.ofNat 1000000000,
            activeWords := (Inhabited.default : EvmYul.SharedState .Yul).activeWords,
            memory := (Inhabited.default : EvmYul.SharedState .Yul).memory,
            returnData := (Inhabited.default : EvmYul.SharedState .Yul).returnData,
            H_return := (Inhabited.default : EvmYul.SharedState .Yul).H_return }
          (Inhabited.default : EvmYul.Yul.VarStore)) =
        .error (EvmYul.Yul.Exception.YulHalt state value) := by
    simpa using hdisp'
  have hdisp''' :
      EvmYul.Yul.exec execFuel contract.dispatcher (.some contract)
        (EvmYul.Yul.State.Ok
          { accountMap := Batteries.RBMap.insert ∅ contractOwner
              { (Inhabited.default : EvmYul.Account .Yul) with code := contract },
            σ₀ := (Inhabited.default : EvmYul.SharedState .Yul).σ₀,
            totalGasUsedInBlock := (Inhabited.default : EvmYul.SharedState .Yul).totalGasUsedInBlock,
            transactionReceipts := (Inhabited.default : EvmYul.SharedState .Yul).transactionReceipts,
            substate := (Inhabited.default : EvmYul.SharedState .Yul).substate,
            executionEnv := { (Inhabited.default : EvmYul.ExecutionEnv .Yul) with
              calldata := input
              code := contract
              codeOwner := contractOwner
              weiValue := ⟨0⟩
              perm := true },
            blocks := (Inhabited.default : EvmYul.SharedState .Yul).blocks,
            genesisBlockHeader := (Inhabited.default : EvmYul.SharedState .Yul).genesisBlockHeader,
            createdAccounts := (Inhabited.default : EvmYul.SharedState .Yul).createdAccounts,
            gasAvailable := EvmYul.UInt256.ofNat 1000000000,
            activeWords := (Inhabited.default : EvmYul.SharedState .Yul).activeWords,
            memory := (Inhabited.default : EvmYul.SharedState .Yul).memory,
            returnData := (Inhabited.default : EvmYul.SharedState .Yul).returnData,
            H_return := (Inhabited.default : EvmYul.SharedState .Yul).H_return }
          (Inhabited.default : EvmYul.Yul.VarStore)) =
        .error (EvmYul.Yul.Exception.YulHalt state value) := by
    simpa [accountMapFor, accountFor, envFor] using hdisp''
  rw [hdisp''']
  exact congrArg Except.ok hret

theorem runContract_ok_of_dispatcherReturn_1000000
    {contract : YulContract} {input : ByteArray} {result : CallResult}
    (h : DispatcherReturn contract input 999998 result) :
    runContract contract input 1000000 = .ok result := by
  simpa using runContract_ok_of_dispatcherReturn (contract := contract)
    (input := input) (execFuel := 999998) (result := result) h

theorem callDispatcher_ok_of_dispatcherReturn
    {contract : YulContract} {input : ByteArray} {execFuel : Nat} {result : CallResult}
    (h : DispatcherReturn contract input execFuel result) :
    (match EvmYul.Yul.callDispatcher (Nat.succ (Nat.succ execFuel)) (.some contract)
        (stateFor contract input) with
      | Except.ok (state, _) => Except.ok (returnOf state)
      | Except.error (.YulHalt state _) => Except.ok (returnOf state)
      | Except.error .Revert => Except.error "revert"
      | Except.error err => Except.error (reprStr err)) =
      Except.ok result := by
  change runContract contract input (Nat.succ (Nat.succ execFuel)) = .ok result
  exact runContract_ok_of_dispatcherReturn h

theorem callDispatcher_ok_of_dispatcherReturn_1000000
    {contract : YulContract} {input : ByteArray} {result : CallResult}
    (h : DispatcherReturn contract input 999998 result) :
    (match EvmYul.Yul.callDispatcher 1000000 (.some contract)
        (stateFor contract input) with
      | Except.ok (state, _) => Except.ok (returnOf state)
      | Except.error (.YulHalt state _) => Except.ok (returnOf state)
      | Except.error .Revert => Except.error "revert"
      | Except.error err => Except.error (reprStr err)) =
      Except.ok result := by
  simpa using callDispatcher_ok_of_dispatcherReturn
    (contract := contract) (input := input) (execFuel := 999998) (result := result) h

theorem callWord_ok_of_runContract_word
    {contract : YulContract} {selector : ByteArray} {args : List Nat}
    {fuel value model : Nat}
    (hRun :
      runContract contract (calldata selector args) fuel =
        .ok (abiWordResult value))
    (hModel : u256 value = model) :
    callWord contract selector args fuel = .ok model := by
  unfold callWord call
  rw [hRun]
  change resultWord (abiWordResult value) = .ok model
  rw [resultWord_word_toByteArray]
  rw [hModel]

theorem callPair_ok_of_runContract_two_words
    {contract : YulContract} {selector : ByteArray} {args : List Nat}
    {fuel a b : Nat} {model : Nat × Nat}
    (hRun :
      runContract contract (calldata selector args) fuel =
        .ok (abiPairResult a b))
    (hModel : (u256 a, u256 b) = model) :
    callPair contract selector args fuel = .ok model := by
  unfold callPair callWords call
  rw [hRun]
  rw [bind_ok_resultWords]
  rw [resultWords_two_word_toByteArray]
  rw [bind_ok_pairFromWords]
  simp only [pairFromWords]
  rw [hModel]

theorem callTriple_ok_of_runContract_three_words
    {contract : YulContract} {selector : ByteArray} {args : List Nat}
    {fuel a b c : Nat} {model : Nat × Nat × Nat}
    (hRun :
      runContract contract (calldata selector args) fuel = .ok (abiTripleResult a b c))
    (hModel : (u256 a, u256 b, u256 c) = model) :
    callTriple contract selector args fuel = .ok model := by
  unfold callTriple callWords call
  rw [hRun]
  rw [bind_ok_resultWords]
  rw [resultWords_three_word_toByteArray]
  rw [bind_ok_tripleFromWords]
  simp only [tripleFromWords]
  rw [hModel]

theorem callWord_ok_of_dispatcherReturn_word
    {contract : YulContract} {selector : ByteArray} {args : List Nat}
    {execFuel value model : Nat}
    (hReturn :
      DispatcherReturn contract (calldata selector args) execFuel
        (abiWordResult value))
    (hModel : u256 value = model) :
    callWord contract selector args (Nat.succ (Nat.succ execFuel)) = .ok model := by
  apply callWord_ok_of_runContract_word
  · exact runContract_ok_of_dispatcherReturn hReturn
  · exact hModel

theorem callWord_ok_of_dispatcherReturn_result
    {contract : YulContract} {selector : ByteArray} {args : List Nat}
    {execFuel model : Nat} {result : CallResult}
    (hReturn :
      DispatcherReturn contract (calldata selector args) execFuel result)
    (hResult : resultWord result = .ok model) :
    callWord contract selector args (Nat.succ (Nat.succ execFuel)) = .ok model := by
  unfold callWord call
  rw [runContract_ok_of_dispatcherReturn hReturn]
  exact hResult

theorem callPair_ok_of_dispatcherReturn_two_words
    {contract : YulContract} {selector : ByteArray} {args : List Nat}
    {execFuel a b : Nat} {model : Nat × Nat}
    (hReturn :
      DispatcherReturn contract (calldata selector args) execFuel
        (abiPairResult a b))
    (hModel : (u256 a, u256 b) = model) :
    callPair contract selector args (Nat.succ (Nat.succ execFuel)) = .ok model := by
  apply callPair_ok_of_runContract_two_words
  · exact runContract_ok_of_dispatcherReturn hReturn
  · exact hModel

theorem callTriple_ok_of_dispatcherReturn_three_words
    {contract : YulContract} {selector : ByteArray} {args : List Nat}
    {execFuel a b c : Nat} {model : Nat × Nat × Nat}
    (hReturn :
      DispatcherReturn contract (calldata selector args) execFuel
        (abiTripleResult a b c))
    (hModel : (u256 a, u256 b, u256 c) = model) :
    callTriple contract selector args (Nat.succ (Nat.succ execFuel)) = .ok model := by
  apply callTriple_ok_of_runContract_three_words
  · exact runContract_ok_of_dispatcherReturn hReturn
  · exact hModel

theorem callWord_ok_of_dispatcherReturn_word_1000000
    {contract : YulContract} {selector : ByteArray} {args : List Nat}
    {value model : Nat}
    (hReturn :
      DispatcherReturn contract (calldata selector args) 999998
        (abiWordResult value))
    (hModel : u256 value = model) :
    callWord contract selector args 1000000 = .ok model := by
  simpa using callWord_ok_of_dispatcherReturn_word
    (contract := contract) (selector := selector) (args := args) (execFuel := 999998)
    (value := value) (model := model) hReturn hModel

theorem callWord_ok_of_dispatcherReturn_result_1000000
    {contract : YulContract} {selector : ByteArray} {args : List Nat}
    {model : Nat} {result : CallResult}
    (hReturn :
      DispatcherReturn contract (calldata selector args) 999998 result)
    (hResult : resultWord result = .ok model) :
    callWord contract selector args 1000000 = .ok model := by
  simpa using callWord_ok_of_dispatcherReturn_result
    (contract := contract) (selector := selector) (args := args) (execFuel := 999998)
    (model := model) hReturn hResult

theorem callPair_ok_of_dispatcherReturn_two_words_1000000
    {contract : YulContract} {selector : ByteArray} {args : List Nat}
    {a b : Nat} {model : Nat × Nat}
    (hReturn :
      DispatcherReturn contract (calldata selector args) 999998
        (abiPairResult a b))
    (hModel : (u256 a, u256 b) = model) :
    callPair contract selector args 1000000 = .ok model := by
  simpa using callPair_ok_of_dispatcherReturn_two_words
    (contract := contract) (selector := selector) (args := args) (execFuel := 999998)
    (a := a) (b := b) (model := model) hReturn hModel

theorem callTriple_ok_of_dispatcherReturn_three_words_1000000
    {contract : YulContract} {selector : ByteArray} {args : List Nat}
    {a b c : Nat} {model : Nat × Nat × Nat}
    (hReturn :
      DispatcherReturn contract (calldata selector args) 999998
        (abiTripleResult a b c))
    (hModel : (u256 a, u256 b, u256 c) = model) :
    callTriple contract selector args 1000000 = .ok model := by
  simpa using callTriple_ok_of_dispatcherReturn_three_words
    (contract := contract) (selector := selector) (args := args) (execFuel := 999998)
    (a := a) (b := b) (c := c) (model := model) hReturn hModel

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
