import Solm.Semantics
import Solm.Notation

/-! The abstract event operation only enforces static permissions. -/

namespace Solm.Tests.Event

-- Every writable execution preserves the entire frame and EVM state.
example (cfg : Config) (frame : Frame) (evm : EVM.State) (result : ExecResult)
    (hp : evm.executionEnv.perm = true) :
    ExecStmt cfg frame evm .event result ↔ result = .ok frame evm := by
  constructor
  · intro h
    cases h <;> simp_all
  · rintro rfl
    exact .event hp

-- Every static execution reverts, including when nested inside another call.
example (cfg : Config) (frame : Frame) (evm : EVM.State) (result : ExecResult)
    (hp : evm.executionEnv.perm = false) :
    ExecStmt cfg frame evm .event result ↔ result = .reverted := by
  constructor
  · intro h
    cases h <;> simp_all
  · rintro rfl
    exact .eventRevert hp

-- A prohibited event stops the block before any following statement.
example (cfg : Config) (frame : Frame) (evm : EVM.State) (rest : List Stmt)
    (hp : evm.executionEnv.perm = false) :
    ExecBlock cfg frame evm (.event :: rest) .reverted :=
  .consRevert (.eventRevert hp)

-- A permitted event allows the rest of the block to execute from the same state.
example (cfg : Config) (frame : Frame) (evm : EVM.State) (rest : List Stmt)
    (result : ExecResult) (hp : evm.executionEnv.perm = true)
    (hr : ExecBlock cfg frame evm rest result) :
    ExecBlock cfg frame evm (.event :: rest) result :=
  .consNormal (.event hp) hr

private def eventContract : ContractDecl := solidity% contract EventExample {
  function emitLog() external payable {
    event();
  }
}

example : (eventContract.transitions[0]!).body = [.event] := rfl

/-- error: solm: event expects no arguments -/
#guard_msgs in
private def invalidEvent : ContractDecl := solidity% contract EventExample {
  function emitLog() external payable {
    event(1);
  }
}

end Solm.Tests.Event
