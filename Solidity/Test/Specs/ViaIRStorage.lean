import Solidity.Notation

/-! ViaIRStorage (`Solidity/Test/Fixtures/ViaIRStorage.sol`): the via-IR storage algorithms on
storage holding bytes no value covers.  Harness input only. -/

namespace ViaIRStorage.SoliditySpec

open _root_.Solidity _root_.Solidity.Notation

def viaIRStorage : SourceUnit := sol% contract ViaIRStorage {
  struct S { uint8 a; uint128 b; uint256 c; int16 d; }
  S s;
  uint8[5] p;
  uint8[] dp;
  bytes b;

  function deleteS() external { delete s; }
  function setS(uint8 a, uint128 b_, uint256 c, int16 d) external { s = S(a, b_, c, d); }
  function setP(uint8[5] calldata x) external { p = x; }
  function deleteP() external { delete p; }
  function setDp(uint8[] calldata x) external { dp = x; }
  function deleteDp() external { delete dp; }
  function pushDp() external { dp.push(); }
  function popDp() external { dp.pop(); }
  function pushB() external { b.push(); }
  function pushBv(bytes1 v) external { b.push(v); }
  function popB() external { b.pop(); }
  function getB() external view returns (bytes memory) { return b; }
  function getDp() external view returns (uint8[] memory) { return dp; }
}

def program : Program := [viaIRStorage]

end ViaIRStorage.SoliditySpec
