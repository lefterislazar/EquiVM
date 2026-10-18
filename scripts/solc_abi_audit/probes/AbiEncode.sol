// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.8.13;

// The `abi.encode*` family and custom errors.
contract AbiEncode {
  struct S { uint8 a; bytes b; uint16[] c; }
  error Err(uint8 a, bytes b);

  function target(uint8 a, bytes memory b) external pure returns (uint8) { return a + uint8(b.length); }

  function eE(uint8 a, bytes memory b, uint16[] memory c) external pure returns (bytes memory) { return abi.encode(a, b, c); }
  function eP(uint8 a, bytes memory b, uint16[] memory c) external pure returns (bytes memory) { return abi.encodePacked(a, b, c); }
  function ePbool(bool a, int8 b, bytes3 c, address d) external pure returns (bytes memory) { return abi.encodePacked(a, b, c, d); }
  function ePstr(string memory a, bytes32 b) external pure returns (bytes memory) { return abi.encodePacked(a, b); }
  function eSel(uint8 a, bytes memory b) external pure returns (bytes memory) { return abi.encodeWithSelector(0x12345678, a, b); }
  function eSig(uint8 a, bytes memory b) external pure returns (bytes memory) { return abi.encodeWithSignature("target(uint8,bytes)", a, b); }
  function eCall(uint8 a, bytes memory b) external view returns (bytes memory) { return abi.encodeCall(this.target, (a, b)); }
  function eS(S memory s) external pure returns (bytes memory) { return abi.encode(s); }
  function eNested(uint8[][] memory x, bytes[] memory y) external pure returns (bytes memory) { return abi.encode(x, y); }
  function eDirty(uint256 w) external pure returns (bytes memory) { uint8 x; assembly { x := w } return abi.encode(x); }
  function ePDirty(uint256 w) external pure returns (bytes memory) { int8 x; assembly { x := w } return abi.encodePacked(x); }
  function rErr(uint8 a, bytes memory b) external pure { revert Err(a, b); }
  function rStr(string memory m) external pure { revert(m); }
  function rReq(bool c, string memory m) external pure { require(c, m); }
  function rAssert(bool c) external pure { assert(c); }
}
