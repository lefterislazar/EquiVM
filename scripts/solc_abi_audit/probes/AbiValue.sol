// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.8.13;

// Value-type parameters and return values: validation of the calldata word, cleanup on encoding.
contract AbiValue {
  enum E { A, B, C }

  function u8(uint8 x) external pure returns (uint8) { return x; }
  function i8(int8 x) external pure returns (int8) { return x; }
  function i40(int40 x) external pure returns (int40) { return x; }
  function u256(uint256 x) external pure returns (uint256) { return x; }
  function bo(bool x) external pure returns (bool) { return x; }
  function ad(address x) external pure returns (address) { return x; }
  function b3(bytes3 x) external pure returns (bytes3) { return x; }
  function b32(bytes32 x) external pure returns (bytes32) { return x; }
  function en(E x) external pure returns (E) { return x; }
  function fx(function() external x) external pure returns (function() external) { return x; }
  function two(uint8 x, bool y) external pure returns (uint8, bool) { return (x, y); }
  function unused(uint8 x, bool y) external pure returns (uint256) { return 7; }
  function dirtyU8(uint256 w) external pure returns (uint8 x) { assembly { x := w } }
  function dirtyBo(uint256 w) external pure returns (bool x) { assembly { x := w } }
  function dirtyI8(uint256 w) external pure returns (int8 x) { assembly { x := w } }
  function dirtyAd(uint256 w) external pure returns (address x) { assembly { x := w } }
}
