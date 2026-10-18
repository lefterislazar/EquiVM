// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.8.13;

// Memory parameters: the whole argument is decoded and validated on entry.
contract AbiMem {
  struct S { uint8 a; bytes b; uint16[] c; }
  struct T { uint256 x; uint8[2] y; }

  function au8(uint8[] memory x) external pure returns (uint8[] memory) { return x; }
  function au8len(uint8[] memory x) external pure returns (uint256) { return x.length; }
  function au8at(uint8[] memory x, uint256 i) external pure returns (uint8) { return x[i]; }
  function fu8(uint8[3] memory x) external pure returns (uint8[3] memory) { return x; }
  function bys(bytes memory x) external pure returns (bytes memory) { return x; }
  function st(string memory x) external pure returns (string memory) { return x; }
  function nn(uint8[][] memory x) external pure returns (uint8[][] memory) { return x; }
  function nnat(uint8[][] memory x, uint256 i, uint256 j) external pure returns (uint8) { return x[i][j]; }
  function fn(uint256[2][] memory x) external pure returns (uint256[2][] memory) { return x; }
  function nf(uint8[][2] memory x) external pure returns (uint8[][2] memory) { return x; }
  function bb(bytes[] memory x) external pure returns (bytes[] memory) { return x; }
  function s(S memory x) external pure returns (S memory) { return x; }
  function sa(S memory x) external pure returns (uint8) { return x.a; }
  function sar(S[] memory x) external pure returns (S[] memory) { return x; }
  function t(T memory x) external pure returns (T memory) { return x; }
  function tar(T[] memory x) external pure returns (T[] memory) { return x; }
  function mix(uint8 a, bytes memory b, bool d) external pure returns (uint8, bytes memory, bool) { return (a, b, d); }
}
