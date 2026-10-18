// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.8.13;

// Calldata parameters: only the head is checked on entry; the content is validated when it is
// accessed, copied to memory or re-encoded.
contract AbiCd {
  struct S { uint8 a; bytes b; uint16[] c; }
  struct T { uint256 x; uint8[2] y; }

  function au8(uint8[] calldata x) external pure returns (uint8[] memory) { return x; }
  function au8len(uint8[] calldata x) external pure returns (uint256) { return x.length; }
  function au8at(uint8[] calldata x, uint256 i) external pure returns (uint8) { return x[i]; }
  function au8slice(uint8[] calldata x, uint256 a, uint256 b) external pure returns (uint8[] memory) { return x[a:b]; }
  function fu8(uint8[3] calldata x) external pure returns (uint8[3] memory) { return x; }
  function fu8at(uint8[3] calldata x, uint256 i) external pure returns (uint8) { return x[i]; }
  function bys(bytes calldata x) external pure returns (bytes memory) { return x; }
  function bylen(bytes calldata x) external pure returns (uint256) { return x.length; }
  function byslice(bytes calldata x, uint256 a, uint256 b) external pure returns (bytes memory) { return x[a:b]; }
  function st(string calldata x) external pure returns (string memory) { return x; }
  function nn(uint8[][] calldata x) external pure returns (uint8[][] memory) { return x; }
  function nnat(uint8[][] calldata x, uint256 i, uint256 j) external pure returns (uint8) { return x[i][j]; }
  function nnlen(uint8[][] calldata x, uint256 i) external pure returns (uint256) { return x[i].length; }
  function nncopy(uint8[][] calldata x) external pure returns (uint256) { uint8[][] memory m = x; return m.length; }
  function nnenc(uint8[][] calldata x) external pure returns (bytes memory) { return abi.encode(x); }
  function fn(uint256[2][] calldata x) external pure returns (uint256[2][] memory) { return x; }
  function nf(uint8[][2] calldata x) external pure returns (uint8[][2] memory) { return x; }
  function bb(bytes[] calldata x) external pure returns (bytes[] memory) { return x; }
  function bbat(bytes[] calldata x, uint256 i) external pure returns (bytes memory) { return x[i]; }
  function s(S calldata x) external pure returns (S memory) { return x; }
  function sa(S calldata x) external pure returns (uint8) { return x.a; }
  function sb(S calldata x) external pure returns (bytes memory) { return x.b; }
  function sar(S[] calldata x) external pure returns (S[] memory) { return x; }
  function t(T calldata x) external pure returns (T memory) { return x; }
  function tar(T[] calldata x) external pure returns (T[] memory) { return x; }
  function tail(bytes calldata d, uint256[2] calldata s2) external pure returns (bytes memory) { return abi.encode(d, s2); }
  function mix(uint8 a, bytes calldata b, bool d) external pure returns (uint8, bytes memory, bool) { return (a, b, d); }
}
