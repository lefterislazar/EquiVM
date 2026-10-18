// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.8.0;

contract Structs {
  struct S { uint8 a; uint128 b; uint256 c; int16 d; }
  struct N { S s; uint8 x; bytes y; uint16[] z; }
  struct M { uint8 a; mapping(uint256 => uint256) m; uint8 b; }
  S s; S s2; N n; N n2; M m;

  // Setters for the sources of storage-to-storage copies (not analyzed).
  function set_s2(S memory x) external { s2 = x; }
  function set_n2(N memory x) external { n2 = x; }

  function w_S_mem(uint8 a, uint128 b, uint256 c, int16 d) external { s = S(a, b, c, d); }
  function w_S_cd(S calldata x) external { s = x; }
  function w_S_sto() external { s = s2; }
  function r_S() external view returns (S memory) { return s; }
  function d_S() external { delete s; }
  function wf_S(uint128 b) external { s.b = b; }
  function rf_S() external view returns (int16) { return s.d; }
  function w_N_mem(N memory x) external { n = x; }
  function w_N_cd(N calldata x) external { n = x; }
  function w_N_sto() external { n = n2; }
  function r_N() external view returns (N memory) { return n; }
  function d_N() external { delete n; }
  function wf_N(S memory x) external { n.s = x; }
  function d_M() external { delete m; }
  function wf_M(uint256 k, uint256 v) external { m.m[k] = v; m.a = 1; }
}
