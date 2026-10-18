// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.8.0;

contract FixedArrays {
  struct S { uint8 a; uint128 b; uint256 c; }
  uint8[5] p; uint8[5] p2;
  uint256[3] f; uint256[3] f2;
  S[2] ms; S[2] ms2;
  uint8[3][2] nn; uint8[3][2] nn2;
  bytes[2] bb; bytes[2] bb2;

  // Setters for the sources of storage-to-storage copies (not analyzed).
  function set_p2(uint8[5] memory x) external { p2 = x; }
  function set_f2(uint256[3] memory x) external { f2 = x; }
  function set_ms2(S[2] memory x) external { ms2 = x; }
  function set_nn2(uint8[3][2] memory x) external { nn2 = x; }
  function set_bb2(bytes[2] memory x) external { bb2 = x; }

  function w_p_mem(uint8[5] memory x) external { p = x; }
  function w_p_cd(uint8[5] calldata x) external { p = x; }
  function w_p_sto() external { p = p2; }
  function r_p() external view returns (uint8[5] memory) { return p; }
  function d_p() external { delete p; }
  function wi_p(uint256 i, uint8 v) external { p[i] = v; }
  function ri_p(uint256 i) external view returns (uint8) { return p[i]; }
  function di_p(uint256 i) external { delete p[i]; }
  function w_f_mem(uint256[3] memory x) external { f = x; }
  function w_f_cd(uint256[3] calldata x) external { f = x; }
  function w_f_sto() external { f = f2; }
  function r_f() external view returns (uint256[3] memory) { return f; }
  function d_f() external { delete f; }
  function wi_f(uint256 i, uint256 v) external { f[i] = v; }
  function ri_f(uint256 i) external view returns (uint256) { return f[i]; }
  function w_ms_mem(S[2] memory x) external { ms = x; }
  function w_ms_cd(S[2] calldata x) external { ms = x; }
  function w_ms_sto() external { ms = ms2; }
  function r_ms() external view returns (S[2] memory) { return ms; }
  function d_ms() external { delete ms; }
  function wi_ms(uint256 i, S memory v) external { ms[i] = v; }
  function w_nn_mem(uint8[3][2] memory x) external { nn = x; }
  function w_nn_cd(uint8[3][2] calldata x) external { nn = x; }
  function w_nn_sto() external { nn = nn2; }
  function r_nn() external view returns (uint8[3][2] memory) { return nn; }
  function d_nn() external { delete nn; }
  function wi_nn(uint256 i, uint256 j, uint8 v) external { nn[i][j] = v; }
  function w_bb_mem(bytes[2] memory x) external { bb = x; }
  function w_bb_cd(bytes[2] calldata x) external { bb = x; }
  function w_bb_sto() external { bb = bb2; }
  function r_bb() external view returns (bytes[2] memory) { return bb; }
  function d_bb() external { delete bb; }
}
