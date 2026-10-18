// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.8.0;

contract DynArrays {
  struct S { uint8 a; uint128 b; uint256 c; }
  uint8[] p; uint8[] p2;
  uint256[] f; uint256[] f2;
  S[] ms; S[] ms2;
  uint16[][] nn; uint16[][] nn2;
  bytes[] bb; bytes[] bb2;
  uint8[3][] fa; uint8[3][] fa2;

  // Setters for the sources of storage-to-storage copies (not analyzed).
  function set_p2(uint8[] memory x) external { p2 = x; }
  function set_f2(uint256[] memory x) external { f2 = x; }
  function set_ms2(S[] memory x) external { ms2 = x; }
  function set_nn2(uint16[][] memory x) external { nn2 = x; }
  function set_bb2(bytes[] memory x) external { bb2 = x; }
  function set_fa2(uint8[3][] memory x) external { fa2 = x; }

  function w_p_mem(uint8[] memory x) external { p = x; }
  function w_p_cd(uint8[] calldata x) external { p = x; }
  function w_p_sto() external { p = p2; }
  function r_p() external view returns (uint8[] memory) { return p; }
  function d_p() external { delete p; }
  function len_p() external view returns (uint256) { return p.length; }
  function push0_p() external { p.push(); }
  function pushv_p(uint8 v) external { p.push(v); }
  function pop_p() external { p.pop(); }
  function wi_p(uint256 i, uint8 v) external { p[i] = v; }
  function ri_p(uint256 i) external view returns (uint8) { return p[i]; }
  function di_p(uint256 i) external { delete p[i]; }
  function w_f_mem(uint256[] memory x) external { f = x; }
  function w_f_cd(uint256[] calldata x) external { f = x; }
  function w_f_sto() external { f = f2; }
  function r_f() external view returns (uint256[] memory) { return f; }
  function d_f() external { delete f; }
  function push0_f() external { f.push(); }
  function pushv_f(uint256 v) external { f.push(v); }
  function pop_f() external { f.pop(); }
  function wi_f(uint256 i, uint256 v) external { f[i] = v; }
  function ri_f(uint256 i) external view returns (uint256) { return f[i]; }
  function w_ms_mem(S[] memory x) external { ms = x; }
  function w_ms_cd(S[] calldata x) external { ms = x; }
  function w_ms_sto() external { ms = ms2; }
  function r_ms() external view returns (S[] memory) { return ms; }
  function d_ms() external { delete ms; }
  function push0_ms() external { ms.push(); }
  function pushv_ms(uint8 a, uint128 b, uint256 c) external { ms.push(S(a, b, c)); }
  function pop_ms() external { ms.pop(); }
  function wi_ms(uint256 i, S memory v) external { ms[i] = v; }
  function w_nn_mem(uint16[][] memory x) external { nn = x; }
  function w_nn_cd(uint16[][] calldata x) external { nn = x; }
  function w_nn_sto() external { nn = nn2; }
  function r_nn() external view returns (uint16[][] memory) { return nn; }
  function d_nn() external { delete nn; }
  function push0_nn() external { nn.push(); }
  function pushv_nn(uint16[] memory v) external { nn.push(v); }
  function pop_nn() external { nn.pop(); }
  function wi_nn(uint256 i, uint256 j, uint16 v) external { nn[i][j] = v; }
  function w_bb_mem(bytes[] memory x) external { bb = x; }
  function w_bb_cd(bytes[] calldata x) external { bb = x; }
  function w_bb_sto() external { bb = bb2; }
  function r_bb() external view returns (bytes[] memory) { return bb; }
  function d_bb() external { delete bb; }
  function pushv_bb(bytes memory v) external { bb.push(v); }
  function pop_bb() external { bb.pop(); }
  function w_fa_mem(uint8[3][] memory x) external { fa = x; }
  function w_fa_cd(uint8[3][] calldata x) external { fa = x; }
  function w_fa_sto() external { fa = fa2; }
  function d_fa() external { delete fa; }
  function pushv_fa(uint8[3] memory v) external { fa.push(v); }
  function pop_fa() external { fa.pop(); }
}
