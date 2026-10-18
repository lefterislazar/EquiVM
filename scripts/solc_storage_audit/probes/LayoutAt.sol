// SPDX-License-Identifier: UNLICENSED
// @min 0.8.29
pragma solidity >=0.8.29;

contract LayoutAt layout at 0x1234 {
  uint8 a; uint16 b; bytes c; uint256[] d; mapping(uint256 => uint256) m; uint256[3] f;

  function w_a(uint8 x) external { a = x; }
  function w_b(uint16 x) external { b = x; }
  function w_c(bytes calldata x) external { c = x; }
  function pushv_d(uint256 x) external { d.push(x); }
  function w_m(uint256 k, uint256 v) external { m[k] = v; }
  function d_f() external { delete f; }
}
